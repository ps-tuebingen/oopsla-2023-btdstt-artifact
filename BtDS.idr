module BtDS

import Data.DPair

-- Contexts and environments

{-
    We use De Bruijn indices and elements of typing contexts are represented as
    positions in a list.
-}
data Name : List k -> k -> Type where
  Z : Name (x :: xs) x
  S : Name xs x -> Name (y :: xs) x

{-
    Runtime Environments are represented as lists over contexts.
-}
data Env : (k -> Type) -> List k -> Type where
  Nil : Env f []
  (::) : {0 x : k} -> {0 xs : List k} -> {0 f : k -> Type} -> f x -> Env f xs -> Env f (x :: xs)


-- Structural rules for contexts

data Sub : List k -> List k -> Type where
  Keep : Sub xs xs
  Weak : Sub xs (y :: xs)
  Lift : Sub xs ys -> Sub (x :: xs) (x :: ys)
  Comp : Sub xs ys -> Sub ys zs -> Sub xs zs
  Swap : Sub (x :: y :: zs) (y :: x :: zs)
  Copy : Sub (x :: x :: xs) (x :: xs)

rename : Sub xs ys -> Name xs x -> Name ys x
rename Keep x = x
rename Weak x = S x
rename (Lift a) Z = Z
rename (Lift a) (S x) = S (rename a x)
rename (Comp a b) x = rename b (rename a x)
rename Swap Z = S Z
rename Swap (S Z) = Z
rename Swap (S (S x)) = S (S x)
rename Copy Z = Z
rename Copy (S y) = y

lookup : Env f xs -> Name xs x -> f x
lookup [] Z impossible
lookup [] (S x) impossible
lookup (v :: _) Z = v
lookup (_ :: vs) (S x) = lookup vs x

mapEnv : ({0 x : k} -> f x -> g x) -> Env f xs -> Env g xs
mapEnv f [] = []
mapEnv f (v :: vs) = f v :: mapEnv f vs

swapMany : {zs : List k} -> Sub (zs ++ (x :: xs)) (x :: (zs ++ xs))
swapMany {zs = []} = Keep
swapMany {zs = _ :: _} = Comp (Lift swapMany) Swap

weakMany : {zs : List k} -> Sub xs (zs ++ xs)
weakMany {zs = []} = Keep
weakMany {zs = _ :: _} = Comp weakMany Weak

liftMany : {zs : List k} -> Sub xs ys -> Sub (zs ++ xs) (zs ++ ys)
liftMany {zs = []} h = h
liftMany {zs = _ :: _} h = Lift (liftMany h)

copyName : Name xs x -> Sub (x :: xs) xs
copyName Z = Copy
copyName (S x) = Comp Swap (Lift (copyName x))


-- Insertion of position into list

data Ins : k -> List k -> List k -> Type where
  Here : Ins x xs (x :: xs)
  Next : Ins x xs ys -> Ins x (y :: xs) (y :: ys)

insEq : Ins x xs zs -> Ins y ys zs -> Maybe (x = y, xs = ys)
insEq Here Here = Just (Refl, Refl)
insEq Here (Next y) = Nothing
insEq (Next x) Here = Nothing
insEq (Next x) (Next y) = case insEq x y of
  Nothing => Nothing
  Just (eq, eqs) => rewrite eq in rewrite eqs in Just (Refl, Refl)

nameToIns : Name xs x -> Exists (\ys => Ins x ys xs)
nameToIns {xs = _ :: ys} Z = Evidence ys Here
nameToIns {xs = y :: _} (S x) = case nameToIns x of
  Evidence ys i => Evidence (y :: ys) (Next i)

insToName : Ins x ys xs -> Name xs x
insToName Here = Z
insToName (Next x) = S (insToName x)

insToWeak : Ins x xs ys -> Sub xs ys
insToWeak Here = Weak
insToWeak (Next x) = Lift (insToWeak x)

insToSwap : Ins x xs ys -> Sub ys (x :: xs)
insToSwap Here = Keep
insToSwap (Next x) = Comp (Lift (insToSwap x)) Swap

insToSwapRev : Ins x xs ys -> Sub (x :: xs) ys
insToSwapRev Here = Keep
insToSwapRev (Next x) = Comp Swap (Lift (insToSwapRev x))

strengthenEnv : Ins x xs ys -> Env k ys -> Env k xs
strengthenEnv Here (h :: t) = t
strengthenEnv (Next x) (h :: t) = h :: (strengthenEnv x t)

{-
    Here we remove a position `x` from list `ys` for position `a` unless `x`
    happens to be `a`.
-}
maybeStrengthenName : Ins x xs ys -> Name ys a -> Maybe (Name xs a)
maybeStrengthenName Here Z = Nothing
maybeStrengthenName Here (S x) = Just x
maybeStrengthenName (Next k) Z = Just Z
maybeStrengthenName (Next k) (S x) = case maybeStrengthenName k x of
  Nothing => Nothing
  Just y => Just (S y)


-- Types

data Tpe : Type where
  Itg : Tpe
  Fun : Tpe -> Tpe -> Tpe
  Cont : Tpe -> Tpe

eqCont : (Cont a = Cont b) -> a = b
eqCont Refl = Refl

-- `Cont r` cannot be `Itg`, so we can always remove that position
strengthenNameContItg : Ins (Cont r) xs ys -> Name ys Itg -> Name xs Itg
strengthenNameContItg Here Z impossible
strengthenNameContItg Here (S x) = x
strengthenNameContItg (Next k) Z = Z
strengthenNameContItg (Next k) (S x) = S (strengthenNameContItg k x)

-- `Cont r` cannot be `r`, so we can always remove that position
strengthenNameCont : Ins (Cont r) xs ys -> Name ys r -> Name xs r
strengthenNameCont Here Z impossible
strengthenNameCont Here (S x) = x
strengthenNameCont (Next k) Z = Z
strengthenNameCont (Next k) (S x) = S (strengthenNameCont k x)

-- Expressions

{-
    Expressions are common to both the DS language and the CPS language.

    We use intrinsic typing, so language constructs are represented by their
    typing derivations. Thus, in `Exp xs s` the list `xs` is the typing context
    and `a` is the type of the expression.
-}
data Exp : List Tpe -> Tpe -> Type where
  Var : Name xs a -> Exp xs a
  Num : Int -> Exp xs Itg

renameExp : Sub xs ys -> Exp xs r -> Exp ys r
renameExp sub (Var x) = Var (rename sub x)
renameExp sub (Num n) = Num n

-- again `Cont r` cannot be `Itg`
strengthenExpItg : Ins (Cont r) xs ys -> Exp ys Itg -> Exp xs Itg
strengthenExpItg k e = case e of
  Num n => Num n
  Var x => let y = strengthenNameContItg k x in Var y


-- DS language

namespace Direct
  -- Syntax

  public export
  {-
      Statements in DS may be returning or non-returning. Thus, in `Stmt xs t`
      the type `t` may be `Nothing` representing a non-returning statement. The
      list `xs` is again the typing context.
  -}
  data Stmt : List Tpe -> Maybe Tpe -> Type where
    Ret : Exp xs a -> Stmt xs (Just a)
    Seq : Stmt xs (Just a) -> Stmt (a :: xs) (Just b) -> Stmt xs (Just b)
    Call : Name xs (Fun a b) -> Exp xs a -> Stmt xs (Just b)
    Def : Stmt (a :: xs) (Just b) -> Stmt (Fun a b :: xs) t -> Stmt xs t
    Proc : Stmt (r :: xs) Nothing -> Stmt (Cont r :: xs) t -> Stmt xs t
    If0 : Exp xs Itg -> Stmt xs t -> Stmt xs t -> Stmt xs t
    Susp : Stmt (Cont r :: xs) Nothing -> Stmt xs (Just r)
    Run : Exp xs (Cont r) -> Stmt xs (Just r) -> Stmt xs Nothing
    Exit : Exp xs a -> Stmt xs Nothing

  public export
  renameStmt : Sub xs ys -> Stmt xs r -> Stmt ys r
  renameStmt sub (Ret e) = Ret (renameExp sub e)
  renameStmt sub (Seq s b) = Seq (renameStmt sub s) (renameStmt (Lift sub) b)
  renameStmt sub (Call f e) = Call (rename sub f) (renameExp sub e)
  renameStmt sub (Def b s) = Def (renameStmt (Lift sub) b) (renameStmt (Lift sub) s)
  renameStmt sub (Proc b s) = Proc (renameStmt (Lift sub) b) (renameStmt (Lift sub) s)
  renameStmt sub (If0 e s1 s2) = If0 (renameExp sub e) (renameStmt sub s1) (renameStmt sub s2)
  renameStmt sub (Susp s) = Susp (renameStmt (Lift sub) s)
  renameStmt sub (Run e s) = Run (renameExp sub e) (renameStmt sub s)
  renameStmt sub (Exit e) = Exit (renameExp sub e)

  public export
  {-
      We strengthen in the context if the corresponding variable is not used in
      the statement.
  -}
  maybeStrengthenStmt : Ins x xs ys -> Stmt ys t -> Maybe (Stmt xs t)
  maybeStrengthenStmt p (Ret (Var x)) = case maybeStrengthenName p x of
    Nothing => Nothing
    Just y => Just (Ret (Var y))
  maybeStrengthenStmt p (Ret (Num n)) = Just (Ret (Num n))
  maybeStrengthenStmt p (Seq s b) = case maybeStrengthenStmt p s of
    Nothing => Nothing
    Just s0 => case maybeStrengthenStmt (Next p) b of
                 Nothing => Nothing
                 Just b0 => Just (Seq s0 b0)
  maybeStrengthenStmt p (Call f (Var x)) = case maybeStrengthenName p f of
    Nothing => Nothing
    Just g => case maybeStrengthenName p x of
                Nothing => Nothing
                Just y => Just (Call g (Var y))
  maybeStrengthenStmt p (Call f (Num n)) = case maybeStrengthenName p f of
    Nothing => Nothing
    Just g => Just (Call g (Num n))
  maybeStrengthenStmt p (Def b s) = case maybeStrengthenStmt (Next p) b of
    Nothing => Nothing
    Just b0 => case maybeStrengthenStmt (Next p) s of
                 Nothing => Nothing
                 Just s0 => Just (Def b0 s0)
  maybeStrengthenStmt p (Proc b s) = case maybeStrengthenStmt (Next p) b of
    Nothing => Nothing
    Just b0 => case maybeStrengthenStmt (Next p) s of
                 Nothing => Nothing
                 Just s0 => Just (Proc b0 s0)
  maybeStrengthenStmt p (If0 (Var x) s1 s2) = case maybeStrengthenName p x of
    Nothing => Nothing
    Just y => case maybeStrengthenStmt p s1 of
                Nothing => Nothing
                Just s10 => case maybeStrengthenStmt p s2 of
                              Nothing => Nothing
                              Just s20 => Just (If0 (Var y) s10 s20)
  maybeStrengthenStmt p (If0 (Num n) s1 s2) = case maybeStrengthenStmt p s1 of
    Nothing => Nothing
    Just s10 => case maybeStrengthenStmt p s2 of
                  Nothing => Nothing
                  Just s20 => Just (If0 (Num n) s10 s20)
  maybeStrengthenStmt p (Susp s) = case maybeStrengthenStmt (Next p) s of
    Nothing => Nothing
    Just s0 => Just (Susp s0)
  maybeStrengthenStmt p (Run (Var k) s) = case maybeStrengthenName p k of
    Nothing => Nothing
    Just k0 => case maybeStrengthenStmt p s of
                 Nothing => Nothing
                 Just s0 => Just (Run (Var k0) s0)
  maybeStrengthenStmt p (Run (Num n) s) impossible
  maybeStrengthenStmt p (Exit (Var x)) = case maybeStrengthenName p x of
    Nothing => Nothing
    Just y => Just (Exit (Var y))
  maybeStrengthenStmt p (Exit (Num n)) = Just (Exit (Num n))

  -- Semantics

  mutual
    public export
    data Value : Tpe -> Type where
      Literal : Int -> Value Itg
      Closure : Env Value xs -> Stmt (a :: xs) (Just b) -> Value (Fun a b)
      Captured : Stack a -> Value (Cont a)

    public export
    data Stack : Tpe -> Type where
      Underflow : Env Value xs -> Stmt (a :: xs) Nothing -> Stack a
      Frame : Env Value xs -> Stmt (a :: xs) (Just b) -> Stack b -> Stack a

  public export
  data Machine : Type where
    ExeD : Env Value xs -> Stmt xs Nothing -> Machine
    ExeU : Env Value xs -> Stmt xs (Just a) -> Stack a -> Machine

  step : Machine -> Machine
  step (ExeU vs (Ret (Var x)) (Underflow ws s)) =
    ExeD (lookup vs x :: ws) s
  step (ExeU vs (Ret (Var x)) (Frame ws s k)) =
    ExeU (lookup vs x :: ws) s k
  step (ExeU vs (Ret (Num n)) (Underflow ws s)) =
    ExeD ((Literal n) :: ws) s
  step (ExeU vs (Ret (Num n)) (Frame ws s k)) =
    ExeU ((Literal n) :: ws) s k
  step (ExeU vs (Seq s b) k) =
    ExeU vs s (Frame vs b k)
  step (ExeU vs (Call f (Var x)) k) = case lookup vs f of
    Closure ws s => ExeU (lookup vs x :: ws) s k
  step (ExeU vs (Call f (Num n)) k) = case lookup vs f of
    Closure ws s => ExeU (Literal n :: ws) s k
  step (ExeU vs (Def b s) k) =
    ExeU (Closure vs b :: vs) s k
  step (ExeU vs (Proc b s) k) =
    ExeU (Captured (Underflow vs b) :: vs) s k
  step (ExeU vs (If0 (Var x) s1 s2) k) = case lookup vs x of
    Literal n => if n == 0
                then ExeU vs s1 k
                else ExeU vs s2 k
  step (ExeU vs (If0 (Num n) s1 s2) k) =
    if n == 0
       then ExeU vs s1 k
       else ExeU vs s2 k
  step (ExeU vs (Susp s) k) =
    ExeD (Captured k :: vs) s
  step (ExeD vs (Def b s)) =
    ExeD (Closure vs b :: vs) s
  step (ExeD vs (Proc b s)) =
    ExeD (Captured (Underflow vs b) :: vs) s
  step (ExeD vs (If0 (Var x) s1 s2)) = case lookup vs x of
    Literal n => if n == 0
                then ExeD vs s1
                else ExeD vs s2
  step (ExeD vs (If0 (Num n) s1 s2)) =
    if n == 0
       then ExeD vs s1
       else ExeD vs s2
  step (ExeD vs (Run (Var k) s)) = case lookup vs k of
    Captured c => ExeU vs s c
  step (ExeD vs (Run (Num n) s)) impossible
  -- here we loop to indicate that we are done
  step (ExeD vs (Exit e)) =
    ExeD vs (Exit e)


-- CPS language

namespace Lambda
  -- Syntax

  public export
  {-
      Terms in CPS never return. Thus, there is no type in `Trs xs` but only the
      list `xs` for the typing context.
  -}
  data Term : List Tpe -> Type where
    Let : Term (Cont b :: a :: xs) -> Term (Fun a b :: xs) -> Term xs
    Apply : Name xs (Fun a b) -> Exp xs a -> Exp xs (Cont b) -> Term xs
    Cnt : Term (a :: xs) -> Term (Cont a :: xs) -> Term xs
    Jump : Name xs (Cont a) -> Exp xs a -> Term xs
    If0 : Exp xs Itg -> Term xs -> Term xs -> Term xs
    Exit : Exp xs a -> Term xs

  public export
  renameTerm : Sub xs ys -> Term xs -> Term ys
  renameTerm sub (Let b t) = Let (renameTerm (Lift (Lift sub)) b) (renameTerm (Lift sub) t)
  renameTerm sub (Apply f e k) = Apply (rename sub f) (renameExp sub e) (renameExp sub k)
  renameTerm sub (Cnt b t) = Cnt (renameTerm (Lift sub) b) (renameTerm (Lift sub) t)
  renameTerm sub (Jump k e) = Jump (rename sub k) (renameExp sub e)
  renameTerm sub (If0 e t1 t2) = If0 (renameExp sub e) (renameTerm sub t1) (renameTerm sub t2)
  renameTerm sub (Exit e) = Exit (renameExp sub e)

  -- Semantics

  public export
  data Value : Tpe -> Type where
    Literal : Int -> Value Itg
    FClosure : Env Lambda.Value xs -> Term (Cont b :: a :: xs) -> Value (Fun a b)
    CClosure : Env Lambda.Value xs -> Term (a :: xs) -> Value (Cont a)

  public export
  data Machine : Type where
    Exe : Env Lambda.Value xs -> Term xs -> Machine

  step : Lambda.Machine -> Lambda.Machine
  step (Exe vs (Let b t)) =
    Exe (FClosure vs b :: vs) t
  step (Exe vs (Apply f (Var x) (Var k))) = case lookup vs f of
    FClosure ws t => Exe (lookup vs k :: lookup vs x :: ws) t
  step (Exe vs (Apply f (Num n) (Var k))) = case lookup vs f of
    FClosure ws t => Exe (lookup vs k :: Literal n :: ws) t
  step (Exe vs (Apply f e (Num n))) impossible
  step (Exe vs (Cnt b t)) =
    Exe (CClosure vs b :: vs) t
  step (Exe vs (Jump k (Var x))) = case lookup vs k of
    CClosure ws t => Exe (lookup vs x :: ws) t
  step (Exe vs (Jump k (Num n))) = case lookup vs k of
    CClosure ws t => Exe (Literal n :: ws) t
  step (Exe vs (If0 (Var x) t1 t2)) = case lookup vs x of
    Literal n => if n == 0
                then Exe vs t1
                else Exe vs t2
  step (Exe vs (If0 (Num n) t1 t2)) =
    if n == 0
       then Exe vs t1
       else Exe vs t2
  step (Exe vs (Exit e)) =
  -- here we loop to indicate that we are done
  Exe vs (Exit e)


-- Translations

{-
    This type augments a DS statement with the information whether there is an
    additional continuation as input for the CPS translation/output for the
    DS translation and if so, which one it is.
-}
data AugmentedStmt : List Tpe -> Type where
  A0 : Stmt ys Nothing -> AugmentedStmt ys
  A1 : Ins (Cont a) xs ys -> Stmt xs (Just a) -> AugmentedStmt ys

-- DS -> CPS

namespace DirectToLambda
  -- Translation on statements

  transform : AugmentedStmt ys -> Term ys
  transform (A0 (Def b s)) = Let (transform (A1 Here b)) (transform (A0 s))
  transform (A0 (Proc b s)) = Cnt (transform (A0 b)) (transform (A0 s))
  transform (A0 (If0 e s1 s2)) = If0 e (transform (A0 s1)) (transform (A0 s2))
  transform (A0 (Run (Var k) s)) = renameTerm (copyName k) (transform (A1 Here s))
  transform (A0 (Run (Num n) s)) impossible
  transform (A0 (Exit e)) = Exit e
  transform (A1 k (Ret e)) = Jump (insToName k) (renameExp (insToWeak k) e)
  transform (A1 k (Seq s b)) = Cnt (transform (A1 (Next k) b)) (transform (A1 Here (renameStmt (insToWeak k) s)))
  transform (A1 k (Call f e)) = Apply (rename (insToWeak k) f) (renameExp (insToWeak k) e) (Var (insToName k))
  transform (A1 k (Def b s)) = Let (transform (A1 Here (renameStmt (insToWeak (Next k)) b))) (transform (A1 (Next k) s))
  transform (A1 k (Proc b s)) = Cnt (transform (A0 (renameStmt (insToWeak (Next k)) b))) (transform (A1 (Next k) s))
  transform (A1 k (If0 e s1 s2)) = If0 (renameExp (insToWeak k) e) (transform (A1 k s1)) (transform (A1 k s2))
  transform (A1 k (Susp s)) = renameTerm (insToSwapRev k) (transform (A0 s))

  -- Translation on machine

  mutual
    transformValue : Direct.Value a -> Lambda.Value a
    transformValue (Literal i) = Literal i
    transformValue (Closure vs s) = FClosure (mapEnv transformValue vs) (transform (A1 Here s))
    transformValue (Captured k) = transformStack k

    transformStack : Stack a -> Lambda.Value (Cont a)
    transformStack (Underflow vs s) = CClosure (mapEnv transformValue vs) (transform (A0 s))
    transformStack (Frame vs s k) = CClosure ((transformStack k) :: (mapEnv transformValue vs)) (transform (A1 (Next Here) s))

  transformMachine : Direct.Machine -> Lambda.Machine
  transformMachine (ExeD vs s) = Exe (mapEnv transformValue vs) (transform (A0 s))
  transformMachine (ExeU vs s k) = Exe ((transformStack k) :: (mapEnv transformValue vs)) (transform (A1 Here s))

-- CPS -> DS

namespace LambdaToDirect
  -- Translation on terms

  mutual
    transform : Term ys -> AugmentedStmt ys

    transform (Apply f e (Var k)) = case nameToIns k of
      Evidence _ k' => resetIfFree k' (Call f e)
    transform (Apply f e (Num n)) impossible

    {-
        In this case we use typing information to preclude k(k) by using that
        Cont t = t is impossible.

        Without using typing information we could instead write:

        ```
        transform (Jump k e) = case nameToIns k of
          Evidence _ k' => resetIfFree k' (Ret e)
        ```
    -}
    transform (Jump k (Var v)) = case nameToIns k of
      Evidence ys' k' => A1 k' (Ret (Var (strengthenNameCont k' v)))
    transform (Jump k (Num n)) = case nameToIns k of
      Evidence _ k' => A1 k' (Ret (Num n))

    transform (Exit e) = A0 (Exit e)

    transform (If0 e t1 t2) = case transform t2 of
      A1 k2 s2 => case transform t1 of
                    A1 k1 s1 => case (insEq k1 k2) of
                                  Just (eq, eqs) => A1 k2 (If0 (strengthenExpItg k2 e) (rewrite sym eqs in rewrite eqCont (sym eq) in s1) s2)
                                  Nothing => A1 k2 (If0 (strengthenExpItg k2 e) (Susp (renameStmt (insToSwap k2) (resetWith k1 s1))) s2)
                    A0 s1 => A1 k2 (If0 (strengthenExpItg k2 e) (Susp (renameStmt (insToSwap k2) s1)) s2)
      A0 s2 => case transform t1 of
                 A1 k1 s1 => A1 k1 (If0 (strengthenExpItg k1 e) s1 (Susp (renameStmt (insToSwap k1) s2)))
                 A0 s1 => A0 (If0 e s1 s2)

    transform (Let b t) = case transform t of
      A0 s' => A0 (Def (transformFun b) s')
      A1 (Next k') s' => resetIfFree k' (Def (transformFun b) (renameStmt (insToWeak (Next k')) s'))

    transform (Cnt b t) = case transform t of
      A0 s' => case transform b of
        A1 (Next k') b' => resetIfFreeSeq k' (Susp s') b'
        A1 Here b' => A0 (Proc (resetWith Here b') s')
        A0 b' => A0 (Proc b' s')
      A1 Here s' => case transform b of
        A1 (Next k') b' => resetIfFreeSeq k' s' b'
        A1 Here b' => A0 (resetWithProc (resetWith Here b') s')
        A0 b' => A0 (resetWithProc b' s')
      A1 (Next k'') s' => case transform b of
        A1 (Next k') b' => resetIfFreeSeq k' (Susp (resetWith (Next k'') s')) b'
        A1 Here b' => resetIfFreeProc k'' (resetWith Here b') s'
        A0 b' => resetIfFreeProc k'' b' s'


    resetIfFree : Ins (Cont a) xs ys -> Stmt ys (Just a) -> AugmentedStmt ys
    resetIfFree k s = case maybeStrengthenStmt k s of
      Just s' => A1 k s'
      Nothing => A0 (Run (Var (insToName k)) s)

    resetWith : Ins (Cont a) xs ys -> Stmt xs (Just a) -> Stmt ys Nothing
    resetWith k s = Run (Var (insToName k)) (renameStmt (insToWeak k) s)

    transformFun : Term (Cont b :: xs) -> Stmt xs (Just b)
    transformFun t = case transform t of
      A0 s' => Susp s'
      A1 Here s' => s'
      A1 (Next k') s' => Susp (resetWith (Next k') s')

    resetIfFreeSeq : Ins (Cont b) xs ys -> Stmt ys (Just a) -> Stmt (a :: xs) (Just b) -> AugmentedStmt ys
    resetIfFreeSeq k s b = resetIfFree k (Seq s (renameStmt (Lift (insToWeak k)) b))

    resetIfFreeProc : Ins (Cont b) xs ys -> Stmt (a :: ys) Nothing -> Stmt ((Cont a) :: xs) (Just b) -> AugmentedStmt ys
    resetIfFreeProc k b s = resetIfFree k (Proc b (renameStmt (Lift (insToWeak k)) s))

    resetWithProc : Stmt (a :: ys) Nothing -> Stmt ys (Just a) -> Stmt ys Nothing
    resetWithProc c s = Proc c (resetWith Here s)

  -- Translation on machine

  mutual
    transformValue : Lambda.Value a -> Direct.Value a
    transformValue (Literal i) = Literal i
    transformValue (FClosure vs t) = Closure (mapEnv transformValue vs) (transformFun t)
    transformValue (CClosure vs t) = Captured (transformCClosure (CClosure vs t))

    transformCClosure : Lambda.Value (Cont a) -> Direct.Stack a
    transformCClosure (CClosure vs t) = case transform t of
      A0 s' => Underflow (mapEnv transformValue vs) s'
      A1 Here s' => Underflow (mapEnv transformValue vs) (resetWith Here s')
      A1 (Next k') s' => Frame (strengthenEnv k' (mapEnv transformValue vs)) s' (transformCClosure (lookup vs (insToName k')))

  transformMachine : Lambda.Machine -> Direct.Machine
  transformMachine (Exe vs t) = case transform t of
    A0 s' => ExeD (mapEnv transformValue vs) s'
    A1 k' s' => ExeU (strengthenEnv k' (mapEnv transformValue vs)) s' (transformCClosure (lookup vs (insToName k')))
