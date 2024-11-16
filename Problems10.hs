{-# LANGUAGE StandaloneDeriving #-}
module Problems10 where

{-------------------------------------------------------------------------------

CS:3820 Fall 2024 Problem Set 10
================================

This problem set explores another extension of the λ-calculus with effects.

The new effect we're adding is *exceptions*.  We have two operations:

* The expression `Throw m` throws an exception; the exception's payload is the
  value of expression `m`.
* The expression `Catch m y n` runs expression `m`:
  - If that expression evaluates to `v`, then `Catch m y n` also evaluates to
    `v`.
  - If that expression throws an exception with payload `w`, then `Catch m y n`
    evaluates to `n[w/y]`.

To keep things interesting, our language will *also* have an accumulator.
Changes to the accumulator should persist, even if an exception is thrown.
Concretely, in the expression:

    Catch (Plus (Store (Const 2)) (Throw (Const 3))) "y" Recall

The `Recall` in the catch block should return the value `Const 2`, resulting
from the `Store` in the first addend, not whatever the initial value of the
accumulator was.

-------------------------------------------------------------------------------}

-- Here is our expression data type

data Expr = -- Arithmetic
            Const Int | Plus Expr Expr 
            -- λ-calculus
          | Var String | Lam String Expr | App Expr Expr
            -- accumulator
          | Store Expr | Recall 
            -- exceptions
          | Throw Expr | Catch Expr String Expr 
  deriving Eq          

deriving instance Show Expr

-- Here's a show instance that tries to be a little more readable than the
-- default Haskell one; feel free to uncomment it (but then, be sure to comment
-- out the `deriving instance` line above).

{-
instance Show Expr where
  showsPrec _ (Const i) = shows i
  showsPrec i (Plus m n) = showParen (i > 1) $ showsPrec 2 m . showString " + " . showsPrec 2 n
  showsPrec i (Var x) = showString x
  showsPrec i (Lam x m) = showParen (i > 0) $ showString "\\" . showString x . showString " . " . showsPrec 0 m
  showsPrec i (App m n) = showParen (i > 2) $ showsPrec 2 m . showChar ' ' . showsPrec 3 n
  showsPrec i (Store m) = showParen (i > 2) $ showString "store " . showsPrec 3 m
  showsPrec i Recall    = showString "recall"
  showsPrec i (Throw m) = showParen (i > 2) $ showString "throw " . showsPrec 3 m
  showsPrec i (Catch m y n) = showParen (i > 0) $ showString "try " . showsPrec 0 m . showString " catch " . showString y . showString " -> " . showsPrec 0 n
-}  

-- Values are, as usual, integer and function constants
isValue :: Expr -> Bool
isValue (Const _) = True
isValue (Lam _ _) = True
isValue _         = False

{-------------------------------------------------------------------------------

Problems 1 & 2: Substitution
----------------------------

For your first problems, you'll need to implement substitution for our language.

I've already provided the cases for the λ-calculus.  In the case for `Lam`, I've
used a helper function `substUnder`, which only substitutes if the new variable
does not shadow the variable being replaced.

In implementing your cases, remember: substitution is about variables.  While
most of the imperative features of this language don't interact with variables,
`Catch` absolutely *does*.

Consider this example:

    (\x -> try M catch x -> N) [L/x]

Or, in our `Expr` data type:

    subst "x" l (Lam "x" (Catch m "x" n))

Suppose there's an instance of variable `x` in `N`.  Do you think that it should
be replaced by the substitution?

-------------------------------------------------------------------------------}

-- Utility to check if an expression is a `Throw`
isThrow :: Expr -> Bool
isThrow (Throw _) = True
isThrow _         = False

substUnder :: String -> Expr -> String -> Expr -> Expr
substUnder x m y n 
  | x == y = n
  | otherwise = subst x m n

subst :: String -> Expr -> Expr -> Expr
subst _ _ (Const i) = Const i
subst x m (Plus n1 n2) = Plus (subst x m n1) (subst x m n2)
subst x m (Var y) 
  | x == y = m
  | otherwise = Var y
subst x m (Lam y n) = Lam y (substUnder x m y n)
subst x m (App n1 n2) = App (subst x m n1) (subst x m n2)
subst x m (Store n) = Store (subst x m n) -- Substitute into the stored expression
subst _ _ Recall = Recall -- No substitution for `Recall`
subst x m (Throw n) = Throw (subst x m n) -- Substitute into the thrown expression
subst x m (Catch n1 y n2)
  | x == y    = Catch (subst x m n1) y n2 -- Do not substitute if `y` shadows `x`
  | otherwise = Catch (subst x m n1) y (substUnder x m y n2) -- Substitute otherwise

{-------------------------------------------------------------------------------

Problems 3 - 10: Small-step semantics
-------------------------------------

For the remaining problems, you'll need to implement a small-step semantics for
our language.

Your semantics should be *left-to-right* and *call-by-value*.

The program state is a pair `(prog, acc)`, where `prog` is the program being
evaluated, and `acc` is the current accumulator.

Because `Store` gets call-by-value treatment, `acc` should always be a value.

Intuitively, `Store m` needs to evaluate `m` (however many steps that takes),
and then replace the current accumulator contents with the value of `m`.
`Recall` returns the contents of the accumulator.  For more detailed treatment,
please see Lecture 12 on ICON.

The more interesting cases are for `Throw` and `Catch`.

We'll implement `Throw` by "bubbling" exceptions up through computations.

For example, consider this expression

    Plus (Const 1) (Plus (Const 2) (Plus (Const 3) (Throw (Const 4))))

For this expression to step, we need

    Plus (Const 3) (Throw (Const 4))

to step.  But we can't add anything here: the second argument is a thrown
exception.  Instead, we replace the entire `Plus` expression with the exception.
That is, the first step is:

    Plus (Const 1) (Plus (Const 2) (Plus (Const 3) (Throw (Const 4))))
      ~~>
    Plus (Const 1) (Plus (Const 2) (Throw (Const 4)))

Note: the exception is still being thrown!  Now, by the same logic, our next
step is:

    Plus (Const 1) (Plus (Const 2) (Throw (Const 4)))
      ~~>
    Plus (Const 1) (Throw (Const 4))

and finally:

    Plus (Const 1) (Throw (Const 4))
      ~~>
    Throw (Const 4)

Now we can't make any more progress; this isn't a value, it's a thrown
exception, but without something to catch the exception we can't simplify any
further.

Exceptions "bubble" through all the points evaluation can happen: `Plus`, `App`,
and `Store`.  

`Throw` itself also gets call-by-value treatment: an exception does not start
"bubbling" until the thrown expression is itself a value.  Here is an example:

  Plus (Const 1) (Throw (Plus (Const 2) (Const 3)))
    ~~>
  Plus (Const 1) (Throw (Const 5))
    ~~>
  Throw (Const 5)

Note: exceptions bubble through `Throw` itself as well.

Now we can explain `Catch`.  `Catch m y n` begins by evaluating `m`.  If `m`
evaluates to a value `v`, then so does `Catch m y n`.  But, if `m` evaluates to
a thrown exception `Throw w`, then `Catch m y n` evaluates to `n[w/y]`.

For example:

    Catch (Plus (Const 1) (Throw (Const 2))) "y" (Plus (Var "y") (Const 1))
      ~~>
    Catch (Throw (Const 2)) "y" (Plus (Var "y") (Const 1))
      ~~>
    Plus (Const 2) (Const 1)
      ~~>
    Const 3

When implementing your `smallStep` function: feel free to start from the code in
Lecture 12.  But be sure to handle *all* the cases where exceptions need to
bubble; this won't *just* be `Throw` and `Catch.

-------------------------------------------------------------------------------}

-- Evaluate expressions to integers
eval :: Expr -> Int
eval (Const i) = i
eval _ = error "Non-constant expression in eval"

smallStep :: (Expr, Expr) -> Maybe (Expr, Expr)
-- Constants do not reduce further
smallStep (Const i, acc) = Nothing

-- Variables are not reduced directly
smallStep (Var x, acc) = Nothing

-- Plus:
smallStep (Plus e1 e2, acc)
  | isValue e1 && isValue e2 = Just (Const (eval e1 + eval e2), acc)
  | isThrow e1 = Just (e1, acc) -- Exception bubbles
  | not (isValue e1) = case smallStep (e1, acc) of
      Just (e1', acc') -> Just (Plus e1' e2, acc')
      Nothing -> Nothing
  | isThrow e2 = Just (e2, acc)
  | otherwise = case smallStep (e2, acc) of
      Just (e2', acc') -> Just (Plus e1 e2', acc')
      Nothing -> Nothing

-- Application: left-to-right, call-by-value
smallStep (App (Lam x body) arg, acc)
  | isValue arg = Just (subst x arg body, acc)
  | isThrow arg = Just (arg, acc) -- Exception bubbles in argument
  | otherwise = case smallStep (arg, acc) of
      Just (arg', acc') -> Just (App (Lam x body) arg', acc')
      Nothing -> Nothing
smallStep (App f arg, acc)
  | isThrow f = Just (f, acc) -- Exception bubbles in function
  | not (isValue f) = case smallStep (f, acc) of
      Just (f', acc') -> Just (App f' arg, acc')
      Nothing -> Nothing

-- Lambda functions do not reduce further on their own
smallStep (Lam x body, acc) = Nothing

-- Accumulator: Store updates accumulator, Recall retrieves it
smallStep (Store e, acc)
  | isValue e = Just (Const 0, e) -- Return `Const 0` as a unit value and update accumulator
  | isThrow e = Just (e, acc) -- Exception bubbles without updating accumulator
  | otherwise = case smallStep (e, acc) of
      Just (e', acc') -> Just (Store e', acc')
      Nothing -> Nothing

-- Throw: evaluates the thrown value before bubbling
smallStep (Throw v, acc)
  | isValue e = Just (e, e) -- Store the value in the accumulator
  | isThrow e = Just (e, acc) -- Exception bubbles
  | otherwise = case smallStep (e, acc) of
      Just (e', acc') -> Just (Store e', acc')
      Nothing -> Nothing
smallStep (Recall, acc) = Just (acc, acc)

-- Catch: evaluates `m`, handles value or exception
smallStep (Catch m y n, acc)
  | isValue m = Just (m, acc) -- If `m` is a value, return it
  | isThrow m = case m of
      Throw v -> Just (subst y v n, acc) -- Handle exception
      _       -> Nothing
  | otherwise = case smallStep (m, acc) of
      Just (m', acc') -> Just (Catch m' y n, acc')
      Nothing -> Nothing

steps :: (Expr, Expr) -> [(Expr, Expr)]
steps s = case smallStep s of
            Nothing -> [s]
            Just s' -> s : steps s'

prints :: Show a => [a] -> IO ()
prints = mapM_ print
