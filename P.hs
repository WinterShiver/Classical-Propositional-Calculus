-- Classical Propositional Calculus

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-} 

module P where

data Prop where
    (:>) :: Prop -> Prop -> Prop
    N :: Prop -> Prop

infixr 9 :>

-- Łukasiewicz's Third axiom systems

data Proof p where 
    -- Axioms
    L1 :: Proof (p :> q :> p)
    L2 :: Proof ((p :> q :> r) :> ((p :> q) :> p :> r))
    L3 :: Proof ((N p :> N q) :> (q :> p))
    -- Deduction
    MP :: Proof p -> Proof (p :> q) -> Proof q

-- Proof example

eg1 :: Proof ((p :> q) :> (p :> p))
eg1 = L1 `MP` L2

-- Theorem examples

theo1 :: Proof (p :> p)
theo1 = L1 `MP` (L1 `MP` L2)

theo2 :: Proof (N q :> (q :> p))
theo2 = L1 `MP` ((L3 `MP` L1) `MP` L2)

-- References
-- Types and Programming Languages, Chapter 3
-- 数理逻辑 汪芳庭
-- https://en.wikipedia.org/wiki/List_of_Hilbert_systems#Classical_propositional_calculus_systems
