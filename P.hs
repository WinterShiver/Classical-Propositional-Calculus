-- Classical Propositional Calculus

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-} 

module P where

-- Proposition
data Prop where
    -- Implies
    (:>) :: Prop -> Prop -> Prop
    -- Not
    N :: Prop -> Prop

infixr 9 :>

-- And, Or, EqualsTo

(∧) :: Prop -> Prop -> Prop
p ∧ q = N (p :> N q)

(∨) :: Prop -> Prop -> Prop 
p ∨ q = N p :> q

infixl 8 ∧
infixl 7 ∨

(↔) :: Prop -> Prop -> Prop
p ↔ q = p :> q ∧ q :> p 

infix 6 ↔

-- Łukasiewicz's Third axiom systems

data Proof p where 
    -- Axioms
    L1 :: Proof (p :> q :> p)
    L2 :: Proof ((p :> q :> r) :> ((p :> q) :> p :> r))
    L3 :: Proof ((N p :> N q) :> (q :> p))
    -- Deduction
    MP :: Proof p -> Proof (p :> q) -> Proof q
    -- Others
    -- Axiom :: Proof p
    Sorry :: Proof p

-- Proof example

eg1 :: Proof p -> Proof (q :> p)
eg1 pf1 = pf1 `MP` L1

eg2 :: Proof ((p :> q) :> (p :> p))
eg2 = L1 `MP` L2

eg3 :: Proof p -> Proof (q :> p :> r) -> Proof (q :> r)
eg3 pf1 pf2 = (pf1 `MP` L1) `MP` (pf2 `MP` L2)

-- Theorems

-- 同一律 
theo1 :: Proof (p :> p)
theo1 = L1 `MP` (L1 `MP` L2)

-- 否定前件律
theo2 :: Proof (N q :> (q :> p))
theo2 = L1 `MP` ((L3 `MP` L1) `MP` L2)

-- 有矛盾公式集
theo3 :: Proof q -> Proof (N q) -> Proof p 
theo3 pf1 pf2 = pf1 `MP` (pf2 `MP` theo2)

-- 演绎定理 用不到L3
theo4 :: ((Proof p -> Proof q) -> Proof (p :> q), Proof (p :> q) -> Proof p -> Proof q)
theo4 = (const Sorry, flip MP)

hs :: Proof (p :> q) -> Proof (q :> r) -> Proof (p :> r)
hs pf_pq pf_qr = fst theo4 (\pf_p -> pf_p `MP` pf_pq `MP` pf_qr)

-- 否定肯定律
theo5 :: Proof ((N p :> p) :> p)
theo5 = fst theo4 (\pf -> pf `MP` (pf `MP` (theo2 `MP` L2) `MP` L3))

-- 反证律
theo6 :: (pfs -> Proof (N p) -> Proof q) -> (pfs -> Proof (N p) -> Proof (N q)) -> pfs -> Proof p 
theo6 pf1 pf2 = \pfs -> fst theo4 (\pfnp -> let
    pfq = pf1 pfs pfnp 
    pfnq = pf2 pfs pfnp
    in pfq `MP` (pfnq `MP` theo2)) `MP` theo5 

-- 双重否定律

dd :: Proof (N (N p) :> p)
dd = let pf1 = \pfnnp -> snd theo4 theo1 in fst theo4 $ theo6 pf1 (flip pf1)

-- 归谬律

theo7 :: (pfs -> Proof p -> Proof q) -> (pfs -> Proof p -> Proof (N q)) -> pfs -> Proof (N p)
theo7 pf1 pf2 = theo6
    (\pfs pfnnp -> pf1 pfs (pfnnp `MP` dd))
    (\pfs pfnnp -> pf2 pfs (pfnnp `MP` dd))

-- 第二双重否定律

dd2 :: Proof (p :> N (N p))
dd2 = let pf1 = \pfp -> snd theo4 theo1 in fst theo4 $ theo7 (flip pf1) pf1

-- References
-- Types and Programming Languages, Chapter 3
-- 数理逻辑 汪芳庭
-- https://en.wikipedia.org/wiki/List_of_Hilbert_systems#Classical_propositional_calculus_systems
