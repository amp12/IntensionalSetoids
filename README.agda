----------------------------------------------------------------------
-- IntensionalSetoids
----------------------------------------------------------------------
module README where

{- We show that a certain notion of displayed setoid (family of
setoids) in intensional type theory can be used to give a semantics
for extensional type theory with universes (ETU). Agda with options
--safe --without-K
serves as a machine-checkable formalization of intentional type theory
augmented with a universe closed under inductive-recursive definitions
(IRU). The syntax of ETU is defined in IRU in a traditional extrinsic
form, using a well-scoped locally nameless representation of its
terms. Giving the semantics of ETU in terms of displayed setoids is
complicated by the very limited means of expression afforded by
IRU. As a corollary we obtain a proof within IRU of the consistency of
ETU. -}

-- Some basic library functions
open import Prelude public

-- Universes of type-valued setoids
open import Setoid public

-- Extensional type theory with universes (ETU)
open import ETU public

-- Semantics of ETU in the intensional setoid model, and as a
-- corollary its logical consistency.
open import Semantics public
