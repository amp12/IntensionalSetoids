----------------------------------------------------------------------
-- IntensionalSetoids
----------------------------------------------------------------------
module README where

{- We give a new notion of displayed setoid (family of setoids) in
intensional type theory. It is used to give a semantics of extensional
type theory with universes (ETU) within Agda with
options --safe --without-K, used as a machine-checkable
formalization of intentional type theory augmented with a universe
closed under inductive-recursive definitions (ITU). The syntax of ETU
is defined in safe Agda in a traditional extrinsic form, using a
well-scoped locally nameless representation of its expressions. Giving
its semantics in the ITU setoid model is complicated by the very
limited means of expression afforded by ITU. As a corollary we obtain
a proof of the consistency of ETU within ITU. -}

-- Some basic library functions
open import Prelude public

-- Universes of type-valued setoids
open import Setoid public

-- Extensional type theory with universes (ETU)
open import ETU public

-- Semantics of ETU in the intensional setoid model, and as a
-- corollary its logical consistency.
open import Semantics public
