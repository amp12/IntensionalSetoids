----------------------------------------------------------------------
-- IntensionalSetoids
----------------------------------------------------------------------
module README where

{- A semantics of extensional type theory with universes (ETU) is
  constructed within Agda with options --safe --without-K, used as a
  machine-checkable formalization of intentional type theory augmented
  with a universe closed under inductive-recursive definitions
  (ITU). The model of ETU uses a simple, but apparently new variation
  on the notion of displayed setoids. The syntax of ETU is defined in
  Agda in a traditional extrinsic form, using a well-scoped locally
  nameless representation of its expressions. Giving its semantics in
  the setoid model is complicated by the very limited means of
  expression afforded by ITU. As a corollary we obtain a proof of the
  consistency of ETU within ITU. -}

-- Some basic library functions
open import Prelude public

-- Universes of type-valued setoids
open import Setoid public

-- Extensional type theory with universes (ETU) (using the WSLN
-- library for well-scoped locally nameless representation of syntax),
-- its semantics in the intensional setoid model, and as a corollary
-- its logical consistency.
open import ETU public
