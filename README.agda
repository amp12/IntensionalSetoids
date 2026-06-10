module README where

{- A model of Extensional Type Theory (ETT) in
Agda --safe --without-K
the latter being used as a formalization of basic
Intensional Type Theory with a universe closed under
inductive-recursive definitions. -}

-- Some basic library functions that are needed
open import Prelude public

-- Universes of type-valued setoids
open import Setoid public

-- Extensional Martin-Löf Type Theory (ETT), using the WSLN library
-- for well-scoped locally nameless representation of syntax
open import ETT public

-- Semantics of ETT in the intensional setoid model
open import Semantics public
