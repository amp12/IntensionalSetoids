module Setoid where

-- The definition of setoids and displayed setoids
open import Setoid.Definition public

-- Inductive-recursively defined countable hierchy of nested universes
-- of type-valued setoids closed under Pi-types, extensional equality
-- types, empty and natural number types
open import Setoid.Universes public

-- Lifting from a universe to a higher universe
open import Setoid.Lift public

-- Agda-style Pi-types
open import Setoid.PiType public

-- Extensional equality
open import Setoid.EqualityType public

-- Empty type
open import Setoid.EmptyType public

-- Natural numbers
open import Setoid.NatType public

-- The setoid-enriched category-with-familes given by the universes
open import Setoid.CwF public
