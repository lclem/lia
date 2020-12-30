!define(preambleCommon)
~~~~~~~~~~~~~~~~~
module !part().!chapter().!1 where

open import TypeOf

open import part0.index
postulate n' : ℕ
~~~~~~~~~~~~~~~~~

!define(preamble)
~~~~~~~~~~~~~~~~~
!preambleCommon(!1)
open import !part().!chapter() n' renaming (!2 to !2-orig)
~~~~~~~~~~~~~~~~~

!define(preamble2)
~~~~~~~~~~~~~~~~~
!preambleCommon(!1)
open import !part().!chapter() n' renaming (!2 to !2-orig; !3 to !3-orig)
~~~~~~~~~~~~~~~~~