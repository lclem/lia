!define(preamble)
~~~~~~~~~~~~~~~~~
module !part().!chapter().!1 where

open import TypeOf

open import part0.index
postulate n' : ℕ
  
open import !part().!chapter() n' renaming (!2 to !2-orig) -- as !chapter()
~~~~~~~~~~~~~~~~~