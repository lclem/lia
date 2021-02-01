module TypeOf where

import Data.Unit
import Reflection

macro
    typeOf : Reflection.Term → Reflection.Term → Reflection.TC Data.Unit.⊤
    typeOf f hole =
        Reflection.bindTC (Reflection.inferType f) λ goal →
        Reflection.unify hole goal