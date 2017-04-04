

open import ProjectivePlane
open import ProjectivePlane.Fano
open import Level
open import Function using (_$_)

open import ProjectivePlane.CompleteNPoint.Triangle.Desargues

module ProjectivePlane.Desargues where

record Desarguesian  a b c d e : Set  (suc $ a ⊔ b ⊔ c ⊔ d ⊔ e) where
  field
    projective : ProjectivePlane a b c d e
    isFano     : IsFano projective
    desargues  : Desargues projective
  open ProjectivePlane.ProjectivePlane projective public

  desargues← = toDesargues← projective desargues

{- desargues dual is equivalent to desargues converse
   we just should acommodate something
  
   todo:

dual : ∀ {a b c d e} → Desarguesian a b c d e
                     → Desarguesian  c d a b e
dual DD 
  = record { projective = pdual projective 
           ; isFano = dualityFano projective isFano 
           ; desargues = {!!} 
           }
  where 
   open import ProjectivePlane.Duality renaming (dual to pdual)
   open Desarguesian DD
-}
