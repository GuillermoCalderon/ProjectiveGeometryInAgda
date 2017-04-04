{-# OPTIONS --no-eta-equality #-} 

open import Level using (_⊔_)
open import Function using (_∘_ ; _$_)
open import Relation.Binary.Apartness
open import Data.Fin
open import Data.Fin.Setoid
open import ProjectivePlane


module ProjectivePlane.CompleteNPoint.Triangle.DesarguesSymmetries
       {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.CompleteNPoint PP
open import ProjectivePlane.PropertiesGeneral PP
open import ProjectivePlane.CompleteNPoint.Triangle PP
open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP
open import ProjectivePlane.CompleteNPoint.Triangle.PerspectiveProperties PP

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP

-- symmetries of Desargues configuration

flipPerspectiveAxis :                       
    ∀ {T T'}
    → ArePerspectiveAxis T  T'
    → ArePerspectiveAxis T' T
flipPerspectiveAxis arePA-TT' 
  = record
      { axis = axis
      ; areDistinct = 
           record { vrt♯ = symmetry ∘ vrt♯ ; sd♯ = symmetry ∘ sd♯ }                       
      ; axis-∉-T = axis-∉-T'
      ; axis-∉-T' = axis-∉-T
      ; perspective = λ i♯j →  ⟨ meet-comm ⟩⇐ perspective i♯j  
      }
    where open ArePerspectiveAxis arePA-TT'
          open AreDistinct areDistinct


permPerspectiveAxis : 
    ∀ {T T'}
    → (F : InjectiveFun♯ (setoidFin 3) (setoidFin 3))
    → ArePerspectiveAxis T  T'
    → ArePerspectiveAxis (subComplete-N-Point F T) (subComplete-N-Point F T')
permPerspectiveAxis F arePA-TT'
  =  record
       { axis = axis
       ; areDistinct = record { vrt♯ = λ i → vrt♯ $ ⟨ fun♯ F ⟩$ i ; sd♯ = sd♯ ∘ isInjective F }
       ; axis-∉-T =  λ {i} → axis-∉-T  { ⟨ fun♯ F ⟩$ i }
       ; axis-∉-T' = λ {i} → axis-∉-T' { ⟨ fun♯ F ⟩$ i }
       ; perspective = perspective ∘ isInjective F
       }
  where open ArePerspectiveAxis arePA-TT'
        open AreDistinct areDistinct
