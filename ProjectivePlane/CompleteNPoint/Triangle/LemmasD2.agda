{-# OPTIONS --no-eta-equality #-} 

open import Function using (_$_)
open import Data.Fin
open import Data.Fin.Setoid
open import ProjectivePlane
open import Relation.Binary.Apartness


module ProjectivePlane.Polygon.Triangle.LemmasD2
       {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.PropertiesGeneral PP
open import ProjectivePlane.Polygon.Triangle.Perspective PP
open import ProjectivePlane.Polygon.Triangle.PerspectiveProperties PP
open import ProjectivePlane.Polygon.Triangle.DesarguesSymmetries PP





{-  este módulo queda anulado -}


module Q0-Q2-PerspectiveCenter
       {T T'}
       (arePerspectiveAxe : ArePerspectiveAxe T T')
       where
       
        open ArePerspectiveAxe arePerspectiveAxe
        open AreDistinct areDistinct
        open import ProjectivePlane.Polygon.Triangle.LemmasD1 PP
        open Q0-Q2-Distinct  arePerspectiveAxe using (Q0 ; Q2 ; Q0≠Q2 ; A♯C)
        open DesarguesLemmas arePerspectiveAxe using (B∉T₀ ; B ; 2♯1)

        apT'T = flipPerspectiveAxe arePerspectiveAxe 
        apTT'sym = permPerspectiveAxe (swap  `0 `2 IdInjectiveFun♯) arePerspectiveAxe

        open ProjectivePlane.Rel♯Instances PP
        open ProjectivePlane.Setoid♯Instances PP

  
        paQ0Q2 : ArePerspectiveCenter Q0 Q2
        paQ0Q2 = record
                   { Center = meet $ sd♯ 0♯2
                   ; areDistinct =  Q0≠Q2
                   ; Center-∉-T =   λ {i} {j} {i♯j} → B∉T₀ {!i!} {!!} {!!}
                                    -- λ {_} {_} {i♯j} → B∉T₀ _ _ i♯j
                   ; Center-∉-T' =  {!!}
                                    -- λ {_} {_} {i♯j} →  ⟨ meet-cong join-comm join-comm ⟩⇐
                                    --                     DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                   ; perspective = persp
                   }

            where


                 persp : ∀ i → B ∈ join  (AreDistinct.vrt♯  Q0≠Q2 i)
                 persp zero = meetᵣ 
                 persp (suc zero) = meetₗ
                 persp (suc (suc zero)) = perspective 0♯2 ⇒⟨ unq-join A♯C (perspective 0♯1) (perspective 2♯1) ⟩ 
                 persp (suc (suc (suc ())))        


