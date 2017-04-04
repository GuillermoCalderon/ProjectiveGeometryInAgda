
-- open import Relation.Nullary
open import Data.Empty
open import Level using (_⊔_)
open import Function using (_$_)
open import Relation.Binary.Apartness
import Data.Nat as Nat
open import Data.Fin
open import Data.Fin.Setoid
open import ProjectivePlane

import Relation.Binary.EqReasoning as EqR

module ProjectivePlane.Polygon.Triangle.LemmasD1
       {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.Polygon PP
open import ProjectivePlane.PropertiesGeneral PP
open import ProjectivePlane.Polygon.Triangle PP
open import ProjectivePlane.Polygon.Triangle.Perspective PP
open import ProjectivePlane.Polygon.Triangle.PerspectiveProperties PP
open import ProjectivePlane.Polygon.Triangle.DesarguesSymmetries PP

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP




module Q0-Q2
       {T T'}
       (arePerspectiveAxe : ArePerspectiveAxe T T')
       where
       

        open ArePerspectiveAxe arePerspectiveAxe
        open AreDistinct areDistinct
        apTT'sym = permPerspectiveAxe (swap  `0 `2 IdInjectiveFun♯) arePerspectiveAxe
        open TriangleD arePerspectiveAxe
        open DesarguesLemmas arePerspectiveAxe

        

        A = meet $ sd♯ 0♯1
        C = meet $ sd♯ 2♯1

        T-01♯21 : edge T 0♯1 ♯ edge T 2♯1
        T-01♯21 = sides♯ T 0♯2 0♯1


        T1♯A :  (T $∙ `1) ♯ A
        T1♯A = C0 axe-∉-T  (perspective 0♯1)

        T-01∙21♯A : meet T-01♯21 ♯ A
        T-01∙21♯A =  ⟨ sym  meet-joinᵣᵣ ⟩⇐ T1♯A


        A∉T-21 : A ∉ edge T 2♯1
        A∉T-21 = C7-a  T-01♯21 (symmetry T-01∙21♯A) meetₗ

        A♯01∙21 : A ♯ (meet T-01♯21 )
        A♯01∙21 = C0 A∉T-21  meetᵣ

        A∉T21 :  A ∉ (edge T $ symmetry 1♯2)
        A∉T21 = C7-a (C5 joinₗ ((Polyangle.nonc3 T 0♯2 (symmetry 1♯2) 0♯1))) A♯01∙21 meetₗ


        A♯C : A ♯ C
        A♯C = C0 A∉T21  meetₗ

        -- two center-perspective triangles
        Q0 =  T₀ -- trp 0♯1    -- 0'0A
        Q2 =  trp 2♯1    -- 2'2C


        Q0≠Q2 :  AreDistinct Q0 Q2
        Q0≠Q2 = record { vrt♯ = v ; sd♯ = λ {i j}→ s i j }
          where

              v : ∀ i → (Q0 $∙ i) ♯ (Q2 $∙ i)
              v zero             
                =  
                   T' $♯ 0♯2
              v (suc zero)       
                =  
                   T $♯ 0♯2
              v (suc (suc zero)) 
                = 
                   A♯C
              v (suc (suc (suc ())))
            
              
              s01 : (edge Q0 0♯1) ♯ (edge Q2  0♯1)
              s01 = 
                  ⟨  join-comm ⟩⇐ 
                  II'♯JJ' 0♯2  
                  ⇒⟨ join-comm ⟩

              s02 : (edge Q0 0♯2) ♯ (edge Q2  0♯2)
              s02 = 
                  ⟨ join-cong refl meet-comm ⟩⇐  
                  DesarguesLemmas.IA♯JB  (flipPerspectiveAxe arePerspectiveAxe) 0♯2 0♯1 2♯1 
                  ⇒⟨ join-cong refl meet-comm ⟩
  

              s12 = IA♯JB 0♯2 0♯1 2♯1

              s : ∀ i j → (i♯j : i ♯ j) → 
                  edge Q0 i♯j ♯ edge Q2 i♯j


              s zero (suc zero) i♯j = s01
              s zero (suc (suc zero)) i♯j = s02

              s (suc zero) zero i♯j =  ⟨ join-comm ⟩⇐  s01 ⇒⟨ join-comm ⟩
              s (suc zero) (suc (suc zero)) i♯j = s12

              s (suc (suc zero)) zero i♯j = ⟨ join-comm ⟩⇐  s02 ⇒⟨ join-comm ⟩
              s (suc (suc zero)) (suc zero) i♯j = ⟨ join-comm ⟩⇐  s12 ⇒⟨ join-comm ⟩

              s zero zero i♯j = ⊥-elim $ irreflexive i♯j
              s (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ irreflexive i♯j
              s (suc zero) (suc zero) i♯j =  ⊥-elim $ irreflexive i♯j
              s (suc (suc (suc ()))) _ _
              s _ (suc (suc (suc ()))) _

        paQ0Q2 : ArePerspectiveCenter Q0 Q2
        paQ0Q2 = record
                   { Center = meet $ sd♯ 0♯2
                   ; areDistinct =  Q0≠Q2
                   ; Center-∉-T =   -- {!B∉T₀!}
                                    λ {_} {_} {i♯j} → B∉T₀ _ _ i♯j
                   ; Center-∉-T' =   λ {i} {j} {i♯j} → cnt∉Q₂ _ _ i♯j 
                                    --λ {_} {_} {i♯j} →  ⟨ meet-cong join-comm join-comm ⟩⇐
                                    --                     DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                   ; perspective = persp
                   }

            where


                 persp : ∀ i → B ∈ join  (AreDistinct.vrt♯  Q0≠Q2 i)
                 persp zero = meetᵣ 
                 persp (suc zero) = meetₗ
                 persp (suc (suc zero)) = perspective 0♯2 ⇒⟨ unq-join A♯C (perspective 0♯1) (perspective 2♯1) ⟩ 
                 persp (suc (suc (suc ())))        

                 cnt∉Q₂ :  ∀ i j →
                           ( i♯j : i ♯ j) →
                           meet  (sd♯ 0♯2) ∉ edge Q2 i♯j

                 -- we have to define all cases in order to improve performace of  the type checker 
                 cnt∉Q₂ zero (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ zero (suc (suc zero)) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc zero) (suc (suc zero)) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc zero) zero i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc (suc zero)) zero i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
                 cnt∉Q₂ (suc (suc zero)) (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DesarguesLemmas.B∉T₀  apTT'sym  _ _ i♯j
            
                 cnt∉Q₂ zero zero i♯j = ⊥-elim $ refl i♯j
                 cnt∉Q₂ (suc zero) (suc zero) i♯j = ⊥-elim $ refl i♯j
                 cnt∉Q₂ (suc (suc zero)) (suc (suc zero))  i♯j = ⊥-elim $ refl i♯j
                 cnt∉Q₂ (suc (suc (suc ()))) _ _ 
                 cnt∉Q₂ _ (suc (suc (suc ())))  _ 

