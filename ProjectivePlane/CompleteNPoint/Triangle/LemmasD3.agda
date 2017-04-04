open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product hiding (swap)
open import Level using (_⊔_)
open import Function using (_$_)
open import Relation.Binary.Apartness
open import Data.Fin
open import Data.Fin.Setoid
open import ProjectivePlane
import Relation.Binary.PropositionalEquality as PropEq


module ProjectivePlane.Polygon.Triangle.LemmasD3
       {a b c d e}
       (PP : ProjectivePlane.ProjectivePlane a b c d e) where

open ProjectivePlane.ProjectivePlane PP
open import ProjectivePlane.Polygon PP
open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP
open import ProjectivePlane.PropertiesGeneral PP
--open import ProjectivePlane.Polygon.Triangle PP
open import ProjectivePlane.Polygon.Triangle.Perspective PP
open import ProjectivePlane.Polygon.Triangle.PerspectiveProperties PP




module Q0-Q2
       {T T'}
       (arePerspectiveAxe : ArePerspectiveAxe T T')
       (direct : Desargues)
       where
       

        open ArePerspectiveAxe arePerspectiveAxe
        open AreDistinct areDistinct
        open import ProjectivePlane.Polygon.Triangle.LemmasD1 PP as D1
        open D1.Q0-Q2  arePerspectiveAxe
        open TriangleD arePerspectiveAxe
        open DesarguesLemmas arePerspectiveAxe
        open import ProjectivePlane.Polygon.Triangle.DesarguesSymmetries PP

        apT'T : ArePerspectiveAxe T' T
        apT'T = flipPerspectiveAxe arePerspectiveAxe



        perspectiveAxe-Q0Q2 = direct Q0 Q2 paQ0Q2 



        axeQ = ArePerspectiveAxe.axe  perspectiveAxe-Q0Q2

        T01≈Q0-12  : edge T 0♯1  ≈ edge Q0 1♯2
        T01≈Q0-12  = unq-join (Q0 $♯ 1♯2)  joinₗ meetₗ


        T21≈Q2-12  : edge T 2♯1  ≈ edge Q2 1♯2
        T21≈Q2-12  = unq-join (Q2 $♯ 1♯2)  joinₗ meetₗ
        
        1∈Q0-12 : (T $∙ `1) ∈ edge Q0 1♯2
        1∈Q0-12 =  joinᵣ ⇒⟨ T01≈Q0-12 ⟩


        
        1∈Q2-12 : (T $∙ `1) ∈ edge Q2 1♯2
        1∈Q2-12 =  joinᵣ ⇒⟨ T21≈Q2-12 ⟩           

        1∈axeQ   : (T $∙ `1) ∈ axeQ
        1∈axeQ = ⟨ unq-meet _  1∈Q0-12 1∈Q2-12  ⟩⇐ 
                 ArePerspectiveAxe.perspective perspectiveAxe-Q0Q2 1♯2

        1'∈axeQ : (T' $∙ `1) ∈ axeQ
        1'∈axeQ =  ⟨ unq-meet _ 
                              (joinᵣ ⇒⟨ unq-join (Q0 $♯ 0♯2)  joinₗ meetᵣ ⟩)
                              (joinₗ ⇒⟨ unq-join (Q2 $♯ 0♯2) {edge T' 1♯2} joinᵣ (meetᵣ ⇒⟨ join-comm ⟩) ⟩) 
                   ⟩⇐ 
                   ArePerspectiveAxe.perspective perspectiveAxe-Q0Q2 0♯2





        axeQ≈11' : axeQ ≈ join (vrt♯ `1)
        axeQ≈11' = unq-join (vrt♯ `1)  1∈axeQ 1'∈axeQ


        Center∉T : (i j : Fin 3) → (i♯j : i ♯ j) → Cnt ∉ (edge T i♯j)

        Center∉T zero (suc zero) _  =  Cnt∉T01 
        Center∉T zero (suc (suc zero))  i♯j = Cnt∉T02 
        Center∉T (suc zero) zero i♯j =  Cnt∉T01 {symmetry i♯j} ⇒⟨ join-comm ⟩
        Center∉T (suc (suc zero)) zero  i♯j =  Cnt∉T02 {symmetry i♯j} ⇒⟨ join-comm ⟩
        Center∉T (suc zero) (suc (suc zero)) i♯j = Cnt∉T12
        Center∉T (suc (suc zero)) (suc zero) i♯j = Cnt∉T12 {symmetry i♯j} ⇒⟨ join-comm ⟩
        Center∉T zero zero i♯j = ⊥-elim $ i♯j PropEq.refl
        Center∉T (suc zero) (suc zero) i♯j = ⊥-elim $ i♯j PropEq.refl
        Center∉T (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ i♯j PropEq.refl
        Center∉T (suc (suc (suc ()))) _ _
        Center∉T _  (suc (suc (suc ()))) _


        module DLT'T = DesarguesLemmas {T'} {T} apT'T

        Center∉T' : (i j : Fin 3) → (i♯j : i ♯ j) → Cnt ∉ (edge T' i♯j)

        Center∉T' zero (suc zero) _  =  ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T01 
        Center∉T' zero (suc (suc zero))  i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T02 
        Center∉T' (suc zero) zero i♯j =  ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T01 {symmetry i♯j} ⇒⟨ join-comm ⟩
        Center∉T' (suc (suc zero)) zero  i♯j =  ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T02 {symmetry i♯j} ⇒⟨ join-comm ⟩
        Center∉T' (suc zero) (suc (suc zero)) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T12
        Center∉T' (suc (suc zero)) (suc zero) i♯j = ⟨ meet-cong join-comm join-comm ⟩⇐ DLT'T.Cnt∉T12 {symmetry i♯j} ⇒⟨ join-comm ⟩
        Center∉T' zero zero i♯j = ⊥-elim $ i♯j PropEq.refl
        Center∉T' (suc zero) (suc zero) i♯j = ⊥-elim $ i♯j PropEq.refl
        Center∉T' (suc (suc zero)) (suc (suc zero)) i♯j = ⊥-elim $ i♯j PropEq.refl
        Center∉T' (suc (suc (suc ()))) _ _
        Center∉T' _  (suc (suc (suc ()))) _


        persp : (i : Fin 3) → (meet $ II'♯JJ' 0♯1) ∈ join (vrt♯ i)


        persp zero = meetₗ
        persp (suc zero) = meetᵣ
        persp (suc (suc zero)) = ⟨ sym (unq-meet _ 
                                                 { meet (symmetry $ AreDistinct.sd♯  Q0≠Q2 0♯1)}
                                                 (meetᵣ ⇒⟨ join-comm ⟩)

                                                 ( ⟨ meet-comm  ⟩⇐ 
                                                     ArePerspectiveAxe.perspective perspectiveAxe-Q0Q2 0♯1 
                                                   ⇒⟨ axeQ≈11' ⟩ )) 
                                 ⟩⇐ 
                                    meetₗ  
                                          ⇒⟨ join-comm ⟩
        persp (suc (suc (suc ())))



