-- open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product hiding (swap)
open import Data.Nat
open import Level as L
open import Function hiding (_∋_)
open import Relation.Binary.Apartness
import Data.Nat 
open import Data.Fin
open import Data.Fin.Setoid
import Relation.Binary.EqReasoning as EqR

open import ProjectivePlane
import ProjectivePlane.CompleteNPoint
import ProjectivePlane.PropertiesGeneral
import ProjectivePlane.CompleteNPoint.Quadrangle
open import ProjectivePlane.Duality
import ProjectivePlane.CompleteNPoint.Triangle
import ProjectivePlane.PropertiesGeneral

module ProjectivePlane.Fano
        where


record IsFano {a b c d e}(PP : ProjectivePlane a b c d e ) : Set (L.suc e L.⊔ L.suc b L.⊔ L.suc a)  where

  open ProjectivePlane.ProjectivePlane PP
  open  ProjectivePlane.CompleteNPoint.Quadrangle PP
  open  ProjectivePlane.CompleteNPoint.Triangle PP
  open  ProjectivePlane.PropertiesGeneral PP


  field
    fano :  ∀ (Q : Quadrangle) → diag₁ Q ∉ join (diag₂♯diag₃ Q) 

  diag123 : ∀ Q → IsTriangle (diag₁ Q) (diag₂ Q) (diag₃ Q)
  diag123 Q = Min→Triangle (record { B♯C = diag₂♯diag₃ Q ; A∉BC = fano Q })

  fano-b : ∀ (Q : Quadrangle) → diag₃ Q ∉ join (diag₁♯diag₂ Q)
  fano-b Q = (IsTriangle.C∉AB  (diag123 Q))  ⇒⟨ ≈join ⟩
           where open Rel♯ Outside
         

record FanoProjectivePlane  a b c d e : Set (L.suc a L.⊔ L.suc b L.⊔ L.suc c L.⊔  L.suc d L.⊔ L.suc e) where
  field 
    projective : ProjectivePlane a b c d e
    isFano : IsFano projective
  open ProjectivePlane.ProjectivePlane projective public
  open IsFano isFano public



 
dualityFano : ∀ {a b c d e} 
              → (PP : ProjectivePlane a b c d e) → IsFano PP → IsFano (dual PP)
dualityFano PP fanoPP =  record { fano = fano-dual } 
  where

    module P* = ProjectivePlane.ProjectivePlane (dual PP)
    module Pol* = ProjectivePlane.CompleteNPoint (dual PP)
    open ProjectivePlane.CompleteNPoint PP
    open   ProjectivePlane.CompleteNPoint.Quadrangle PP
    module Q* = ProjectivePlane.CompleteNPoint.Quadrangle (dual PP)
    open ProjectivePlane.Duality.Lemmas PP
    open ProjectivePlane.PropertiesGeneral PP
    open ProjectivePlane.CompleteNPoint.Triangle PP
    module T* = ProjectivePlane.CompleteNPoint.Triangle (dual PP)
    open ProjectivePlane.ProjectivePlane PP
    open ProjectivePlane.Setoid♯Instances PP
    open ProjectivePlane.Rel♯Instances PP
    module fPP =  IsFano fanoPP

    fano-dual : ∀ (Q : Q*.Quadrangle)
                → (meet $ Q*.diag₂♯diag₃  Q) ∉ (Q*.diag₁  Q) 

    fano-dual Q =  ⟨ meet-comm ⟩⇐  T*.IsTriangle.B∉AC triangle-d₃₁₂  

       where

        -- some convenient abrebriations
         edge* = Pol*.Complete-N-Point.edge
         _∉*_  = P*._∉_
         _$⋆_ = Pol*._$∙_



         triangle-ABC : (Q : Q*.Quadrangle ) → IsTriangle (edge* Q 0♯1) (edge* Q 1♯2) (edge* Q 2♯3)
         triangle-ABC Q = Min→Triangle  record { B♯C =  Pol*.sides♯  Q 1♯2 1♯3 
                                               ; A∉BC =  (Pol*.nonc3 Q (symmetry  0♯2) 0♯1 (symmetry 1♯2)) 
                                                         ⇒⟨ join-meetᵣₗ  ⟩                                                            
                                               }
                                                   


         -- generalizing previous function 
         getTriangle : (Q : Q*.Quadrangle) → 
                       {n₀ n₁ n₂ n₃ : Fin 4} →
                       (n01 : n₀ ♯ n₁) →
                       (n02 : n₀ ♯ n₂)
                       (n12 : n₁ ♯ n₂) →
                       (n23 : n₂ ♯ n₃) →
                       (n13 : n₁ ♯ n₃) →
                       IsTriangle (edge* Q n01) (edge* Q n12) (edge* Q n23)
         getTriangle Q {n₂ = n₂} n01 n02 n12 n23 n13 = 
           Min→Triangle (record { 
                            B♯C = B♯C ; 
                            A∉BC = (Pol*.nonc3 Q (symmetry n02) n01 (symmetry n12))
                                   ⇒⟨ join-meetᵣₗ ⟩
                        })
                 where B♯C = Pol*.sides♯  Q n12 n13 



         A B C D : Point
         A = Pol*.Complete-N-Point.edge Q 0♯1
         B = Pol*.Complete-N-Point.edge Q 1♯2
         C = Pol*.Complete-N-Point.edge Q 2♯3
         D = Pol*.Complete-N-Point.edge Q (symmetry 0♯3)

         A≈A : A ≈ A
         A≈A = Setoid♯.refl Point♯ 
        
         B♯C : B ♯ C
         B♯C = Pol*.sides♯  Q 1♯2 1♯3


         isQMin-ABCD : IsQuadrangleMin  A B C D
         isQMin-ABCD = 
           record { ABC = triangle-ABC Q
                  ; ABD = let
                              BAD = triangle-ABC $ Pol*.subComplete-N-Point (swap `0 `2 IdInjectiveFun♯) Q 
                          in Min→Triangle (record { B♯C  = ⟨ meet-comm ⟩⇐ IsTriangle.A♯C BAD ⇒⟨ meet-comm ⟩  
                                                  ; A∉BC = ⟨ meet-comm ⟩⇐ IsTriangle.B∉AC BAD ⇒⟨ join-cong meet-comm meet-comm ⟩   
                                                  })
                                       
                  ; ACD = let CDA : IsTriangle C D A
                              CDA = getTriangle Q 2♯3 (symmetry 0♯2) (symmetry 0♯3) 0♯1 (symmetry 1♯3)
                          in Min→Triangle (record { B♯C = IsTriangle.A♯B CDA ; A∉BC = IsTriangle.C∉AB CDA })
                  ; BCD = getTriangle Q 1♯2 1♯3 2♯3 (symmetry 0♯3) (symmetry 0♯2)
           }

 

         Q' : Quadrangle
         Q' = isQMin→Q    isQMin-ABCD

         fanoQ' = IsFano.fano-b fanoPP  Q'
       
         D₁-Q'≈13-Q : diag₁  Q'  ≈ Pol*.edge Q 1♯3
         D₁-Q'≈13-Q = meet-cong  (sym join-meetᵣₗ) (sym join-meetᵣₗ) 

         D₂-Q'≈02-Q : diag₂ Q' ≈ Pol*.edge Q 0♯2
         D₂-Q'≈02-Q = meet-cong (sym join-meetₗᵣ) (sym join-meetₗᵣ)

         D₁Q'∈d₃Q : diag₁  Q' ∈ Q*.diag₃ Q
         D₁Q'∈d₃Q = ⟨ D₁-Q'≈13-Q ⟩⇐ joinᵣ 

         D₂Q'∈d₃Q : diag₂ Q' ∈ Q*.diag₃  Q
         D₂Q'∈d₃Q = ⟨ D₂-Q'≈02-Q ⟩⇐ joinₗ 

         D₁D₂Q'≈d₃Q : join (diag₁♯diag₂ Q') ≈ Q*.diag₃ Q  
         D₁D₂Q'≈d₃Q = sym $ unq-join ((diag₁♯diag₂ Q'))  D₁Q'∈d₃Q    D₂Q'∈d₃Q


         
         D₃-Q'≈d₁d₂Q :  diag₃ Q' ≈ meet  (Q*.diag₁♯diag₂ Q)
         D₃-Q'≈d₁d₂Q =  meet-cong  (join-cong ≈meet ≈meet)  (join-flip-cong meet-comm meet-comm)


         d₁d₂Q'∉d₃-Q : meet  (Q*.diag₁♯diag₂  Q) ∉ Q*.diag₃  Q
         d₁d₂Q'∉d₃-Q = ⟨  sym D₃-Q'≈d₁d₂Q ⟩⇐ fPP.fano-b Q'  ⇒⟨  D₁D₂Q'≈d₃Q ⟩

         triangle-d₃₁₂ : T*.IsTriangle (Q*.diag₃   Q)  (Q*.diag₁ Q) (Q*.diag₂ Q)
         triangle-d₃₁₂ = 
                 T*.Min→Triangle 
                         (record { B♯C = Q*.diag₁♯diag₂ Q 
                                 ; A∉BC = d₁d₂Q'∉d₃-Q 
                                 }
                         )

dualFano : ∀ {a b c d e} 
           → FanoProjectivePlane a b c d e → FanoProjectivePlane  c d a b e
dualFano FPP = let open FanoProjectivePlane FPP
               in record { projective = dual projective ; 
                           isFano = dualityFano projective isFano }


