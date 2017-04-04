{-# OPTIONS --no-eta-equality #-} 


open import Data.Empty
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-A {a b c d e}
       (PPD : Desarguesian a b c d e)  where


open Desarguesian PPD 
     renaming (projective to PP)

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP
open ProjectivePlane.EqReasoningInstances PP

open import ProjectivePlane.PropertiesGeneral PP 
open import  ProjectivePlane.Harmonic.Base PPD
open import ProjectivePlane.Harmonic.Lemmas PPD
open import ProjectivePlane.Harmonic.Uniqueness.MBase PPD

          
absurdity      
    : (A B C : Point)
    → (A♯B   : A ♯ B)
    → (C∈AB  : C ∈ join A♯B) 
    → (HC HC' : HarmonicConf C∈AB)
    → let
         open General A B C A♯B C∈AB HC HC'
         open HarmonicConf HC 
         -- module H' = HarmonicConf HC'
         open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
      in
       
        (D♯D' : D ♯ D')
        → (C♯A  : C ♯ A)
        → (C♯B  : C ♯ B)
        → (l♯l' : l ♯ l')
        → (R♯R' : R ♯ R')
        →  let
             open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
           in
              (R'∉RB : R' ∉ join R♯B)
              → (R'∉RA : R' ∉ join R♯A)
              → (SP♯S'P' : join S♯P ♯ join S'♯P') 
              → (SQ♯S'Q' :  join S♯Q ♯ join S'♯Q') 
              → (O∉RS : O ∉ join R♯S)
              → (O∉R'S' : O ∉ join H'.R♯S)
              → (S♯S' : S ♯ S')
      → ⊥

absurdity A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∉RA SP♯S'P' SQ♯S'Q' O∉RS O∉R'S' S♯S'
         = D≈D' D♯D'
 where
  open General A B C A♯B C∈AB HC HC'
  open HarmonicConf HC 
  
  open H' using ()
          renaming (l to l'; R to R';  D to D';
                    P to P'; Q to Q'; S to S')
  open import ProjectivePlane.CompleteNPoint PP
  open import ProjectivePlane.CompleteNPoint.Triangle PP 
  open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP as TP
  open import Data.Fin
  open import Data.Fin.Setoid

  open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
  open Case₁-R'∉RB R'∉RB
  open PerspectivePQR R'∉RA 
       using ( RB♯P'R'
             ; perspectiveCenter-PQR
             ; O∈RR'
             )

  open PerspectivePQS R'∉RA SP♯S'P' SQ♯S'Q' S♯S'
       using (perspectiveCenter-PQS)
  
  O∈SS' : O ∈ join S♯S'
  O∈SS' = ⟨ unq-meet _ meetₗ meetᵣ ⟩⇐ ArePerspectiveCenter.perspective perspectiveCenter-PQS  `2

  tPRS  = triangle→Poly $ isT2T PRS
  t'PRS = triangle→Poly $ isT2T HC'-4-6.PRS
  perspectiveCenter-PRS : ArePerspectiveCenter tPRS t'PRS 
  perspectiveCenter-PRS = 
    toArePerspectiveCenter record
      { Center = O
      ; areDistinct = toAreDistinct areDistinct₁
      ; perspective = λ { zero → meetₗ
                        ; (suc zero) → O∈RR'
                        ; (suc (suc zero)) → O∈SS'
                        ; (suc (suc (suc ())))
                                              }
      ; O∉T-01 = ⟨  ≈meet ⟩⇐ 
                   ArePerspectiveCenter.Center-∉-T perspectiveCenter-PQR {i♯j = 0♯2} 
                 ⇒⟨ ≈join ⟩
      ; O∉T-02 = ⟨ ≈meet ⟩⇐  
                ArePerspectiveCenter.Center-∉-T perspectiveCenter-PQS {i♯j = 0♯2}  
                ⇒⟨ ≈join ⟩
      ; O∉T-12 = O∉RS
      ; O∉T'-01 = ⟨ ≈meet ⟩⇐ 
                  ArePerspectiveCenter.Center-∉-T' perspectiveCenter-PQR {i♯j = 0♯2} 
                ⇒⟨ ≈join ⟩
      ; O∉T'-02 = ⟨ ≈meet ⟩⇐  
                 ArePerspectiveCenter.Center-∉-T' perspectiveCenter-PQS {i♯j = 0♯2}  
                 ⇒⟨ ≈join ⟩
      ; O∉T'-12 = O∉R'S'
      }

       where
         areDistinct₁ : AreDistinct₁ tPRS t'PRS
         areDistinct₁ = record
                          { vrt-0 = P♯P'
                          ; vrt-1 = R♯R'
                          ; vrt-2 = S♯S'
                          ; sd-01 = ⟨  sym $ unq-join _ meetₗ joinₗ ⟩⇐ RB♯P'R' ⇒⟨ ≈join ⟩
                          ; sd-02 = ⟨  join-comm ⟩⇐ SP♯S'P' ⇒⟨ join-comm ⟩
                          ; sd-12 = RS♯R'S'
                          }

  perspectiveAxis-PRS :  ArePerspectiveAxis tPRS t'PRS
  perspectiveAxis-PRS = desargues _ _  perspectiveCenter-PRS

  module apa-PRS =  ArePerspectiveAxis perspectiveAxis-PRS 
  axisPRS≈AB : apa-PRS.axis  ≈ join A♯B
  axisPRS≈AB = unq-join _ (⟨ unq-meet _ (joinₗ ⇒⟨ unq-join _ joinᵣ meetₗ ⟩) (joinₗ ⇒⟨ unq-join _ joinᵣ meetₗ ⟩) 
                          ⟩⇐ apa-PRS.perspective 0♯2) 
                         (⟨ unq-meet _ (joinᵣ ⇒⟨ unq-join _ meetₗ  joinₗ ⟩) (joinᵣ ⇒⟨ unq-join _ meetₗ  joinₗ ⟩) 
                          ⟩⇐ apa-PRS.perspective 0♯1)


  D≈D' : D ≈ D'
  D≈D' = begin
         D             
            ≈⟨ sym $ unq-meet _ meetₗ ( apa-PRS.perspective 1♯2 ⇒⟨ axisPRS≈AB ⟩) ⟩
         meet (AreDistinct.sd♯ apa-PRS.areDistinct 1♯2)  
            ≈⟨ unq-meet _ meetᵣ ( apa-PRS.perspective 1♯2 ⇒⟨ axisPRS≈AB ⟩) ⟩
         D'
         ∎
 

   


