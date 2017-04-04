open import Data.Empty
open import Relation.Nullary
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-B {a b c d e}
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
         open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
      in
       
        (D♯D' : D ♯ D')
        → (C♯A  : C ♯ A)
        → (C♯B  : C ♯ B)
        → (l♯l' : l ♯ l')
        → (R♯R' : R ≈ R')
        → ⊥

absurdity  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R≈R' 


    =  D≈D' D♯D' 
       where
         open General A B C A♯B C∈AB HC HC'
         open Case₀ D♯D' C♯A C♯B l♯l'
         open HarmonicConf HC 
         open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')

         open import ProjectivePlane.CompleteNPoint.Triangle PP

         tPQS  = triangle→Poly $ isT2T PQS
         t'PQS = triangle→Poly $ isT2T HC'-4-6.PQS

         Q'∉SQ :  Q' ∉ join S♯Q
         Q'∉SQ = C7-b (symmetry Q♯Q') (symmetry (IsTriangle.AC♯AB QRS) ⇒⟨ join-comm ⟩) joinₗ joinᵣ 
                      ( meetₗ ⇒⟨ join-cong (sym R≈R') refl  -∘- -QRA-.BC≈AB -∘- ≈join ⟩)

         SQ♯S'Q' : join S♯Q ♯ join HC'-4-6.S♯Q
         SQ♯S'Q' = symmetry (C5 joinᵣ Q'∉SQ)

         S'∉SQ : S' ∉ join S♯Q
         S'∉SQ = C7-b (symmetry HC'-4-6.B♯S) (symmetry SQ♯S'Q') HC'-4-6.-SBQ-.B∈AC -SBQ-.B∈AC joinₗ

         S♯S' : S ♯ S'
         S♯S' = symmetry $ C0 S'∉SQ joinₗ 

         P∉AP' : P ∉ join H'.A♯P
         P∉AP' = C7-b P♯P' (symmetry H'.AP♯RB) meetₗ joinᵣ (meetₗ ⇒⟨ join-cong R≈R' refl ⟩)

         open import ProjectivePlane.CompleteNPoint PP
         open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP
         open import Data.Fin

         perspectiveAxis :  ArePerspectiveAxis tPQS t'PQS 
         perspectiveAxis 
           = toPerspectiveAxis 
             (record
                { axis = join A♯B
                ; areDistinct 
                    = toAreDistinct 
                      (record
                         { vrt-0 = P♯P'
                         ; vrt-1 = Q♯Q'
                         ; vrt-2 = S♯S'
                         ; sd-01 =  ⟨ sym $ unq-join _ meetᵣ meetᵣ ⟩⇐ l♯l' ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩
                         ; sd-02 = C5 joinₗ (P∉AP' ⇒⟨ HC'-4-6.-SAP-.BC≈AC -∘- join-comm ⟩)  
                         ; sd-12 =  ⟨ join-comm  ⟩⇐ SQ♯S'Q' ⇒⟨ join-comm ⟩
                         })
                ; axis-∉-T =  λ {i} → Ti∉AB i
                ; axis-∉-T' = λ {i} → T'i∉AB i
                ; persp01 =  ⟨ begin  _        ≈⟨ meet-cong (sym (unq-join _ meetᵣ meetᵣ)) (sym (unq-join _ meetᵣ meetᵣ)) ⟩
                                     meet l♯l' ≈⟨ sym (unq-meet _ C∈l  H'.C∈l) ⟩ 
                                     C 
                               ∎ 
                             ⟩⇐ C∈AB
                ; persp02 =  ⟨ sym (unq-meet _ (-SAP-.B∈AC ⇒⟨ join-comm ⟩) (HC'-4-6.-SAP-.B∈AC ⇒⟨ join-comm ⟩)) ⟩⇐ joinₗ
                ; persp12 =  ⟨ sym (unq-meet _ (-SBQ-.B∈AC ⇒⟨ join-comm ⟩) (HC'-4-6.-SBQ-.B∈AC ⇒⟨ join-comm ⟩)) ⟩⇐ joinᵣ
                })
                where Ti∉AB : ∀ i → tPQS  $∙ i ∉ join A♯B
                      Ti∉AB zero = P∉AB
                      Ti∉AB (suc zero) = Q∉AB
                      Ti∉AB (suc (suc zero)) = S∉AB
                      Ti∉AB (suc (suc (suc ())))

                      T'i∉AB : ∀ i → t'PQS  $∙ i ∉ join A♯B
                      T'i∉AB zero = HC'-4-6.P∉AB
                      T'i∉AB (suc zero) = HC'-4-6.Q∉AB
                      T'i∉AB (suc (suc zero)) = HC'-4-6.S∉AB
                      T'i∉AB (suc (suc (suc ())))


         perspectiveCenter : ArePerspectiveCenter tPQS t'PQS
         perspectiveCenter = desargues← _ _ perspectiveAxis

         module pc = ArePerspectiveCenter  perspectiveCenter

         
         R∈QQ' : R ∈ join Q♯Q'
         R∈QQ' = -QRA-.B∈AC ⇒⟨ unq-join _ joinₗ ( meetₗ ⇒⟨  join-cong (sym R≈R') refl -∘- -QRA-.BC≈AC ⟩) ⟩ 

         R∈PP' : R ∈ join P♯P'
         R∈PP' =  -PRB-.B∈AC ⇒⟨ unq-join _ joinₗ ( meetₗ ⇒⟨  join-cong (sym R≈R') refl -∘- -PRB-.BC≈AC ⟩) ⟩ 
         
         R≈Center : R ≈ pc.Center
         R≈Center = unq-meet _ R∈PP' R∈QQ'

         R∈SS' : R ∈ join S♯S'
         R∈SS' =  ⟨ R≈Center ⟩⇐ pc.perspective `2 

         RS≈R'S' : join R♯S ≈ join H'.R♯S
         RS≈R'S' = begin
                    join R♯S ≈⟨ sym (unq-join _ R∈SS' joinₗ) ⟩
                    join S♯S' ≈⟨ unq-join _ (⟨ sym R≈R' ⟩⇐ R∈SS') joinᵣ ⟩
                    join H'.R♯S
                   ∎

         D≈D' : D ≈ D'
         D≈D' = meet-cong RS≈R'S' refl
