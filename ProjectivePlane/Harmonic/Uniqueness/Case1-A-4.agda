open import Data.Empty
open import Relation.Nullary
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-A-4 {a b c d e}
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


module Lemmas-0 
    (A B C : Point)
    (A♯B   : A ♯ B)
    (C∈AB  : C ∈ join A♯B) 
    (HC HC' : HarmonicConf C∈AB)
    where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
    open H' using ()
            renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
    module A
        (D♯D' : D ♯ D')
        (C♯A  : C ♯ A)
        (C♯B  : C ♯ B)
        (l♯l' : l ♯ l')
        (R♯R' : R ♯ R')
        (R'∉RB : R' ∉ join R♯B)
        (R'∈RA : R' ∈ join R♯A)

      where
        open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
        module -R'RA- =  lemma-3-collinear (symmetry R♯R')  R♯A H'.R♯A  R'∈RA
    
    
        RA≈R'A : join R♯A ≈ join H'.R♯A
        RA≈R'A = unq-join _ R'∈RA joinᵣ
    
    
        Q∉BQ' : Q ∉ join H'.B♯Q
        Q∉BQ' = C7-b Q♯Q' (symmetry H'.BQ♯RA) meetₗ joinᵣ (meetₗ ⇒⟨ RA≈R'A ⟩)
                    
    
        BQ♯BQ' : join B♯Q ♯ join H'.B♯Q
        BQ♯BQ' = C5 joinᵣ Q∉BQ'
    
        S∉BQ'  :  S ∉ join H'.B♯Q
        S∉BQ' = C7-b (symmetry B♯S) BQ♯BQ' joinₗ joinₗ meetᵣ
    
        S'∉BQ  :  S' ∉ join B♯Q
        S'∉BQ = C7-b (symmetry HC'-4-6.B♯S) (symmetry BQ♯BQ') joinₗ joinₗ meetᵣ
      
    
        S♯S' : S ♯ S'
        S♯S' = C0 S∉BQ' meetᵣ


module Lemmas-1 
    (A B C : Point)
    (A♯B   : A ♯ B)
    (C∈AB  : C ∈ join A♯B) 
    (HC HC' : HarmonicConf C∈AB)
    where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
    open H' using ()
            renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
    
    module A
      (D♯D' : D ♯ D')
      (C♯A  : C ♯ A)
      (C♯B  : C ♯ B)
      (l♯l' : l ♯ l')
      (R♯R' : R ♯ R') where

      open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
      module B 
       (R'∉RB : R' ∉ join R♯B)
       (R'∈RA : R' ∈ join R♯A) 
       (S'∈AS : S' ∈ join A♯S)  where

       open Lemmas-0.A  _ _ _ _  _ HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA 


       module -S'AS- =  lemma-3-collinear (symmetry HC'-4-6.A♯S)  A♯S (symmetry S♯S')   S'∈AS

       AS≈AS' : join A♯S ≈ join HC'-4-6.A♯S
       AS≈AS' = begin
                join A♯S         ≈⟨ -S'AS-.BC≈AB ⟩     
                _                ≈⟨ join-comm  ⟩
                join HC'-4-6.A♯S 
                ∎
       AS≈SS' : join A♯S ≈ join S♯S'
       AS≈SS' = begin
                join A♯S  ≈⟨ -S'AS-.BC≈AC ⟩
                _         ≈⟨ join-comm ⟩
                join S♯S' ∎

       AP'≈AP :  join H'.A♯P ≈ join A♯P
       AP'≈AP = begin
                join H'.A♯P      ≈⟨ HC'-4-6.-SAP-.BC≈AB ⇒⟨ join-comm ⟩ ⟩ 
                join HC'-4-6.A♯S ≈⟨ sym $ unq-join _ joinₗ S'∈AS ⟩
                join A♯S         ≈⟨ sym (-SAP-.BC≈AB ⇒⟨ join-comm ⟩) ⟩
                join A♯P
            ∎

module Lemmas-2 
    (A B C : Point)
    (A♯B   : A ♯ B)
    (C∈AB  : C ∈ join A♯B) 
    (HC HC' : HarmonicConf C∈AB)
    where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
    open H' using ()
            renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
    
    module A
      (D♯D' : D ♯ D')
      (C♯A  : C ♯ A)
      (C♯B  : C ♯ B)
      (l♯l' : l ♯ l')
      (R♯R' : R ♯ R') where

      open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
      module B 
       (R'∉RB : R' ∉ join R♯B)
       (R'∈RA : R' ∈ join R♯A) 
       (S'∈AS : S' ∈ join A♯S)  
       (Q'∉PR : Q' ∉ join P♯R ) where

        open Lemmas-0.A  _ _ _ _  _ 
                       HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA

        open import ProjectivePlane.CompleteNPoint.Triangle PP 
        open import ProjectivePlane.CompleteNPoint
        open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP
        tPQR  = triangle→Poly $ isT2T PQR
        -- t'PQR = triangle→Poly $ isT2T HC'-4-6.PQR
        
        Q'P'S' : IsTriangle Q' P' S'
        Q'P'S' =  Min→Triangle (record { B♯C = symmetry HC'-4-6.S♯P 
                                       ; A∉BC = IsTriangle.B∉AC HC'-4-6.PQS ⇒⟨ ≈join ⟩ })

        t'QPS =  triangle→Poly $ isT2T Q'P'S'

        AP'≈AP :  join H'.A♯P ≈ join A♯P
        AP'≈AP = begin
                 join H'.A♯P      ≈⟨ HC'-4-6.-SAP-.BC≈AB ⇒⟨ join-comm ⟩ ⟩ 
                 join HC'-4-6.A♯S ≈⟨ sym $ unq-join _ joinₗ S'∈AS ⟩
                 join A♯S         ≈⟨ sym (-SAP-.BC≈AB ⇒⟨ join-comm ⟩) ⟩
                 join A♯P
                 ∎

        perspectiveAxis : ArePerspectiveAxis tPQR t'QPS
        perspectiveAxis 
          = toPerspectiveAxis 
            (record
               { axis = join A♯B
               ; areDistinct 
                 = toAreDistinct 
                   (record
                     { vrt-0 = C0 (C7-b P♯C l♯l' C∈l H'.C∈l meetᵣ) meetᵣ
                     ; vrt-1 = symmetry (C0 (C7-b HC'-4-6.P♯C (symmetry l♯l') H'.C∈l C∈l meetᵣ) meetᵣ)
                     ; vrt-2 = C0 (C7-b R♯A (symmetry AP♯RA)  joinᵣ joinₗ joinₗ) (meetₗ ⇒⟨ AP'≈AP ⟩)
                     ; sd-01 =  ⟨ sym (unq-join _ meetᵣ meetᵣ) ⟩⇐ l♯l' ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩
                     ; sd-02 = symmetry (C5 joinₗ (Q'∉PR ⇒⟨ ≈join ⟩))
                     ; sd-12 =  ⟨ sym -QRA-.BC≈AB  ⟩⇐  symmetry AP♯RA 
                                ⇒⟨ begin join A♯P  ≈⟨  sym AP'≈AP ⟩ 
                                          join H'.A♯P ≈⟨ HC'-4-6.-SAP-.BC≈AC  -∘- join-comm   ⟩ 
                                          edge  t'QPS  1♯2 
                                    ∎ ⟩
                                    })
               ; axis-∉-T  = λ {i} → tPQR-∉-AB i
               ; axis-∉-T' = λ {i} → t'QPS-∉-AB i
               ; persp01 =   ⟨ sym (unq-meet _ (C∈l ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩) (H'.C∈l ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩)) ⟩⇐ C∈AB
               ; persp02 =  ⟨ sym (unq-meet _ (-PRB-.C∈AB ⇒⟨ ≈join ⟩) ( HC'-4-6.-SBQ-.B∈AC ⇒⟨ join-comm ⟩ )) ⟩⇐ joinᵣ 
               ; persp12 =  ⟨ sym (unq-meet _  -QRA-.C∈AB  (HC'-4-6.-SAP-.B∈AC ⇒⟨ join-comm ⟩)) ⟩⇐ joinₗ
               })

               where 
                     open import Data.Fin
                     tPQR-∉-AB : ∀ i → (tPQR $∙ i) ∉ join A♯B
                     tPQR-∉-AB zero = P∉AB
                     tPQR-∉-AB (suc zero) = Q∉AB
                     tPQR-∉-AB (suc (suc zero)) = R∉AB
                     tPQR-∉-AB (suc (suc (suc ())))

                     
                     t'QPS-∉-AB : ∀ i → (t'QPS $∙ i) ∉ join A♯B
                     t'QPS-∉-AB zero = HC'-4-6.Q∉AB
                     t'QPS-∉-AB (suc zero) = HC'-4-6.P∉AB
                     t'QPS-∉-AB (suc (suc zero)) = HC'-4-6.S∉AB
                     t'QPS-∉-AB (suc (suc (suc ())))


        pc-tPQR-t'QPS :  ArePerspectiveCenter tPQR t'QPS
        pc-tPQR-t'QPS = desargues← _ _ perspectiveAxis

        -- center
        U = ArePerspectiveCenter.Center pc-tPQR-t'QPS

 
module Lemmas-3 
    (A B C : Point)
    (A♯B   : A ♯ B)
    (C∈AB  : C ∈ join A♯B) 
    (HC HC' : HarmonicConf C∈AB)
    where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
    open H' using ()
            renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
    
    module A
      (D♯D' : D ♯ D')
      (C♯A  : C ♯ A)
      (C♯B  : C ♯ B)
      (l♯l' : l ♯ l')
      (R♯R' : R ♯ R') where

      open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
      module B 
       (R'∉RB : R' ∉ join R♯B)
       (R'∈RA : R' ∈ join R♯A) 
       (S'∈AS : S' ∈ join A♯S)  
       (Q'∉PR : Q' ∉ join P♯R )
       (Q∈P'R' : Q ∈ join H'.P♯R) where

         open Lemmas-0.A  _ _ _ _  _ 
                       HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA

         open Lemmas-1.A.B  _ _ _ _  _ 
                       HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA S'∈AS

         open Lemmas-2.A.B  _ _ _ _ _ HC HC'
                           D♯D' C♯A C♯B l♯l' R♯R' R'∉RB R'∈RA S'∈AS Q'∉PR

         open import ProjectivePlane.CompleteNPoint.Triangle PP
         R'≈Q : R' ≈ Q
         R'≈Q = begin
                 R'     ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
                 meet (IsTriangle.AC♯BC HC'-4-6.PQR)  ≈⟨ sym (unq-meet _ (Q∈P'R' ⇒⟨ ≈join ⟩) ( meetₗ  ⇒⟨ trans RA≈R'A HC'-4-6.-QRA-.BC≈AB ⟩)) ⟩ 
                 Q
                ∎

         R'B≈BQ : join H'.R♯B ≈ join B♯Q
         R'B≈BQ = join-flip-cong R'≈Q refl

         SA'≈PS : join (symmetry HC'-4-6.A♯S) ≈ join (symmetry S♯P)
         SA'≈PS = begin
                  join (symmetry HC'-4-6.A♯S) ≈⟨ sym -S'AS-.BC≈AB ⟩
                  join  A♯S                    ≈⟨  ⟨ join-comm ⟩⇐ sym -SAP-.AC≈AB ⇒⟨ join-comm ⟩ ⟩
                  join (symmetry S♯P)
                  ∎

         S≈P' : S ≈ P'
         S≈P' = begin
                S    ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
                meet (IsTriangle.AC♯BC PQS) ≈⟨ sym (unq-meet _ (HC'-4-6.-SAP-.C∈AB  ⇒⟨ SA'≈PS ⇒⟨ ≈join ⟩ ⟩) ( meetₗ  ⇒⟨ trans R'B≈BQ (trans -SBQ-.BC≈AC join-comm) ⟩)) ⟩
                P'
                ∎


         tPRS  = triangle→Poly $ isT2T PRS
         QSR'  : IsTriangle Q' S' R'
         QSR' =  Min→Triangle (record { B♯C = (symmetry H'.R♯S) ; A∉BC = HC'-4-6.Q∉RS ⇒⟨ join-comm ⟩ })
         t'QSR = triangle→Poly $ isT2T QSR'

         open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP

         module  APC-tPQR-t'QPS = ArePerspectiveCenter pc-tPQR-t'QPS


         SP♯QR : join S♯P ♯ join Q♯R
         SP♯QR = C5 joinᵣ P∉QR

         QR≈Q'R' : join Q♯R ≈ join H'.Q♯R
         QR≈Q'R' = begin
                   join Q♯R     ≈⟨ sym -QRA-.BC≈AB ⟩
                   join R♯A     ≈⟨ RA≈R'A ⟩
                   join H'.R♯A  ≈⟨ HC'-4-6.-QRA-.BC≈AB ⟩
                   join H'.Q♯R
                   ∎

         S'P'≈SP : join HC'-4-6.S♯P ≈ join S♯P
         S'P'≈SP = begin
                   join HC'-4-6.S♯P  ≈⟨ trans HC'-4-6.-SAP-.AC≈AB join-comm ⟩  
                   join HC'-4-6.A♯S  ≈⟨ sym-join ⟩  _  ≈⟨ SA'≈PS ⟩ _  ≈⟨ join-comm ⟩
                   join S♯P
                   ∎


         open import Data.Fin

         pc-tPRS-t'QSR : ArePerspectiveCenter tPRS t'QSR
         pc-tPRS-t'QSR 
          = toArePerspectiveCenter 
            (record
               { Center = U
               ; areDistinct 
                  = toAreDistinct 
                    (record
                       { vrt-0 = AreDistinct.vrt♯ APC-tPQR-t'QPS.areDistinct `0
                       ; vrt-1 = AreDistinct.vrt♯ APC-tPQR-t'QPS.areDistinct `2
                       ; vrt-2 = S♯Q ⇒⟨ sym R'≈Q ⟩
                       ; sd-01 =  ⟨ ≈join ⟩⇐ AreDistinct.sd♯ APC-tPQR-t'QPS.areDistinct 0♯2 ⇒⟨  ≈join ⟩ 
                       ; sd-02 =  ⟨ join-comm ⟩⇐ SP♯QR ⇒⟨ QR≈Q'R' ⇒⟨ ≈join ⟩ ⟩  --PS♯Q'R'
                       ; sd-12 =  C5 joinₗ (C7-b R♯R' ( IsTriangle.AC♯BC QSR') joinᵣ joinᵣ 
                                                 (joinₗ ⇒⟨ begin _  ≈⟨ RA≈R'A ⟩  
                                                                 _  ≈⟨ HC'-4-6.-QRA-.BC≈AB ⟩ 
                                                                 _  ≈⟨ ≈join ⟩ _ ∎ ⟩) )
                       })
               ; perspective = λ { zero → APC-tPQR-t'QPS.perspective `0 
                                 ; (suc zero) → APC-tPQR-t'QPS.perspective `2 
                                 ; (suc (suc zero)) → APC-tPQR-t'QPS.perspective `1 ⇒⟨ join-flip-cong ( sym R'≈Q) (sym S≈P') ⟩ 
                                 ; (suc (suc (suc ())))}
               ; O∉T-01 = APC-tPQR-t'QPS.Center-∉-T {i♯j = 0♯2} ⇒⟨ ≈join ⟩ 
               ; O∉T-02 =  APC-tPQR-t'QPS.Center-∉-T' {i♯j = 1♯2} ⇒⟨  join-comm  -∘- S'P'≈SP -∘- join-comm ⟩  
                                                                           
                                                                
               ; O∉T-12 = C7-b (C0 (APC-tPQR-t'QPS.Center-∉-T' {i♯j = 1♯2}) joinₗ   )
                               (IsTriangle.AC♯BC QRS) (⟨ sym S≈P' ⟩⇐  joinᵣ)  (⟨ sym S≈P' ⟩⇐ joinᵣ) (APC-tPQR-t'QPS.perspective `1 ⇒⟨ join-cong refl ( sym S≈P') ⟩)
               ; O∉T'-01 =  APC-tPQR-t'QPS.Center-∉-T' {i♯j = 0♯2} ⇒⟨  ≈join ⟩
               ; O∉T'-02 = APC-tPQR-t'QPS.Center-∉-T {i♯j = 1♯2} ⇒⟨  QR≈Q'R' -∘- ≈join ⟩ 
               ; O∉T'-12 = C7-b (C0 (APC-tPQR-t'QPS.Center-∉-T {i♯j = 1♯2}) joinₗ) 
                                (IsTriangle.AB♯BC HC'-4-6.PRS ⇒⟨ join-comm ⟩) ( ⟨ sym R'≈Q ⟩⇐ joinᵣ ) ( ⟨ sym R'≈Q ⟩⇐ joinᵣ)
                                (APC-tPQR-t'QPS.perspective  `1 ⇒⟨ join-flip-cong (sym R'≈Q) refl ⟩)
               }) 


         pa-tPRS-t'QSR  : ArePerspectiveAxis tPRS t'QSR
         pa-tPRS-t'QSR = desargues _ _ pc-tPRS-t'QSR


         module apa  =  ArePerspectiveAxis pa-tPRS-t'QSR


         A≈apa02 :  A ≈  meet (AreDistinct.sd♯ apa.areDistinct  0♯2)
         A≈apa02 = unq-meet _ (-SAP-.B∈AC ⇒⟨ join-comm ⟩) (HC'-4-6.-QRA-.C∈AB ⇒⟨ ≈join ⟩)


         B≈apa01 :  B ≈  meet (AreDistinct.sd♯ apa.areDistinct  0♯1)
         B≈apa01 = unq-meet _  (-PRB-.C∈AB ⇒⟨ ≈join ⟩) (HC'-4-6.-SBQ-.B∈AC ⇒⟨ join-comm ⟩)

         axis≈AB : apa.axis  ≈ join A♯B
         axis≈AB = unq-join _ (⟨ A≈apa02 ⟩⇐ apa.perspective 0♯2) (⟨ B≈apa01 ⟩⇐ apa.perspective 0♯1)


         D≈D' : D ≈ D'
         D≈D' = begin
                     D             
                       ≈⟨ sym $ unq-meet _ meetₗ ( apa.perspective 1♯2 ⇒⟨ axis≈AB ⟩) ⟩
                     meet (AreDistinct.sd♯ apa.areDistinct 1♯2)  
                       ≈⟨ unq-meet _ (meetᵣ ⇒⟨ join-comm ⟩) ( apa.perspective 1♯2  ⇒⟨ axis≈AB ⟩) ⟩
                     D' 
                ∎




absurdity₁     
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
        → (R♯R' : R ♯ R')
        →  let
             open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
           in
              (R'∉RB : R' ∉ join R♯B)
              → (R'∈RA : R' ∈ join R♯A)
              → (S'∈AS : S' ∈ join A♯S)
              → (Q'∉PR : Q' ∉ join P♯R)
              → (Q∉P'R' : Q ∉ join H'.P♯R)

      → ⊥

absurdity₁  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∈RA 
          S'∈AS
          Q'∉PR
          Q∉P'R'
            =  D≈D' D♯D' 
   where
        open General A B C A♯B C∈AB HC HC'
        open HarmonicConf HC 
        open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
        open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
        open Lemmas-0.A  _ _ _ _  _ 
                       HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA

        open Lemmas-1.A.B  _ _ _ _  _ 
                       HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA S'∈AS

        open Lemmas-2.A.B  _ _ _ _ _ HC HC'
                           D♯D' C♯A C♯B l♯l' R♯R' R'∉RB R'∈RA S'∈AS Q'∉PR

        module Lemmas-2-HC'-HC 
                =   Lemmas-2.A.B  _ _ _ _ _ HC' HC
                       (symmetry D♯D') C♯A C♯B (symmetry l♯l') (symmetry R♯R') 
                       (lemma-triangle.B∉AC R'∉RB ⇒⟨ ≈join ⟩) -R'RA-.B∈AC (-S'AS-.C∈AB ⇒⟨ join-comm ⟩ )  Q∉P'R'

        t'PQR = Lemmas-2-HC'-HC.tPQR 
                       

        tQPS = Lemmas-2-HC'-HC.t'QPS
                       

        open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP
 
        pc-PQR'-QPS : ArePerspectiveCenter t'PQR tQPS
        pc-PQR'-QPS = Lemmas-2-HC'-HC.pc-tPQR-t'QPS
                       
        -- center
        W = ArePerspectiveCenter.Center pc-PQR'-QPS

        W≈U : W ≈ U
        W≈U =   unq-meet _ (ArePerspectiveCenter.perspective pc-PQR'-QPS `1 ⇒⟨ join-comm ⟩) 
                           (ArePerspectiveCenter.perspective pc-PQR'-QPS `0 ⇒⟨ join-comm ⟩)
                    

 

        open import ProjectivePlane.CompleteNPoint.Triangle PP
        tPRS  = triangle→Poly $ isT2T PRS
        QSR'  : IsTriangle Q' S' R'
        QSR' =  Min→Triangle (record { B♯C = (symmetry H'.R♯S) ; A∉BC = HC'-4-6.Q∉RS ⇒⟨ join-comm ⟩ })
        t'QSR = triangle→Poly $ isT2T QSR'


        pc-tPRS-t'QSR : ArePerspectiveCenter tPRS t'QSR
        pc-tPRS-t'QSR 
          = toArePerspectiveCenter 
            (record
               { Center = W
               ; areDistinct 
                 = toAreDistinct 
                   (record
                      { vrt-0 = AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) `0
                      ; vrt-1 = AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) `2
                      ; vrt-2 =  symmetry $ AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-PQR'-QPS) `2
                      ; sd-01 =  ⟨ ≈join ⟩⇐ AreDistinct.sd♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) 0♯2 ⇒⟨ ≈join ⟩
                      ; sd-02 = ⟨ ≈join ⟩⇐ symmetry (AreDistinct.sd♯ (ArePerspectiveCenter.areDistinct  pc-PQR'-QPS) 1♯2) ⇒⟨ ≈join ⟩
                      ; sd-12 = C5 joinₗ (C7-b R♯R' ( IsTriangle.AC♯BC QSR') joinᵣ joinᵣ (joinₗ ⇒⟨ trans RA≈R'A (HC'-4-6.-QRA-.BC≈AB ⇒⟨ ≈join ⟩) ⟩))
                      })
               ; perspective = persp
               ; O∉T-01 = ⟨ W≈U ⟩⇐ ArePerspectiveCenter.Center-∉-T  pc-tPQR-t'QPS {i♯j = 0♯2} ⇒⟨ ≈join ⟩
               ; O∉T-02 = ArePerspectiveCenter.Center-∉-T'  pc-PQR'-QPS {i♯j = 1♯2} ⇒⟨ ≈join ⟩
               ; O∉T-12 = W∉RS
               ; O∉T'-01 = ⟨ W≈U ⟩⇐ ArePerspectiveCenter.Center-∉-T'  pc-tPQR-t'QPS {i♯j = 0♯2} ⇒⟨ ≈join ⟩
               ; O∉T'-02 = ArePerspectiveCenter.Center-∉-T  pc-PQR'-QPS {i♯j = 1♯2} ⇒⟨ ≈join ⟩
               ; O∉T'-12 = W∉R'S' ⇒⟨ join-comm ⟩
               })

              where
                distinct : AreDistinct tPRS t'QSR
                distinct = toAreDistinct 
                   (record
                      { vrt-0 = AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) `0
                      ; vrt-1 = AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) `2
                      ; vrt-2 =  symmetry $ AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-PQR'-QPS) `2
                      ; sd-01 =  ⟨ ≈join ⟩⇐ AreDistinct.sd♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) 0♯2 ⇒⟨ ≈join ⟩
                      ; sd-02 = ⟨ ≈join ⟩⇐ symmetry (AreDistinct.sd♯ (ArePerspectiveCenter.areDistinct  pc-PQR'-QPS) 1♯2) ⇒⟨ ≈join ⟩
                      ; sd-12 = C5 joinₗ (C7-b R♯R' ( IsTriangle.AC♯BC QSR') joinᵣ joinᵣ (joinₗ ⇒⟨ trans RA≈R'A (HC'-4-6.-QRA-.BC≈AB ⇒⟨ ≈join ⟩) ⟩))
                      })
                open import Data.Fin
                persp : ∀ i → W ∈ join (AreDistinct.vrt♯ distinct i)
                persp zero =  ⟨ W≈U ⟩⇐ ArePerspectiveCenter.perspective  pc-tPQR-t'QPS `0 
                persp (suc zero) =  ⟨ W≈U ⟩⇐ ArePerspectiveCenter.perspective  pc-tPQR-t'QPS `2
                persp (suc (suc zero)) = ArePerspectiveCenter.perspective  pc-PQR'-QPS `2 ⇒⟨ join-comm ⟩
                persp (suc (suc (suc ())))

                QR♯RS :  join Q♯R ♯ join R♯S
                QR♯RS = ⟨ ≈join ⟩⇐  IsTriangle.AB♯BC QRS


                R'∉RS : R' ∉ join R♯S
                R'∉RS = C7-b (symmetry R♯R') QR♯RS joinᵣ joinₗ ( joinₗ ⇒⟨  trans (sym RA≈R'A) -QRA-.BC≈AB ⟩ )

                R'S♯RS :  join (AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-PQR'-QPS) `2) ♯ join R♯S 
                R'S♯RS =  C5 joinₗ R'∉RS

                W♯S : W ♯ S
                W♯S = C0 ( ArePerspectiveCenter.Center-∉-T'  pc-PQR'-QPS {i♯j = 1♯2}) joinᵣ

                W∉RS :  W ∉ join R♯S
                W∉RS = C7-b W♯S   R'S♯RS joinᵣ joinᵣ (ArePerspectiveCenter.perspective  pc-PQR'-QPS `2)


                Q'R'♯R'S' :  join H'.Q♯R ♯ join H'.R♯S
                Q'R'♯R'S' = ⟨ ≈join ⟩⇐  IsTriangle.AB♯BC HC'-4-6.QRS


                R∉R'S' : R ∉ join H'.R♯S
                R∉R'S' = C7-b R♯R' Q'R'♯R'S' joinᵣ joinₗ ( joinₗ ⇒⟨  trans RA≈R'A HC'-4-6.-QRA-.BC≈AB ⟩ )

                RS'♯R'S' :  join (AreDistinct.vrt♯ (ArePerspectiveCenter.areDistinct  pc-tPQR-t'QPS) `2) ♯ join H'.R♯S 
                RS'♯R'S' =  C5 joinₗ R∉R'S'

                W♯S' : W ♯ S'
                W♯S' = ⟨ W≈U ⟩⇐ C0 ( ArePerspectiveCenter.Center-∉-T'  pc-tPQR-t'QPS {i♯j = 1♯2}) joinᵣ

                W∉R'S' :  W ∉ join H'.R♯S
                W∉R'S' = C7-b W♯S'   RS'♯R'S' joinᵣ joinᵣ ( ⟨ W≈U ⟩⇐  ArePerspectiveCenter.perspective  pc-tPQR-t'QPS `2)



        pa-PRS-QSR' : ArePerspectiveAxis tPRS t'QSR
        pa-PRS-QSR' = desargues _ _ pc-tPRS-t'QSR


        module apa  =  ArePerspectiveAxis pa-PRS-QSR'

        -- axis≈AB : apa.axis  ≈ join A♯B


        A≈apa02 :  A ≈  meet (AreDistinct.sd♯ apa.areDistinct  0♯2)
        A≈apa02 = unq-meet _ (-SAP-.B∈AC ⇒⟨ join-comm ⟩) (HC'-4-6.-QRA-.C∈AB ⇒⟨ ≈join ⟩)


        B≈apa01 :  B ≈  meet (AreDistinct.sd♯ apa.areDistinct  0♯1)
        B≈apa01 = unq-meet _  (-PRB-.C∈AB ⇒⟨ ≈join ⟩) (HC'-4-6.-SBQ-.B∈AC ⇒⟨ join-comm ⟩)

        axis≈AB : apa.axis  ≈ join A♯B
        axis≈AB = unq-join _ (⟨ A≈apa02 ⟩⇐ apa.perspective 0♯2) (⟨ B≈apa01 ⟩⇐ apa.perspective 0♯1)


        D≈D' : D ≈ D'
        D≈D' = begin
               D             
                 ≈⟨ sym $ unq-meet _ meetₗ ( apa.perspective 1♯2 ⇒⟨ axis≈AB ⟩) ⟩
               meet (AreDistinct.sd♯ apa.areDistinct 1♯2)  
                 ≈⟨ unq-meet _ (meetᵣ ⇒⟨ join-comm ⟩) ( apa.perspective 1♯2  ⇒⟨ axis≈AB ⟩) ⟩
               D' 
               ∎



absurdity₂     
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
        → (R♯R' : R ♯ R')
        →  let
             open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
           in
              (R'∉RB : R' ∉ join R♯B)
              → (R'∈RA : R' ∈ join R♯A)
              → (S'∈AS : S' ∈ join A♯S)
              → (Q'∉PR : Q' ∉ join P♯R)
              → (Q∈P'R' : Q ∈ join H'.P♯R)

      → ⊥

absurdity₂  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∈RA 
          S'∈AS
          Q'∉PR
          Q∈P'R'
            =  Lemmas-3.A.B.D≈D' A B C A♯B C∈AB HC HC' D♯D' C♯A C♯B l♯l' R♯R' R'∉RB R'∈RA S'∈AS Q'∉PR Q∈P'R' D♯D' 


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
        → (R♯R' : R ♯ R')
        →  let
             open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
           in
              (R'∉RB : R' ∉ join R♯B)
              → (R'∈RA : R' ∈ join R♯A)
              → ⊥
absurdity  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∈RA 
    =  C≈D' HC'-4-6.C♯D
       where
         open General A B C A♯B C∈AB HC HC'
         open HarmonicConf HC 
         open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
         open Case₁ D♯D' C♯A C♯B l♯l' R♯R'

         open Case₁-R'∉RB R'∉RB

         open Lemmas-0.A  _ _ _ _  _ HC HC' D♯D' C♯A C♯B l♯l' R♯R'
                       R'∉RB R'∈RA

         ¬S'∉AS : ¬ ( S' ∉ join A♯S)
         ¬S'∉AS S'∉AS =  
                C1A3.absurdity 
                  A B C A♯B  C∈AB 
                  flipRS-HC flipRS-HC'  
                  RS-D♯D' C♯A C♯B l♯l' RS-R♯R'  RS-R'∉RB (S'∉AS ⇒⟨ join-comm ⟩) RS-SP≈S'P'
            where 
              import ProjectivePlane.Harmonic.Uniqueness.Case1-A-3 PPD as C1A3

              --open Lemmas-0.A  _ _ _ _  _ HC HC' D♯D' C♯A C♯B l♯l' R♯R'
              --         R'∉RB R'∈RA               


              flipRS-HC : HarmonicConf C∈AB
              flipRS-HC = flipH-RS C♯A C♯B HC
          
              flipRS-HC' : HarmonicConf C∈AB
              flipRS-HC' = flipH-RS C♯A C♯B HC'
          
              RS-D♯D' : hconj flipRS-HC ♯ hconj flipRS-HC'
              RS-D♯D' =  ⟨ sym (FlipH-RS.D→D HC C♯A C♯B) ⟩⇐ D♯D' ⇒⟨ FlipH-RS.D→D HC' C♯A C♯B ⟩
          
          
           
              RS-R♯R' : HarmonicConf.R flipRS-HC ♯ HarmonicConf.R flipRS-HC'
              RS-R♯R' =  ⟨ sym (FlipH-RS.S→R HC C♯A C♯B) ⟩⇐ S♯S' ⇒⟨ FlipH-RS.S→R HC' C♯A C♯B ⟩
          
              RS-R'∉RB : HarmonicConf.R flipRS-HC' ∉ join (HarmonicConf.R♯B flipRS-HC)
              RS-R'∉RB =  ⟨ sym (FlipH-RS.S→R HC' C♯A C♯B) ⟩⇐ S'∉BQ ⇒⟨ -SBQ-.BC≈AB ⇒⟨ ≈join ⟩ ⟩
          
              RS-SP≈S'P' :  join (Lemma-4-6.S♯P flipRS-HC  C♯A C♯B) ≈ join (Lemma-4-6.S♯P flipRS-HC' C♯A C♯B)
              RS-SP≈S'P' = begin
                           join (Lemma-4-6.S♯P flipRS-HC  C♯A C♯B) 
                                ≈⟨ join-flip-cong ( sym $ FlipH-RS.R→S HC C♯A C♯B) (sym $ FlipH-RS.Q→P HC C♯A C♯B) ⟩
                           join Q♯R       ≈⟨ sym -QRA-.BC≈AB ⟩
                           join R♯A       ≈⟨ RA≈R'A ⟩
                           join H'.R♯A    ≈⟨ HC'-4-6.-QRA-.BC≈AB ⟩
                           join H'.Q♯R    ≈⟨ join-flip-cong (FlipH-RS.Q→P HC' C♯A C♯B) (FlipH-RS.R→S HC' C♯A C♯B) ⟩
                           join (Lemma-4-6.S♯P flipRS-HC' C♯A C♯B)
                           ∎

         S'∈AS : S' ∈ join A♯S
         S'∈AS = C6  ¬S'∉AS

         open Lemmas-1.A.B A B C A♯B C∈AB HC HC' 
                            D♯D' C♯A C♯B l♯l' R♯R' 
                            R'∉RB
                            R'∈RA 
                            S'∈AS
         
         ¬Q'∉PR : ¬(Q' ∉ join P♯R)
         ¬Q'∉PR Q'∉PR =  absurdity₂ A B C A♯B C∈AB HC HC' 
                                  D♯D' C♯A C♯B l♯l' R♯R' 
                                  R'∉RB
                                  R'∈RA 
                                  S'∈AS
                                  Q'∉PR
                                  Q∈P'R'
           where
             ¬Q∉P'R' : ¬ (Q ∉ join H'.P♯R)
             ¬Q∉P'R' Q∉P'R' 
                     = absurdity₁ A B C A♯B C∈AB HC HC' 
                                  D♯D' C♯A C♯B l♯l' R♯R' 
                                  R'∉RB
                                  R'∈RA 
                                  S'∈AS
                                  Q'∉PR
                                  Q∉P'R'
             Q∈P'R' :  Q ∈ join H'.P♯R
             Q∈P'R' = C6 ¬Q∉P'R'

         Q'∈PR : Q' ∈ join P♯R
         Q'∈PR = C6 ¬Q'∉PR
         
         ¬Q∉P'R' : ¬ (Q ∉ join H'.P♯R)
         ¬Q∉P'R' Q∉P'R' 
                     =  absurdity₂ A B C A♯B C∈AB HC' HC 
                            (symmetry D♯D') C♯A C♯B (symmetry l♯l') (symmetry R♯R') 
                            (lemma-triangle.B∉AC R'∉RB ⇒⟨ ≈join ⟩) -R'RA-.B∈AC (-S'AS-.C∈AB ⇒⟨ join-comm ⟩ )  
                            Q∉P'R' Q'∈PR

         Q∈P'R' :  Q ∈ join H'.P♯R
         Q∈P'R' = C6  ¬Q∉P'R'

         open import ProjectivePlane.CompleteNPoint.Triangle PP
         R'≈Q : R' ≈ Q
         R'≈Q = begin
                 R'     
              ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
                 meet (IsTriangle.AC♯BC HC'-4-6.PQR)  
              ≈⟨ sym (unq-meet _ (Q∈P'R' ⇒⟨ ≈join ⟩) ( meetₗ  ⇒⟨ trans RA≈R'A HC'-4-6.-QRA-.BC≈AB ⟩)) ⟩ 
                 Q
                ∎
           

         R≈Q' : R ≈ Q'
         R≈Q' = begin
                 R     ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
                 meet (IsTriangle.AC♯BC PQR)  ≈⟨ sym (unq-meet _ (Q'∈PR ⇒⟨ ≈join ⟩) ( meetₗ  ⇒⟨ trans (sym RA≈R'A) -QRA-.BC≈AB ⟩)) ⟩ 
                 Q'
                ∎


         RB≈BQ' : join R♯B ≈ join H'.B♯Q
         RB≈BQ' = join-flip-cong R≈Q' refl


         SA≈P'S' : join (symmetry A♯S) ≈ join (symmetry HC'-4-6.S♯P)
         SA≈P'S' = begin
                  join (symmetry A♯S)        ≈⟨  join-comm -∘- -S'AS-.BC≈AB  -∘- join-comm ⟩
                  join  HC'-4-6.A♯S          ≈⟨  ⟨ join-comm ⟩⇐ sym HC'-4-6.-SAP-.AC≈AB ⇒⟨ join-comm ⟩ ⟩
                  join (symmetry HC'-4-6.S♯P)
                  ∎

         S'≈P : S' ≈ P
         S'≈P = begin
                S'    ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
                meet (IsTriangle.AC♯BC HC'-4-6.PQS) 
                ≈⟨ sym (unq-meet _ (-SAP-.C∈AB  ⇒⟨  SA≈P'S' ⇒⟨ ≈join ⟩ ⟩) 
                                   (  meetₗ  ⇒⟨ trans RB≈BQ' (trans HC'-4-6.-SBQ-.BC≈AC join-comm) ⟩  )) ⟩
                P
                ∎

         R'S'≈PQ : join H'.R♯S ≈ join P♯Q
         R'S'≈PQ = join-flip-cong R'≈Q S'≈P

         C≈D' : C ≈ D'
         C≈D' = unq-meet _  (C∈l ⇒⟨  unq-join _ meetᵣ meetᵣ -∘- sym R'S'≈PQ ⟩) C∈AB 
