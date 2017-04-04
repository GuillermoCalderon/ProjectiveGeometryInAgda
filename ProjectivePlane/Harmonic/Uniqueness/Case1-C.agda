open import Data.Empty
open import Relation.Nullary
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-C {a b c d e}
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


module Lemmas 
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

   module case₂
          -- suppose that
          (D♯D' : D ♯ D') (C♯A : C ♯ A) (C♯B : C ♯ B)(l≈l' : l ≈ l') 
     where



     module case₂₁
          -- suppose that
          (P♯P' : P ♯ P') (Q∉AP' : Q ∉ join H'.A♯P ) (Q'∉AP : Q' ∉ join A♯P)
      where
        open Lemma-4-6 HC C♯A C♯B {-using (PQRS ; PQR; PQS; PRS; S∉AB; P∉AB; Q∉AB )-} public
        module HC'-4-6 = Lemma-4-6 HC' C♯A C♯B

        open import ProjectivePlane.CompleteNPoint PP
        open import ProjectivePlane.CompleteNPoint.Triangle PP
        open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP as TP
        open import Data.Fin
        open import Data.Fin.Setoid
     

        P'AB : IsTriangle P' A B 
        P'AB =  Min→Triangle (record { B♯C = A♯B ; A∉BC = HC'-4-6.P∉AB })
        tP'AB =  triangle→Poly $ isT2T P'AB

        PAB : IsTriangle P A B 
        PAB =  Min→Triangle (record { B♯C = A♯B ; A∉BC = P∉AB })
        tPAB =  triangle→Poly $ isT2T PAB


     
        tPRS  = triangle→Poly $ isT2T PRS
        t'PRS = triangle→Poly $ isT2T HC'-4-6.PRS





        A∉PR : A ∉ join P♯R
        A∉PR = A∉RB ⇒⟨ -PRB-.BC≈AB ⟩

        AB♯AS : join A♯B ♯ join A♯S
        AB♯AS = symmetry $ C5 joinᵣ S∉AB

        B∉AS : B ∉ join A♯S
        B∉AS = C7-b (symmetry A♯B) AB♯AS joinₗ joinₗ joinᵣ

        B∉PS : B ∉ join (symmetry S♯P)
        B∉PS = B∉AS ⇒⟨ begin 
                         join A♯S  ≈⟨ join-comm ⟩
                         join (symmetry A♯S)  ≈⟨ sym  -SAP-.AC≈AB ⟩
                         join S♯P  ≈⟨ join-comm ⟩
                         join (symmetry S♯P) ∎ ⟩ 

   
        B∉l :  B ∉ l
        B∉l = C7-b (symmetry C♯B) (symmetry l♯AB) C∈AB C∈l joinᵣ

        l♯P'B : l ♯ join HC'-4-6.P♯B
        l♯P'B = symmetry $ C5 joinᵣ B∉l

        Q∉P'B : Q ∉ join HC'-4-6.P♯B
        Q∉P'B = C7-b (C0 Q∉AP' joinᵣ) l♯P'B (meetᵣ ⇒⟨ sym l≈l' ⟩) joinₗ meetᵣ

        open  import ProjectivePlane.CompleteNPoint.Quadrangle PP as Q 
        perspectiveCenter-PRS-P'AB : ArePerspectiveCenter tPRS tP'AB
        perspectiveCenter-PRS-P'AB 
          = toArePerspectiveCenter 
            (record
               { Center = Q
               ; areDistinct = toAreDistinct (record
                                                { vrt-0 = P♯P'
                                                ; vrt-1 = R♯A
                                                ; vrt-2 = symmetry B♯S
                                                ; sd-01 = symmetry (C5 joinᵣ (A∉PR ⇒⟨ ≈join ⟩))
                                                ; sd-02 = symmetry (C5 joinᵣ (B∉PS ⇒⟨ ≈join ⟩))
                                                ; sd-12 = RS♯AB
                                                })
               ; perspective =
                             λ { zero →  meetᵣ ⇒⟨ unq-join _ meetᵣ (meetᵣ ⇒⟨ sym l≈l' ⟩) ⟩
                               ; (suc zero) → meetₗ 
                               ; (suc (suc zero)) → -SBQ-.C∈AB
                               ; (suc (suc (suc ())))
                               }
 
               ; O∉T-01 = nonc3 PQRS (symmetry Q.0♯1) Q.0♯2 Q.1♯2 ⇒⟨  ≈join ⟩
               ; O∉T-02 = nonc3 PQRS (symmetry Q.0♯1) Q.0♯3 Q.1♯3 ⇒⟨  ≈join ⟩
               ; O∉T-12 =  nonc3 PQRS  Q.1♯2 Q.2♯3 Q.1♯3 ⇒⟨  ≈join ⟩
               ; O∉T'-01 = Q∉AP' ⇒⟨ join-comm ⟩
               ; O∉T'-02 = Q∉P'B ⇒⟨ ≈join ⟩
               ; O∉T'-12 = Q∉AB
               })
               

        A∉P'R' : A ∉ join H'.P♯R
        A∉P'R' = H'.A∉RB ⇒⟨ HC'-4-6.-PRB-.BC≈AB ⟩

        AB♯AS' : join A♯B ♯ join HC'-4-6.A♯S
        AB♯AS' = symmetry $ C5 joinᵣ HC'-4-6.S∉AB

        B∉AS' : B ∉ join HC'-4-6.A♯S
        B∉AS' = C7-b (symmetry A♯B) AB♯AS' joinₗ joinₗ joinᵣ

        B∉P'S' : B ∉ join (symmetry HC'-4-6.S♯P)
        B∉P'S' = B∉AS' ⇒⟨ begin 
                           join HC'-4-6.A♯S             ≈⟨ join-comm ⟩
                           join (symmetry HC'-4-6.A♯S)  ≈⟨ sym  HC'-4-6.-SAP-.AC≈AB ⟩
                           join HC'-4-6.S♯P             ≈⟨ join-comm ⟩
                           join (symmetry HC'-4-6.S♯P) 
                          ∎ 
                       ⟩  

   
        B∉l' :  B ∉ l'
        B∉l' = C7-b (symmetry C♯B) (symmetry H'.l♯AB) C∈AB H'.C∈l joinᵣ


        l'♯PB : l' ♯ join P♯B
        l'♯PB = symmetry $ C5 joinᵣ B∉l'

        Q'∉PB : Q' ∉ join P♯B
        Q'∉PB = C7-b (C0 Q'∉AP joinᵣ) l'♯PB (meetᵣ ⇒⟨  l≈l' ⟩) joinₗ meetᵣ


        perspectiveCenter-P'R'S'-PAB : ArePerspectiveCenter t'PRS tPAB
        perspectiveCenter-P'R'S'-PAB 
          = toArePerspectiveCenter 
            (record
               { Center = Q'
               ; areDistinct = toAreDistinct (record
                                                { vrt-0 = symmetry P♯P'
                                                ; vrt-1 = H'.R♯A
                                                ; vrt-2 = symmetry HC'-4-6.B♯S
                                                ; sd-01 = symmetry (C5 joinᵣ (A∉P'R' ⇒⟨ ≈join ⟩))
                                                ; sd-02 = symmetry (C5 joinᵣ (B∉P'S' ⇒⟨ ≈join ⟩))
                                                ; sd-12 = H'.RS♯AB
                                                })
               ; perspective =
                             λ { zero →  meetᵣ ⇒⟨ unq-join _ meetᵣ (meetᵣ ⇒⟨ l≈l' ⟩) ⟩
                               ; (suc zero) → meetₗ 
                               ; (suc (suc zero)) → HC'-4-6.-SBQ-.C∈AB
                               ; (suc (suc (suc ())))
                               }
 
               ; O∉T-01 = nonc3 HC'-4-6.PQRS (symmetry Q.0♯1) Q.0♯2 Q.1♯2 ⇒⟨  ≈join ⟩
               ; O∉T-02 = nonc3 HC'-4-6.PQRS (symmetry Q.0♯1) Q.0♯3 Q.1♯3 ⇒⟨  ≈join ⟩
               ; O∉T-12 =  nonc3 HC'-4-6.PQRS  Q.1♯2 Q.2♯3 Q.1♯3 ⇒⟨  ≈join ⟩
               ; O∉T'-01 = Q'∉AP ⇒⟨ join-comm ⟩
               ; O∉T'-02 = Q'∉PB ⇒⟨ ≈join ⟩
               ; O∉T'-12 = HC'-4-6.Q∉AB
               })
                                                
        perspectiveAxis-PRS-P'AB :  ArePerspectiveAxis tPRS tP'AB
        perspectiveAxis-PRS-P'AB = desargues _ _  perspectiveCenter-PRS-P'AB

        perspectiveAxis-P'R'S'-PAB :  ArePerspectiveAxis t'PRS tPAB
        perspectiveAxis-P'R'S'-PAB = desargues _ _  perspectiveCenter-P'R'S'-PAB


        module apa-PRS-P'AB = ArePerspectiveAxis  perspectiveAxis-PRS-P'AB
        module apa-P'R'S'-PAB =  ArePerspectiveAxis perspectiveAxis-P'R'S'-PAB

        axis₁ = apa-PRS-P'AB.axis
        axis₂ = apa-P'R'S'-PAB.axis

        W₁ U₁ : Point
        W₁ = meet ( AreDistinct.sd♯ apa-PRS-P'AB.areDistinct  TP.0♯1)
        U₁ = meet ( AreDistinct.sd♯ apa-PRS-P'AB.areDistinct  TP.0♯2)

        
        PR♯PS : edge tPRS TP.0♯1 ♯ edge tPRS TP.0♯2 
        PR♯PS =   symmetry (IsTriangle.AC♯AB PRS) 

        P∉axis₁ : P ∉ axis₁
        P∉axis₁ = apa-PRS-P'AB.axis-∉-T {TP.`0}

        W₁♯P : W₁ ♯ P
        W₁♯P = symmetry $ C0 P∉axis₁ (apa-PRS-P'AB.perspective TP.0♯1)

        W₁∉PS : W₁ ∉ edge tPRS TP.0♯2
        W₁∉PS = C7-b W₁♯P PR♯PS joinₗ joinₗ meetₗ


        W₁♯U₁ : W₁ ♯ U₁
        W₁♯U₁ = C0 W₁∉PS meetₗ

        axis₁≈W₁U₁ : axis₁ ≈ join W₁♯U₁
        axis₁≈W₁U₁ = unq-join _ (apa-PRS-P'AB.perspective TP.0♯1) 
                               (apa-PRS-P'AB.perspective TP.0♯2)
        
        W₂ U₂ :  Point
        W₂ = meet ( AreDistinct.sd♯ apa-P'R'S'-PAB.areDistinct  TP.0♯1)
        U₂ = meet ( AreDistinct.sd♯ apa-P'R'S'-PAB.areDistinct  TP.0♯2)


        W₁≈U₂ : W₁ ≈ U₂
        W₁≈U₂ = meet-flip-cong (trans ≈join $ trans (sym -PRB-.AC≈AB) ≈join) 
                               ( trans join-comm  ( trans HC'-4-6.-SAP-.BC≈AC join-comm))
        W₂≈U₁ : W₂ ≈ U₁
        W₂≈U₁ = meet-flip-cong (trans ≈join $ trans (sym HC'-4-6.-PRB-.AC≈AB) ≈join) 
                               ( trans join-comm  ( trans -SAP-.BC≈AC join-comm))

        U₂♯W₂ : U₂ ♯ W₂ 
        U₂♯W₂ =  ⟨  sym W₁≈U₂ ⟩⇐ W₁♯U₁ ⇒⟨  sym W₂≈U₁ ⟩
     

        A∉axis₁ : A ∉ axis₁
        A∉axis₁ = apa-PRS-P'AB.axis-∉-T' {TP.`1}

        AB♯axis₁ : join A♯B ♯ axis₁
        AB♯axis₁ = C5 joinₗ A∉axis₁

        axis₁≈axis₂ :  axis₁ ≈ axis₂
        axis₁≈axis₂ = begin
                     axis₁        ≈⟨  axis₁≈W₁U₁ ⟩
                     join W₁♯U₁  ≈⟨ join-cong W₁≈U₂ (sym W₂≈U₁) ⟩
                     join U₂♯W₂  ≈⟨ sym (unq-join _ (apa-P'R'S'-PAB.perspective TP.0♯2) (apa-P'R'S'-PAB.perspective TP.0♯1)) ⟩
                     axis₂
                    ∎

        D≈D' : D ≈ D'
        D≈D' = begin
                meet RS♯AB     ≈⟨ unq-meet _ meetᵣ ( ⟨ ≈meet ⟩⇐ apa-PRS-P'AB.perspective TP.1♯2) ⟩
                meet AB♯axis₁   ≈⟨ sym (unq-meet _ meetᵣ ( ⟨ ≈meet ⟩⇐ apa-P'R'S'-PAB.perspective TP.1♯2 ⇒⟨ sym axis₁≈axis₂ ⟩)) ⟩
                meet H'.RS♯AB
               ∎

        absurdity : ⊥
        absurdity = D≈D' D♯D'

     module case₂₂
          -- suppose that
          (P♯P' : P ♯ P') (Q∉AP' : Q ∉ join H'.A♯P ) (Q'∈AP : Q' ∈ join A♯P)
      where
        open Lemma-4-6 HC C♯A C♯B  public
        module HC'-4-6 = Lemma-4-6 HC' C♯A C♯B

        open import ProjectivePlane.CompleteNPoint PP
        open import ProjectivePlane.CompleteNPoint.Triangle PP
        open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP as TP
        open import Data.Fin

        AP♯l : join A♯P ♯ l
        AP♯l = C5 joinₗ (C7-b (symmetry C♯A) (symmetry l♯AB) C∈AB C∈l joinₗ)

        Q'≈P : Q' ≈ P
        Q'≈P = begin
               Q'          ≈⟨ unq-meet _ Q'∈AP (meetᵣ ⇒⟨ sym l≈l' ⟩) ⟩
               meet AP♯l   ≈⟨ sym (unq-meet _ joinᵣ meetᵣ) ⟩
               P
               ∎

        QSR : IsTriangle Q S R
        QSR = Min→Triangle (record { B♯C = symmetry R♯S ; A∉BC = Q∉RS ⇒⟨ join-comm ⟩ })
        tQSR =  triangle→Poly $ isT2T QSR
        t'PRS = triangle→Poly $ isT2T HC'-4-6.PRS

        l♯SQ : l ♯ join S♯Q
        l♯SQ =  ⟨ unq-join _ meetᵣ meetᵣ ⟩⇐ IsTriangle.AB♯BC PQS ⇒⟨ join-comm ⟩
 
        Q♯P' : Q ♯ P'
        Q♯P' = C0 Q∉AP' joinᵣ

        P'∉SQ : P' ∉ join S♯Q
        P'∉SQ = C7-b (symmetry Q♯P') l♯SQ meetᵣ joinᵣ ( meetᵣ ⇒⟨ sym  l≈l' ⟩)

        R'B♯SQ : join H'.R♯B ♯ join S♯Q
        R'B♯SQ = C5 meetₗ P'∉SQ

        S∉R'B : S ∉ join H'.R♯B
        S∉R'B = C7-b (symmetry B♯S) (symmetry R'B♯SQ) -SBQ-.B∈AC joinᵣ joinₗ

        S♯R' : S ♯ R'
        S♯R' = C0 S∉R'B joinₗ


        l♯QR : l ♯ join Q♯R
        l♯QR = ⟨ unq-join _ meetᵣ meetᵣ ⟩⇐ IsTriangle.AB♯BC PQR 

        P'∉QR : P' ∉ join Q♯R
        P'∉QR = C7-b (symmetry Q♯P') l♯QR meetᵣ joinₗ (meetᵣ ⇒⟨ sym l≈l' ⟩)

        P'A♯QR : join H'.A♯P ♯ join Q♯R
        P'A♯QR = C5 joinᵣ P'∉QR

        R∉P'A : R ∉ join H'.A♯P
        R∉P'A = C7-b R♯A (symmetry P'A♯QR) -QRA-.C∈AB joinₗ joinᵣ

        R♯S' : R ♯ S'
        R♯S' = C0 R∉P'A  meetₗ

        S'Q'♯R'S' : join HC'-4-6.S♯Q ♯ join H'.R♯S
        S'Q'♯R'S' = C5 joinᵣ HC'-4-6.Q∉RS          

        R∉R'S' : R ∉ join H'.R♯S
        R∉R'S' = C7-b R♯S' S'Q'♯R'S' joinₗ joinᵣ 
                 (joinₗ ⇒⟨ begin  
                           join R♯B ≈⟨  -PRB-.BC≈AC ⟩ 
                           join P♯B ≈⟨ join-flip-cong ( sym Q'≈P) refl ⟩
                           join H'.B♯Q ≈⟨  HC'-4-6.-SBQ-.BC≈AC ⟩
                           join HC'-4-6.S♯Q  ∎ ⟩)

        RS♯R'S' : join R♯S ♯ join H'.R♯S
        RS♯R'S' = C5 joinₗ R∉R'S'


        perspectiveCenter-tQSR-t'PRS : ArePerspectiveCenter tQSR t'PRS
        perspectiveCenter-tQSR-t'PRS
          = toArePerspectiveCenter 
            (record
             { Center = Q'
             ; areDistinct 
               = toAreDistinct 
                 (record
                   { vrt-0 = C0 Q∉AP' joinᵣ
                   ; vrt-1 = S♯R'
                   ; vrt-2 = R♯S'
                   ; sd-01 =  ⟨ join-comm ⟩⇐ symmetry R'B♯SQ ⇒⟨ trans (HC'-4-6.-PRB-.BC≈AB) ≈join ⟩ 
                   ; sd-02 =  ⟨ ≈join ⟩⇐ symmetry P'A♯QR ⇒⟨  trans  (HC'-4-6.-SAP-.BC≈AC) join-comm ⟩
                   ; sd-12 =  ⟨ join-comm ⟩⇐ RS♯R'S'
                   })
             ; perspective = λ { zero →    meetᵣ ⇒⟨ unq-join _ (meetᵣ ⇒⟨ l≈l' ⟩) meetᵣ ⟩
                               ; (suc zero) →  ⟨ Q'≈P ⟩⇐  joinᵣ  ⇒⟨ unq-join _ meetₗ (HC'-4-6.-QRA-.B∈AC ⇒⟨ join-flip-cong Q'≈P refl ⟩  ) ⟩
                               ; (suc (suc zero)) →  ⟨ Q'≈P ⟩⇐  joinᵣ {B} {P} {symmetry P♯B}  ⇒⟨ unq-join _ (  -PRB-.B∈AC ⇒⟨ join-comm ⟩) ( meetᵣ ⇒⟨ join-cong refl Q'≈P ⟩ )⟩
                               ; (suc (suc (suc ())))
                               }  
             ; O∉T-01 =  ⟨ Q'≈P ⟩⇐ IsTriangle.A∉BC PQS ⇒⟨  ≈join ⟩
             ; O∉T-02 = ⟨ Q'≈P ⟩⇐ IsTriangle.A∉BC PQR ⇒⟨  ≈join ⟩
             ; O∉T-12 = ⟨ Q'≈P ⟩⇐ IsTriangle.A∉BC PRS ⇒⟨  join-comm ⟩
             ; O∉T'-01 =  IsTriangle.B∉AC HC'-4-6.PQR ⇒⟨ ≈join ⟩
             ; O∉T'-02 = IsTriangle.B∉AC HC'-4-6.PQS ⇒⟨  ≈join ⟩
             ; O∉T'-12 = HC'-4-6.Q∉RS
             })
     

        perspectiveAxis-tQSR-t'PRS :  ArePerspectiveAxis tQSR t'PRS
        perspectiveAxis-tQSR-t'PRS = desargues _ _  perspectiveCenter-tQSR-t'PRS

        module apa-tQSR-t'PRS =  ArePerspectiveAxis perspectiveAxis-tQSR-t'PRS 
        axis≈AB : apa-tQSR-t'PRS.axis  ≈ join A♯B
        axis≈AB = unq-join _ ( ⟨ unq-meet _ (-QRA-.C∈AB ⇒⟨ ≈join ⟩) (HC'-4-6.-SAP-.B∈AC ⇒⟨ join-comm ⟩) ⟩⇐ apa-tQSR-t'PRS.perspective 0♯2) 
                            ( ⟨ unq-meet _ (-SBQ-.B∈AC ⇒⟨ join-comm ⟩) (HC'-4-6.-PRB-.C∈AB ⇒⟨ ≈join ⟩) ⟩⇐ apa-tQSR-t'PRS.perspective 0♯1)

        D≈D' : D ≈ D'
        D≈D' = begin
                     D             
                        ≈⟨ sym (unq-meet _ (meetₗ ⇒⟨ join-comm ⟩) ( apa-tQSR-t'PRS.perspective 1♯2 ⇒⟨ axis≈AB ⟩))  ⟩
                     meet (AreDistinct.sd♯ apa-tQSR-t'PRS.areDistinct 1♯2)  
                        ≈⟨ unq-meet _ meetᵣ ( apa-tQSR-t'PRS.perspective 1♯2 ⇒⟨ axis≈AB ⟩) ⟩
                     D'
                     ∎
 

        -- contradiction
        absurdity : ⊥
        absurdity = D≈D' D♯D'
        ------ case₂₂

     module case₂₃
          -- suppose that
          (P♯P' : P ♯ P') (Q∈AP' : Q ∈ join H'.A♯P ) (Q'∈AP : Q' ∈ join A♯P)
      where
        open Lemma-4-6 HC C♯A C♯B  public
        module HC'-4-6 = Lemma-4-6 HC' C♯A C♯B

        AP♯l : join A♯P ♯ l
        AP♯l = C5 joinₗ (C7-b (symmetry C♯A) (symmetry l♯AB) C∈AB C∈l joinₗ)

        Q'≈P : Q' ≈ P
        Q'≈P = begin
               Q'          ≈⟨ unq-meet _ Q'∈AP (meetᵣ ⇒⟨ sym l≈l' ⟩) ⟩
               meet AP♯l   ≈⟨ sym (unq-meet _ joinᵣ meetᵣ) ⟩
               P
               ∎

        AP'♯l' : join H'.A♯P ♯ l'
        AP'♯l' = C5 joinₗ (C7-b (symmetry C♯A) (symmetry H'.l♯AB) C∈AB H'.C∈l joinₗ)

        Q≈P' : Q ≈ P'
        Q≈P' = begin
               Q          ≈⟨ unq-meet _ Q∈AP' (meetᵣ ⇒⟨  l≈l' ⟩) ⟩
               meet AP'♯l'   ≈⟨ sym (unq-meet _ joinᵣ meetᵣ) ⟩
               P'
               ∎

        S≈R' : S ≈ R'
        S≈R' = sym (unq-meet _ (HC'-4-6.-QRA-.B∈AC ⇒⟨ join-flip-cong Q'≈P refl ⟩) (HC'-4-6.-PRB-.B∈AC ⇒⟨ join-flip-cong (sym Q≈P') refl ⟩))

        S'≈R : S' ≈ R
        S'≈R =  sym (unq-meet _ (-QRA-.B∈AC ⇒⟨ join-flip-cong Q≈P' refl ⟩) (-PRB-.B∈AC ⇒⟨ join-flip-cong (sym Q'≈P) refl ⟩))

        RS≈R'S' : join R♯S ≈ join H'.R♯S
        RS≈R'S' = join-flip-cong (sym S'≈R) S≈R'

        D≈D' : D ≈ D'
        D≈D' = meet-cong RS≈R'S' refl

        absurdity : ⊥
        absurdity = D≈D' D♯D'
   
----------------------------
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
        → (l≈l' : l ≈ l')
        → ⊥

absurdity  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l≈l'
    =  D≈D' D♯D'
       where
         open General A B C A♯B C∈AB HC HC'
         open HarmonicConf HC 
         open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')

         P≈P' : P ≈ P'
         P≈P' P♯P' = 
                     Lemmas.case₂.case₂₃.absurdity 
                                   A B C A♯B C∈AB HC HC' 
                                   D♯D' C♯A C♯B l≈l'
                                   P♯P' Q∈AP' Q'∈AP
           where 
             ¬Q∉AP' : ¬ (Q ∉ join H'.A♯P)
             ¬Q∉AP' Q∉AP' = Lemmas.case₂.case₂₂.absurdity 
                                   A B C A♯B C∈AB HC HC' 
                                   D♯D' C♯A C♯B l≈l'
                                   P♯P' Q∉AP' Q'∈AP
               where
                 ¬Q'∉AP : ¬ (Q' ∉ join A♯P)
                 ¬Q'∉AP Q'∉AP =  Lemmas.case₂.case₂₁.absurdity 
                                   A B C A♯B C∈AB HC HC' 
                                   D♯D' C♯A C♯B l≈l'
                                   P♯P' Q∉AP' Q'∉AP
                 Q'∈AP : Q' ∈ join A♯P
                 Q'∈AP = C6  ¬Q'∉AP

             Q∈AP' : Q ∈ join H'.A♯P
             Q∈AP' = C6 ¬Q∉AP'
           
             ¬Q'∉AP : ¬ (Q' ∉ join A♯P)
             ¬Q'∉AP Q'∉AP = Lemmas.case₂.case₂₂.absurdity 
                                   A B C A♯B C∈AB HC' HC 
                                   (symmetry D♯D') C♯A C♯B (sym l≈l')
                                   (symmetry P♯P') Q'∉AP Q∈AP' 

             Q'∈AP : Q' ∈ join A♯P
             Q'∈AP = C6 ¬Q'∉AP

         Q≈Q' : Q ≈ Q' 
         Q≈Q' Q♯Q' =  Lemmas.case₂.case₂₁.absurdity 
                         B A  C (symmetry A♯B)
                         (C∈AB ⇒⟨ join-comm ⟩)
                         (flipH HC) (flipH HC') 
                         (⟨ sym $ SymmetryHarmonic.D→D HC ⟩⇐ D♯D' ⇒⟨  SymmetryHarmonic.D→D  HC' ⟩) 
                          C♯B C♯A l≈l'
                          ( ⟨ sym (SymmetryHarmonic.Q→P HC) ⟩⇐ Q♯Q' ⇒⟨ SymmetryHarmonic.Q→P HC' ⟩) 
                          ( ⟨  sym (SymmetryHarmonic.P→Q HC) ⟩⇐ P∉BQ' ⇒⟨ join-cong refl (SymmetryHarmonic.Q→P HC') ⟩) 
                          ( ⟨  sym (SymmetryHarmonic.P→Q HC')⟩⇐ P'∉BQ ⇒⟨ join-cong refl (SymmetryHarmonic.Q→P HC) ⟩) 
                 where
                   open Lemma-4-6 HC C♯A C♯B  public
                   module HC'-4-6 = Lemma-4-6 HC' C♯A C♯B

                   P∉BQ' : P ∉ join H'.B♯Q
                   P∉BQ' =  ⟨ P≈P' ⟩⇐ HC'-4-6.P∉SQ ⇒⟨  sym HC'-4-6.-SBQ-.BC≈AC  ⟩
               
                   P'∉BQ : P' ∉ join B♯Q
                   P'∉BQ =  ⟨ sym P≈P' ⟩⇐ P∉SQ ⇒⟨  sym -SBQ-.BC≈AC  ⟩
                 


         S≈S' : S ≈ S'
         S≈S' = unq-meet _ ( meetₗ ⇒⟨ join-cong refl P≈P' ⟩) (meetᵣ ⇒⟨ join-cong refl Q≈Q' ⟩)

         open Lemma-4-6 HC C♯A C♯B  public
         module HC'-4-6 = Lemma-4-6 HC' C♯A C♯B
         open import ProjectivePlane.CompleteNPoint.Triangle PP

         PR≈P'R' : join P♯R ≈ join H'.P♯R
         PR≈P'R' = begin
                   join P♯R  ≈⟨ sym -PRB-.AC≈AB ⟩
                   join P♯B  ≈⟨ join-cong P≈P' refl ⟩
                   join HC'-4-6.P♯B ≈⟨ HC'-4-6.-PRB-.AC≈AB ⟩
                   join H'.P♯R
                   ∎

         QR≈Q'R' : join Q♯R ≈ join H'.Q♯R
         QR≈Q'R' = begin
                   join Q♯R  ≈⟨ sym -QRA-.AC≈AB ⟩
                   join Q♯A  ≈⟨ join-cong Q≈Q' refl ⟩
                   join HC'-4-6.Q♯A ≈⟨ HC'-4-6.-QRA-.AC≈AB ⟩
                   join H'.Q♯R
                   ∎

         R≈R' :  R ≈ R'
         R≈R' = begin
                R    ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
                meet (IsTriangle.AC♯BC PQR)    ≈⟨ meet-cong ( ≈join -∘- PR≈P'R' -∘- ≈join) ( QR≈Q'R' -∘- ≈join) ⟩
                meet (IsTriangle.AC♯BC HC'-4-6.PQR) ≈⟨ sym (unq-meet _ joinᵣ joinᵣ) ⟩
                R'
                ∎

         RS≈R'S' : join R♯S ≈ join H'.R♯S
         RS≈R'S' = join-cong R≈R' S≈S'

         D≈D' : D ≈ D'
         D≈D' = meet-cong RS≈R'S' refl
