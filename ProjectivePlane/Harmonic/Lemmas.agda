-- {-# OPTIONS --no-eta-equality #-} 

open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Lemmas {a b c d e}
       (PPD : Desarguesian a b c d e)  where

open import Function using (_$_)

open import ProjectivePlane.Harmonic.Base PPD
open Desarguesian PPD 
  renaming (projective to PP)

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP
open import ProjectivePlane.PropertiesGeneral PP 
open import ProjectivePlane.CompleteNPoint.Quadrangle PP
     hiding (0♯1)


flipH : ∀ {A B C} → {A♯B : A ♯ B} {C∈AB : C ∈ join A♯B} → 
        HarmonicConf C∈AB  → HarmonicConf (C∈AB ⇒⟨ sym-join ⟩)
flipH Harm-ABC = 
      record { l = l 
             ; C∈l = C∈l 
             ; l♯AB = l♯AB ⇒⟨ sym-join ⟩ 
             ; R = R 
             ; R∉l = R∉l 
             ; R∉AB = R∉AB ⇒⟨  sym-join ⟩ 
             }
        where open HarmonicConf Harm-ABC


module SymmetryHarmonic  
       {A B C} 
       {A♯B : A ♯ B} 
       {C∈AB : C ∈ join A♯B}
       (HConf : HarmonicConf C∈AB) where

-- some results about symetry of an Harmonic Configuration

   open HarmonicConf HConf
   module SymH = HarmonicConf (flipH HConf)

   P→Q : P ≈ SymH.Q
   P→Q = meet-cong ≈join refl

   Q→P : Q ≈ SymH.P
   Q→P = meet-cong ≈join refl

   S→S : S ≈ SymH.S
   S→S = meet-flip-cong (join-cong refl P→Q) (join-cong refl Q→P )

   D→D : D ≈ SymH.D
   D→D = meet-cong (join-cong refl S→S)  sym-join



{-- lemma 4.4
    =========
    Let A ≠ B. Then h(A,B;A) = A and h(A,B;B) = B
   for any selection of construction elements l, R
   -----------------------------------------------
-}
Harm-BAB≈B :  ∀ {A B : Point} {A♯B : A ♯ B} 
              → (HCB : HarmonicConf {A} {B} {A♯B} joinᵣ)
              → B ≈ HConjugate HCB
Harm-BAB≈B {A} {B} {A♯B} HCB = unq-meet RS♯AB (⟨ B≈S ⟩⇐ joinᵣ) joinᵣ
           where open HarmonicConf HCB
                 B≈P : B ≈ P
                 B≈P = unq-meet RB♯l joinᵣ C∈l
                 B≈S : B ≈ S
                 B≈S = unq-meet AP♯BQ ( ⟨ B≈P ⟩⇐ joinᵣ) joinₗ

Harm-C≈B :  ∀ {A B C : Point} {A♯B : A ♯ B} {C∈AB : C ∈ join A♯B}
              → (HC : HarmonicConf C∈AB)
              → C ≈ B
              → B ≈  HConjugate HC
Harm-C≈B {A} {B} {C} {A♯B} HC C≈B = unq-meet RS♯AB ( ⟨ B≈S ⟩⇐ joinᵣ) joinᵣ
    where open HarmonicConf HC
          B≈P : B ≈ P
          B≈P = unq-meet _ joinᵣ (⟨ sym C≈B ⟩⇐ C∈l)
          B≈S : B ≈ S
          B≈S = unq-meet AP♯BQ ( ⟨ B≈P ⟩⇐ joinᵣ) joinₗ


                      

-- lemma 4.4
Harm-AAB≈A :  ∀ {A B : Point} {A♯B : A ♯ B} 
              → (HCA : HarmonicConf {A} {B} {A♯B} joinₗ)
              → A ≈ HConjugate HCA
Harm-AAB≈A {A} {B} {A♯B} HCA = unq-meet RS♯AB ( ⟨ A≈S ⟩⇐ joinᵣ ) joinₗ
           where open HarmonicConf HCA
                 A≈Q : A ≈ Q
                 A≈Q = unq-meet RA♯l joinᵣ C∈l
                 A≈S : A ≈ S
                 A≈S = unq-meet AP♯BQ joinₗ (⟨ A≈Q ⟩⇐ joinᵣ)

Harm-C≈A :  ∀ {A B C : Point} {A♯B : A ♯ B} {C∈AB : C ∈ join A♯B}
              → (HC : HarmonicConf C∈AB)
              → C ≈ A
              → A ≈  HConjugate HC
Harm-C≈A {A} {B} {C} {A♯B} HC C≈A = unq-meet RS♯AB ( ⟨ A≈S ⟩⇐ joinᵣ) joinₗ
    where open HarmonicConf HC
          A≈Q : A ≈ Q
          A≈Q = unq-meet _ joinᵣ (⟨ sym C≈A ⟩⇐ C∈l)
          A≈S : A ≈ S
          A≈S = unq-meet _ joinₗ ( ⟨ A≈Q ⟩⇐ joinᵣ)

-- end lemma 4.4-------------------------------------------
{- 
   Lemma 4.5
   =========
   a.  If C ≠ A, then Q ∉ AB, Q ≠ S, S ≠ A, and D ≠ A
   b.  If C ≠ B,  then P ∉ AB, P ≠ S, S ≠ B and D ≠ B
   --------------------------------------------------
-}

module Lemma-4-5-a  
       {A B C : Point}{A♯B : A ♯ B}  
       {C∈AB : C ∈ join A♯B}
       (HC : HarmonicConf C∈AB) 
       (C♯A : C ♯ A) where

  open HarmonicConf HC

  C∉RA : C ∉ join R♯A
  C∉RA = C7-b C♯A AB♯RA joinₗ joinᵣ C∈AB

  C♯Q : C ♯ Q
  C♯Q = C0 C∉RA meetₗ

  Q∉AB : Q ∉ join A♯B
  Q∉AB = C7-b (symmetry C♯Q) l♯AB C∈l C∈AB meetᵣ

  Q♯A : Q ♯ A
  Q♯A = C0 Q∉AB joinₗ

  A∉BQ : A ∉ join B♯Q
  A∉BQ = C7-b (symmetry Q♯A) (symmetry BQ♯RA) meetₗ joinᵣ joinᵣ

  A♯S : A ♯ S
  A♯S = C0 A∉BQ meetᵣ

  S∉RA : S ∉ join R♯A
  S∉RA = C7-b (symmetry A♯S) AP♯RA joinₗ joinᵣ meetₗ

  S♯Q : S ♯ Q
  S♯Q = C0 S∉RA meetₗ

  RS♯RA : join R♯S ♯ join R♯A
  RS♯RA = C5 joinᵣ S∉RA

  A∉RS : A ∉ join R♯S
  A∉RS = C7-b (symmetry R♯A) (symmetry RS♯RA) joinₗ joinₗ joinᵣ

  A♯D : A ♯ D
  A♯D = C0 A∉RS meetₗ

module Lemma-4-5-b  
       {A B C : Point}
       {A♯B : A ♯ B}  
       {C∈AB : C ∈ join A♯B}
       (HC : HarmonicConf C∈AB) 
       (C♯B : C ♯ B) where

  open HarmonicConf HC
  module Sym = Lemma-4-5-a (flipH HC) (C♯B)
  open SymmetryHarmonic HC

  P∉AB : P ∉ join A♯B
  P∉AB =  ⟨  P→Q ⟩⇐  Sym.Q∉AB  ⇒⟨ join-comm ⟩

  B♯S : B ♯ S
  B♯S =  Sym.A♯S ⇒⟨ sym S→S ⟩

  S♯P : S ♯ P
  S♯P =  ⟨ S→S ⟩⇐  Sym.S♯Q  ⇒⟨ sym P→Q ⟩

  P♯B : P ♯ B
  P♯B =  ⟨ P→Q ⟩⇐ Sym.Q♯A

  B♯D : B ♯ D
  B♯D = Sym.A♯D ⇒⟨ sym D→D ⟩ 

  P♯C : P ♯ C
  P♯C = C0 P∉AB C∈AB

module Lemma-4-6 
       {A B C : Point}
       {A♯B : A ♯ B}  
       {C∈AB : C ∈ join A♯B}
       (HC : HarmonicConf C∈AB)
       (C♯A : C ♯ A)
       (C♯B : C ♯ B) where


    open HarmonicConf HC
    open  Lemma-4-5-a HC C♯A public
    open  Lemma-4-5-b HC C♯B public

    BQ♯AB : join B♯Q ♯ join A♯B
    BQ♯AB = C5 joinᵣ Q∉AB

    S∉AB : S ∉ join A♯B
    S∉AB = C7-b (symmetry B♯S) BQ♯AB joinₗ joinᵣ meetᵣ


    AR♯RS : join R♯A ♯ join R♯S
    AR♯RS = symmetry $ C5 joinᵣ S∉RA

    Q∉RS : Q ∉ join R♯S
    Q∉RS = C7-b Q♯R AR♯RS joinₗ joinₗ meetₗ

    -- prueba análoga para P∉RS (¿cómo hacer una sola?)

    S∉RB : S ∉ join R♯B
    S∉RB = C7-b (symmetry B♯S) BQ♯RB joinₗ joinᵣ meetᵣ

    BR♯RS : join R♯B ♯ join R♯S
    BR♯RS = symmetry $ C5 joinᵣ S∉RB

    P∉RS : P ∉ join R♯S
    P∉RS = C7-b P♯R BR♯RS joinₗ joinₗ meetₗ

    P∉BQ : P ∉ join B♯Q
    P∉BQ = C7-b P♯B (symmetry BQ♯RB) joinᵣ joinₗ meetₗ

    P∉SQ : P ∉ join S♯Q
    P∉SQ = P∉BQ ⇒⟨ unq-join S♯Q meetᵣ joinᵣ ⟩


    P∉QR : P ∉ join Q♯R
    P∉QR = P∉RA ⇒⟨ unq-join Q♯R meetₗ joinₗ ⟩

    open import ProjectivePlane.CompleteNPoint.Triangle PP
    PQR : IsTriangle P Q R
    PQR =  Min→Triangle (record { B♯C = Q♯R ; A∉BC = P∉QR })

    PQS : IsTriangle P Q S
    PQS =  Min→Triangle (record { B♯C = symmetry S♯Q ; A∉BC = P∉SQ ⇒⟨ join-comm ⟩ })

    PRS : IsTriangle P R S
    PRS = Min→Triangle (record { B♯C = R♯S ; A∉BC = P∉RS })

    QRS : IsTriangle Q R S
    QRS =  Min→Triangle (record { B♯C = R♯S ; A∉BC = Q∉RS }) 

    -- Then, PQRS is a quadrangle
    PQRS : Quadrangle 
    PQRS = isQMin→Q 
          record { ABC = PQR
                 ; ABD = PQS
                 ; ACD = PRS
                 ; BCD = Min→Triangle (record { B♯C = R♯S ; A∉BC = Q∉RS }) 
           }


    
    -- diagonal point of PQRS 
    l♯RS : l ♯ join R♯S
    l♯RS = symmetry $ C5 joinₗ R∉l

    T : Point
    T = meet l♯RS 

    -- (A and B are also diagonals)
    T≈D₁ : T ≈ diag₁ PQRS
    T≈D₁ = unq-meet _  T∈PQ T∈RS
           where  
             T∈PQ : T ∈ join _
             T∈PQ = meetₗ ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩

             T∈RS : T ∈ join R♯S
             T∈RS = meetᵣ

    A≈D₂ :  A ≈ diag₂ PQRS
    A≈D₂ = unq-meet _ (A∈SP ⇒⟨ join-comm ⟩) (A∈QR ⇒⟨ join-comm ⟩)
         where
            -- Q R A distinc and collinear
            --            {A B C}   A♯B    B♯C         A♯C     A∈BC     
            open lemma-3-collinear  Q♯A (symmetry R♯A) Q♯R (meetₗ ⇒⟨ join-comm ⟩)
                 renaming (B∈AC to A∈QR)

            open lemma-3-collinear  (symmetry A♯S)   A♯P S♯P meetₗ
                 renaming  (B∈AC to A∈SP)

    B≈D₃ :  B ≈ diag₃ PQRS
    B≈D₃ = unq-meet _ (B∈PR ⇒⟨ ≈join ⟩) (B∈SQ ⇒⟨ join-comm ⟩)
         where
             open lemma-3-collinear P♯R R♯B P♯B meetₗ -- P∈RB
                  renaming (C∈AB to B∈PR)
             open lemma-3-collinear (symmetry B♯S) B♯Q S♯Q meetᵣ -- S∈BQ
                  renaming (B∈AC to B∈SQ)
           
    T∉AB : T ∉ join A♯B
    T∉AB =  ⟨ T≈D₁ ⟩⇐ 
            IsFano.fano isFano PQRS 
            ⇒⟨  join-cong (sym A≈D₂) (sym B≈D₃) ⟩
         where open import ProjectivePlane.Fano 

    T♯C : T ♯ C
    T♯C = C0 T∉AB C∈AB

    C∉RS : C ∉ join R♯S
    C∉RS = C7-b (symmetry T♯C) l♯RS meetₗ meetᵣ C∈l

    -- some 3-tuples of distinct collinear points
    module -QRA- = lemma-3-collinear Q♯R R♯A Q♯A meetₗ    
    module -PRB- = lemma-3-collinear P♯R R♯B P♯B meetₗ
    module -SAP- = lemma-3-collinear (symmetry A♯S) A♯P  S♯P meetₗ
    module -SBQ- = lemma-3-collinear (symmetry B♯S) B♯Q  S♯Q meetᵣ

    D♯R : D ♯ R
    D♯R = symmetry $ C0 R∉AB meetᵣ
    D♯S : D ♯ S
    D♯S = symmetry  $ C0 S∉AB meetᵣ
    module -DRS- = lemma-3-collinear D♯R R♯S D♯S meetₗ

    -- Finally
    C♯D : C ♯ D
    C♯D = C0 C∉RS meetₗ
---------------------------------

flipH-RS : ∀ {A B C} {A♯B : A ♯ B} {C∈AB : C ∈ join A♯B} →
           (C ♯ A) → (C ♯ B) →
           HarmonicConf C∈AB  → HarmonicConf (C∈AB)
flipH-RS C♯A C♯B Harm-ABC = 
      record { l = l 
             ; C∈l = C∈l 
             ; l♯AB = l♯AB 
             ; R = S 
             ; R∉l = C7-b S♯P (symmetry l♯SP) joinᵣ meetᵣ joinₗ
             ; R∉AB = S∉AB 
             }
        where open HarmonicConf Harm-ABC
              open Lemma-4-6 Harm-ABC C♯A C♯B
              -- open lm-4-5-b
              open import ProjectivePlane.CompleteNPoint.Triangle PP
              l♯SP : l ♯ join S♯P
              l♯SP = ⟨ unq-join _ meetᵣ meetᵣ ⟩⇐
                     symmetry (IsTriangle.AC♯AB PQS)  
                     ⇒⟨ join-comm ⟩

module FlipH-RS
       {A B C} 
       {A♯B : A ♯ B} 
       {C∈AB : C ∈ join A♯B}
       (HConf : HarmonicConf C∈AB)
       (C♯A : C ♯ A)
       (C♯B : C ♯ B) where

-- some results about swap R-S of a Harmonic Configuration

   open HarmonicConf HConf
   module H-RS = HarmonicConf (flipH-RS C♯A C♯B HConf)
   open Lemma-4-6 HConf C♯A C♯B



   P→Q : P ≈ H-RS.Q
   P→Q = unq-meet _ (joinᵣ ⇒⟨ unq-join _ meetₗ joinₗ ⟩) meetᵣ

   Q→P : Q ≈ H-RS.P
   Q→P = unq-meet _ (joinᵣ ⇒⟨ unq-join _ meetᵣ joinₗ ⟩) meetᵣ

   S→R : S ≈ H-RS.R
   S→R = refl

   R→S : R ≈ H-RS.S
   R→S = unq-meet _ (R∈QA ⇒⟨ join-flip-cong Q→P refl ⟩) (R∈PB ⇒⟨ join-flip-cong P→Q refl ⟩)
         where R∈QA : R ∈ join Q♯A
               R∈QA = -QRA-.B∈AC
               R∈PB : R ∈ join P♯B
               R∈PB = -PRB-.B∈AC


   D→D : D ≈ H-RS.D
   D→D = meet-cong (join-flip-cong R→S S→R) refl

