{-# OPTIONS --no-eta-equality #-} 

open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Level
open import Function using (case_of_ ; _$_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Fano
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Base {a b c d e}
       (PPD : Desarguesian a b c d e)  where

open Desarguesian PPD 
  renaming (projective to PP)

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP
open import ProjectivePlane.PropertiesGeneral PP 
open import ProjectivePlane.CompleteNPoint.Quadrangle PP
           


record HarmonicConf {A B} {A♯B : A ♯ B}  
       {C} (C∈AB : C ∈ join A♯B) 
       : Set (a ⊔ c ⊔ d ⊔ e) where

  -- basic configuration to construct the harmonic conjugate of C wrt A and B
  field
    -- l is a line by C, l ♯ AB
    l    : Line
    C∈l  : C ∈ l
 
    l♯AB : l ♯ join A♯B

    -- R is outside l and AB
    R    : Point
    R∉l  : R ∉ l
    R∉AB : R ∉ join A♯B

  -- some results 
  R♯B : R ♯ B
  R♯B = C0 R∉AB joinᵣ

  R♯A : R ♯ A
  R♯A = C0 R∉AB  joinₗ
  
  RB♯l : join R♯B ♯ l
  RB♯l = C5 joinₗ R∉l

  AB♯RB : join A♯B ♯ join R♯B
  AB♯RB = symmetry $ C5 joinₗ R∉AB

  AB♯RA : join A♯B ♯ join R♯A
  AB♯RA = symmetry $ C5 joinₗ R∉AB



  RA♯l : join R♯A ♯ l
  RA♯l = C5 joinₗ R∉l

  P : Point
  P = meet RB♯l
  
  Q : Point
  Q = meet RA♯l

  P∈RB : P ∈ join R♯B
  P∈RB = meetₗ

  A∉RB : A ∉ join R♯B
  A∉RB = C7-b  A♯B AB♯RB joinᵣ joinᵣ joinₗ

  B∉RA : B ∉ join R♯A
  B∉RA = C7-b (symmetry A♯B) AB♯RA joinₗ joinᵣ joinᵣ

  A♯P : A ♯ P
  A♯P = C0 A∉RB meetₗ

  B♯Q : B ♯ Q
  B♯Q = C0 B∉RA meetₗ


  AP♯RB : join A♯P ♯ join R♯B
  AP♯RB = C5 joinₗ A∉RB

  RA♯RB : join R♯A ♯ join R♯B
  RA♯RB = C5 joinᵣ A∉RB



  BQ♯RA : join B♯Q ♯ join R♯A 
  BQ♯RA = C5 joinₗ B∉RA

  P♯R : P ♯ R
  P♯R = symmetry (C0 R∉l meetᵣ)

  Q♯R : Q ♯ R
  Q♯R = symmetry (C0 R∉l meetᵣ)

  P∉RA : P  ∉ join R♯A
  P∉RA = C7-b P♯R (symmetry RA♯RB) joinₗ joinₗ meetₗ 

  Q∉RB : Q ∉ join R♯B
  Q∉RB = C7-b Q♯R RA♯RB joinₗ joinₗ meetₗ

  BQ♯RB : join B♯Q ♯ join R♯B
  BQ♯RB = C5 joinᵣ Q∉RB

  P♯Q : P ♯ Q
  P♯Q = C0 P∉RA  meetₗ 

  AP♯RA : join A♯P ♯ join R♯A
  AP♯RA =  C5 joinᵣ P∉RA

  AP♯BQ : join A♯P ♯ join B♯Q
  AP♯BQ with cotransitivity C A♯B
  AP♯BQ | inj₁ C♯A = C5 joinₗ A∉BQ
       where   
         C∉RA : C ∉ join R♯A
         C∉RA = C7-b C♯A AB♯RA joinₗ joinᵣ C∈AB
         C♯Q  : C ♯ Q
         C♯Q = C0 C∉RA meetₗ
         Q∉AB : Q ∉ join A♯B
         Q∉AB = C7-b (symmetry C♯Q) l♯AB C∈l C∈AB meetᵣ
         AB♯BQ : join A♯B ♯ join B♯Q
         AB♯BQ = symmetry $ C5 joinᵣ Q∉AB
         A∉BQ : A ∉ join B♯Q
         A∉BQ = C7-b A♯B AB♯BQ joinᵣ joinₗ joinₗ

  AP♯BQ | inj₂ C♯B = symmetry $ C5 joinₗ B∉AP
       where   
         C∉RB : C ∉ join R♯B
         C∉RB = C7-b C♯B AB♯RB joinᵣ joinᵣ C∈AB
         C♯P  : C ♯ P
         C♯P = C0 C∉RB meetₗ
         P∉AB : P ∉ join A♯B
         P∉AB = C7-b (symmetry C♯P) l♯AB C∈l C∈AB meetᵣ
         AB♯AP : join A♯B ♯ join A♯P
         AB♯AP = symmetry $ C5 joinᵣ P∉AB
         B∉AP : B ∉ join A♯P
         B∉AP = C7-b (symmetry A♯B) AB♯AP joinₗ joinₗ joinᵣ

  S : Point
  S = meet AP♯BQ

  R∉BQ : R ∉ join B♯Q
  R∉BQ = C7-b R♯B (symmetry BQ♯RB) joinᵣ joinₗ joinₗ

  R♯S : R ♯ S
  R♯S = C0 R∉BQ meetᵣ

  RS♯AB : join R♯S ♯ join A♯B
  RS♯AB = C5 joinₗ R∉AB


  -- Finally,  here you are:  the harmonic conjugate of C:
  D : Point
  D = meet RS♯AB

open HarmonicConf using ()
     renaming (D to hconj) public


HConjugate : ∀ {A B C : Point}{A♯B : A ♯ B}  
             → {C∈AB : C ∈ join A♯B}
             → HarmonicConf C∈AB
             → Point
HConjugate  H-C∈AB = HarmonicConf.D H-C∈AB 

-----------------------------------------
-- existence of harmonic configuration --
-----------------------------------------
∃HConf : ∀ {A B C : Point}{A♯B : A ♯ B}  
         → (C∈AB : C ∈ join A♯B)
         → HarmonicConf C∈AB
∃HConf {A} {B} {C} {A♯B} C∈AB 
  = case ∃l-byC-AB♯l of
      \ { (l , C∈l , AB♯l ) → 
           case  pointOutside2 AB♯l of
           \{ (R , R∉AB , R∉l) → 
 
                     record { l =  l ; C∈l = C∈l ; l♯AB = symmetry AB♯l ; R = R ; R∉l = R∉l ; R∉AB = R∉AB }
            }
        }
  where
    open import ProjectivePlane.Duality
    open ProjectivePlane.ProjectivePlane (dual PP)
      using ()
      renaming (point₁ to line₁ ; point₂ to line₂ ;
                ∈-point₁ to ∈-line₁ ; ∈-point₂ to ∈-line₂ ;
                point-i♯j to line-i♯j)
                                         
    -- construct l ♯ AB  passing by C
    ∃l-byC-AB♯l : ∃ \ l → C ∈ l × join A♯B ♯ l
    ∃l-byC-AB♯l  =
          case cotransitivity  (join A♯B)  (proj₁ (line-i♯j C)) of 
          \{ (inj₁ AB♯l₁)  →  (line₁ C , ∈-line₁ C , AB♯l₁)
           ; (inj₂ AB♯l₂)  →  (line₂ C , ∈-line₂ C , AB♯l₂)
           }



       
