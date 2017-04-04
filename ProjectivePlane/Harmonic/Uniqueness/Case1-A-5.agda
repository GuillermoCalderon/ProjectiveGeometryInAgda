open import Data.Empty
open import Relation.Nullary
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-A-5 {a b c d e}
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
        → (R♯R' : R ♯ R')
        →  let
             open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
           in
              (R'∈RB : R' ∈ join R♯B)
              → ⊥

absurdity  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∈RB
          
    =  R≈R' R♯R'
       where
         open General A B C A♯B C∈AB HC HC'
         open HarmonicConf HC 
         open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
         open Case₁ D♯D' C♯A C♯B l♯l' R♯R'

         ¬R'∉RA : ¬ (R' ∉ join R♯A)
         ¬R'∉RA R'∉RA 
           = C1A4.absurdity
                          B A  C (symmetry A♯B)
                          (C∈AB ⇒⟨ join-comm ⟩)
                          (flipH HC) (flipH HC') 
                          (⟨ sym $ SymmetryHarmonic.D→D HC ⟩⇐ D♯D' ⇒⟨  SymmetryHarmonic.D→D  HC' ⟩) 
                          C♯B C♯A l♯l' R♯R'
                          ( R'∉RA ⇒⟨  ≈join ⟩) ( R'∈RB ⇒⟨  ≈join ⟩) 
              
                where open import ProjectivePlane.Harmonic.Uniqueness.Case1-A-4 PPD as C1A4

         R'∈RA : R' ∈ join R♯A
         R'∈RA = C6 ¬R'∉RA

         R≈R' : R ≈ R'
         R≈R' = begin 
                R           ≈⟨ unq-meet _  joinₗ joinₗ ⟩
                meet RA♯RB  ≈⟨  sym (unq-meet _ R'∈RA R'∈RB) ⟩
                R'
                ∎
