{-# OPTIONS --no-eta-equality #-} 

open import Data.Empty
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-A-3 {a b c d e}
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
              → (SP≈S'P' : join S♯P ≈ join S'♯P') 

      → ⊥

absurdity  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∉RA 
          SP≈S'P' 

   =  case-S≈S'.absurdity S≈S'
  where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
  
    open H' using ()
            renaming (l to l'; R to R';  D to D';
                    P to P'; Q to Q'; S to S')
    open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
    open Case₁-R'∉RB R'∉RB
  
  
    SQ≈S'Q' : join S♯Q ≈ join S'♯Q'
    SQ≈S'Q' SQ♯S'Q' =  C1A2.absurdity  
                         B A  C (symmetry A♯B)
                         (C∈AB ⇒⟨ join-comm ⟩)
                         (flipH HC) (flipH HC') 
                         (⟨ sym $ SymmetryHarmonic.D→D HC ⟩⇐ D♯D' ⇒⟨  SymmetryHarmonic.D→D  HC' ⟩) 
                         C♯B C♯A l♯l' R♯R'
                         ( R'∉RA ⇒⟨  ≈join ⟩) ( R'∉RB ⇒⟨  ≈join ⟩) 
                         ( ⟨ join-cong (sym $ SymmetryHarmonic.S→S HC) (sym $ SymmetryHarmonic.Q→P HC) ⟩⇐ SQ♯S'Q' 
                           ⇒⟨  join-cong (SymmetryHarmonic.S→S HC') (SymmetryHarmonic.Q→P HC') ⟩ )
                         (trans (trans 
                                 (join-cong (sym $ SymmetryHarmonic.S→S HC) (sym $ SymmetryHarmonic.P→Q HC))  
                                   SP≈S'P') 
                                  (join-cong  (SymmetryHarmonic.S→S HC') (SymmetryHarmonic.P→Q HC'))) 
       where import  ProjectivePlane.Harmonic.Uniqueness.Case1-A-2 PPD as C1A2
                
    open import ProjectivePlane.CompleteNPoint.Triangle PP

    S≈S' : S ≈ S'            
    S≈S' = begin
           S               ≈⟨ unq-meet _ joinᵣ joinᵣ ⟩
           meet (IsTriangle.AC♯BC  PQS)      ≈⟨ meet-cong ( trans (trans join-comm SP≈S'P') join-comm) 
                                                                       (( trans (trans join-comm SQ≈S'Q') join-comm)) ⟩
           meet (IsTriangle.AC♯BC HC'-4-6.PQS)  ≈⟨ sym (unq-meet _ joinᵣ joinᵣ) ⟩
           S'
           ∎
