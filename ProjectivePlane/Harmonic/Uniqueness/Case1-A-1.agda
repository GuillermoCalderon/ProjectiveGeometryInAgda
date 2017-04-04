{-# OPTIONS --no-eta-equality #-} 

open import Data.Empty
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-A-1 {a b c d e}
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

          
absurdity-O∈R'S'      
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
              → (R'∉RA : R' ∉ join R♯A)
              → (SP♯S'P' : join S♯P ♯ join S'♯P') 
              → (SQ♯S'Q' :  join S♯Q ♯ join S'♯Q') 
              -- → (O∉RS : O ∉ join R♯S) 
              → (O∈R'S' : O ∈ join H'.R♯S)

      → ⊥

absurdity-O∈R'S' A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∉RA SP♯S'P' SQ♯S'Q' O∈R'S'
         = case-S≈S'.absurdity S≈S'
 where
  open General A B C A♯B C∈AB HC HC'
  open HarmonicConf HC 
  
  open H' using ()
          renaming (l to l'; R to R';  D to D';
                    P to P'; Q to Q'; S to S')
  open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
  open Case₁-R'∉RB R'∉RB

  S≈S' :  S ≈ S'
  S≈S' S♯S' = D≈D' D♯D'
      where
        open PerspectivePQR R'∉RA 
             using ( perspectiveCenter-PQR ; O∈RR'; O♯R ; O♯R' )
    

        open PerspectivePQS R'∉RA SP♯S'P' SQ♯S'Q' S♯S'
                 using (perspectiveCenter-PQS ; O∈SS' ; O♯S ; O♯S')

        open lemma-3-collinear O♯R' H'.R♯S O♯S' O∈R'S'
                     renaming ( BC≈AB to R'S'≈OR'
                              ; AC≈AB to OS'≈OR'
                              ; BC≈AC to R'S'≈OS'
                              )

        open lemma-3-collinear O♯R R♯R' O♯R' O∈RR'
                     renaming ( BC≈AB to RR'≈OR
                              ; AC≈AB to OR'≈OR
                              ; BC≈AC to RR'≈OR'
                              )
        open lemma-3-collinear O♯S S♯S' O♯S' O∈SS'
                     renaming ( BC≈AB to SS'≈OS
                              ; AC≈AB to OS'≈OS
                              ; BC≈AC to SS'≈OS'
                              )
        R∈R'S' : R ∈ join H'.R♯S
        R∈R'S' =  joinᵣ ⇒⟨ begin
                                join O♯R    ≈⟨ sym OR'≈OR ⟩ 
                                join O♯R'   ≈⟨ sym R'S'≈OR' ⟩
                                join H'.R♯S ∎
                             ⟩

                              
        S∈R'S' : S ∈ join H'.R♯S
        S∈R'S' =  joinᵣ ⇒⟨ begin
                                join O♯S    ≈⟨ sym OS'≈OS ⟩ 
                                join O♯S'   ≈⟨ sym R'S'≈OS' ⟩
                                join H'.R♯S ∎
                             ⟩
        RS≈R'S' : join R♯S ≈ join H'.R♯S
        RS≈R'S' = sym $ unq-join _ R∈R'S' S∈R'S'

        D≈D' : D ≈ D'
        D≈D' = unq-meet _ (meetₗ ⇒⟨ RS≈R'S' ⟩) meetᵣ

-- by symmetry        
absurdity-O∈RS      
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
              → (R'∉RA : R' ∉ join R♯A)
              → (SP♯S'P' : join S♯P ♯ join S'♯P') 
              → (SQ♯S'Q' :  join S♯Q ♯ join S'♯Q') 
              --
              → (O∈RS : O ∈ join R♯S)

      → ⊥

absurdity-O∈RS A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∉RA SP♯S'P' SQ♯S'Q' O∈RS
         =  absurdity-O∈R'S' 
              A B C A♯B C∈AB HC' HC 
              (symmetry D♯D') C♯A C♯B (symmetry l♯l') (symmetry R♯R') 
              (lemma-triangle.B∉AC  R'∉RB ⇒⟨ ≈join ⟩) (lemma-triangle.B∉AC  R'∉RA ⇒⟨ ≈join ⟩) 
              (symmetry SP♯S'P') (symmetry SQ♯S'Q') (⟨ meet-cong join-comm join-comm ⟩⇐  O∈RS)
