open import Data.Empty
open import Relation.Nullary
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Main {a b c d e}
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


uniqueness :  (A B C : Point)
              → (A♯B   : A ♯ B)
              → (C∈AB  : C ∈ join A♯B) 
              → (HC HC' : HarmonicConf C∈AB)
              → HConjugate HC ≈ HConjugate HC'
uniqueness A B C A♯B C∈AB HC HC' D♯D' = D≈D' D♯D' 
  where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
    open H' using ()
                 renaming (l to l'; R to R';  D to D';
                           P to P'; Q to Q'; S to S')
    D≈D' : D ≈ D'
    D≈D' D♯D' 
      = let
          D≈D' : D ≈ D'
          D≈D' = begin D ≈⟨ sym (Harm-C≈A HC C≈A) ⟩ A  ≈⟨ Harm-C≈A HC' C≈A ⟩ D' ∎ 
        in 
          D≈D' D♯D'
      where
        C≈A  : C ≈ A
        C≈A C♯A 
          = let
              D≈D' : D ≈ D'
              D≈D' = begin D ≈⟨ sym (Harm-C≈B HC C≈B) ⟩ B  ≈⟨ Harm-C≈B HC' C≈B ⟩ D' ∎
            in 
               D≈D' D♯D'
          where 
            C≈B  : C ≈ B
            C≈B C♯B =  C1C.absurdity 
                                A B C A♯B C∈AB HC HC' 
                                D♯D' C♯A C♯B l≈l'

              where
                open import ProjectivePlane.Harmonic.Uniqueness.Case1-C PPD as C1C
                l≈l' : l ≈ l'
                l≈l' l♯l' = C1B.absurdity 
                                A B C A♯B C∈AB HC HC' 
                                D♯D' C♯A C♯B l♯l' R≈R' 
                  where 
                    open import ProjectivePlane.Harmonic.Uniqueness.Case1-B PPD as C1B
                    R≈R' : R ≈ R'
                    R≈R' R♯R' = 
                         let R'∈RB = C6 ¬R'∉RB
                             R'∉RA : R' ∉ join R♯A
                             R'∉RA = C7-b (symmetry R♯R') (symmetry RA♯RB) joinₗ joinₗ R'∈RB
                          in  C1A4.absurdity
                                   B A  C (symmetry A♯B)
                                   (C∈AB ⇒⟨ join-comm ⟩)
                                   (flipH HC) (flipH HC') 
                                   (⟨ sym $ SymmetryHarmonic.D→D HC ⟩⇐ D♯D' ⇒⟨  SymmetryHarmonic.D→D  HC' ⟩) 
                                   C♯B C♯A l♯l' R♯R'
                                   ( R'∉RA ⇒⟨  ≈join ⟩) ( R'∈RB ⇒⟨  ≈join ⟩) 

                      where
                        open import ProjectivePlane.Harmonic.Uniqueness.Case1-A-4 PPD as C1A4
                        open Case₁ D♯D' C♯A C♯B l♯l' R♯R' 
                        ¬R'∉RB : ¬ (R' ∉ join R♯B)
                        ¬R'∉RB R'∉RB = C1A4.absurdity
                                           A B C A♯B C∈AB HC HC' 
                                           D♯D' C♯A C♯B l♯l' R♯R' 
                                           R'∉RB
                                           (C6 ¬R'∉RA)  
                          where
                            open  Case₁-R'∉RB R'∉RB
                            ¬R'∉RA : ¬(R' ∉ join R♯A)
                            ¬R'∉RA R'∉RA =  C1A3.absurdity
                                                 A B C A♯B C∈AB HC HC' 
                                                 D♯D' C♯A C♯B l♯l' R♯R' 
                                                 R'∉RB
                                                 R'∉RA SP≈S'P'
                              where
                                open import ProjectivePlane.Harmonic.Uniqueness.Case1-A-3 PPD as C1A3
                                SP≈S'P' : join S♯P ≈ join S'♯P'
                                SP≈S'P' SP♯S'P' = C1A2.absurdity
                                                       A B C A♯B C∈AB HC HC' 
                                                       D♯D' C♯A C♯B l♯l' R♯R' 
                                                       R'∉RB
                                                       R'∉RA SP♯S'P' SQ≈S'Q' 
                                  where
                                    open import ProjectivePlane.Harmonic.Uniqueness.Case1-A-2 PPD as C1A2
                                    SQ≈S'Q' :  join S♯Q ≈ join S'♯Q'
                                    SQ≈S'Q' SQ♯S'Q' = C1A1.absurdity-O∈RS
                                                         A B C A♯B C∈AB HC HC' 
                                                          D♯D' C♯A C♯B l♯l' R♯R' 
                                                          R'∉RB
                                                          R'∉RA SP♯S'P' SQ♯S'Q' (C6 ¬O∉RS)

                                      where
                                        open import ProjectivePlane.Harmonic.Uniqueness.Case1-A-1 PPD as C1A1
                                        ¬O∉RS : ¬ (O ∉ join R♯S)
                                        ¬O∉RS O∉RS = C1A1.absurdity-O∈R'S'
                                                          A B C A♯B C∈AB HC HC' 
                                                          D♯D' C♯A C♯B l♯l' R♯R' 
                                                          R'∉RB
                                                          R'∉RA SP♯S'P' SQ♯S'Q' (C6 ¬O∉R'S')
                                          where 
                                            ¬O∉R'S' : ¬ (O ∉ join H'.R♯S)
                                            ¬O∉R'S' O∉R'S' = case-S≈S'.absurdity S≈S'
                                              where
                                                S≈S' : S ≈ S'
                                                S≈S' S♯S' = C1A.absurdity 
                                                                A B C A♯B C∈AB HC HC' 
                                                                D♯D' C♯A C♯B l♯l' R♯R' 
                                                                R'∉RB
                                                                R'∉RA SP♯S'P' SQ♯S'Q' O∉RS O∉R'S' S♯S'
                                                  where
                                                    open import ProjectivePlane.Harmonic.Uniqueness.Case1-A PPD as C1A
