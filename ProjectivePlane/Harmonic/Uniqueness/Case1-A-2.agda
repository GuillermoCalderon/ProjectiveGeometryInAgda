{-# OPTIONS --no-eta-equality #-} 

open import Data.Empty
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Case1-A-2 {a b c d e}
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
              → (SQ≈S'Q' :  join S♯Q ≈ join S'♯Q') 

      → ⊥

absurdity  A B C A♯B C∈AB HC HC' 
          D♯D' C♯A C♯B l♯l' R♯R' 
          R'∉RB
          R'∉RA SP♯S'P' 
          SQ≈S'Q' 
   =  case-S≈S'.absurdity S≈S'
  where
    open General A B C A♯B C∈AB HC HC'
    open HarmonicConf HC 
  
    open H' using ()
            renaming (l to l'; R to R';  D to D';
                    P to P'; Q to Q'; S to S')
    open Case₁ D♯D' C♯A C♯B l♯l' R♯R'
    open Case₁-R'∉RB R'∉RB

    open PerspectivePQR R'∉RA 
            using ( RB♯P'R'
                  ; perspectiveCenter-PQR
                  ; O∈RR' ; O∈QQ' ; O∉PR ; O∉P'R' 
                  ; O♯R'; O♯P; O♯P'
                  )
  
    QQ'≈S'Q' : join Q♯Q' ≈ join S'♯Q'
    QQ'≈S'Q' = sym $ unq-join _ (joinᵣ ⇒⟨ SQ≈S'Q' ⟩) joinᵣ
  
      
    QQ'≈SQ : join Q♯Q' ≈ join S♯Q
    QQ'≈SQ   = begin
                 join Q♯Q'  ≈⟨ sym $ unq-join _ (joinᵣ ⇒⟨ SQ≈S'Q' ⟩) joinᵣ ⟩
                 join S'♯Q' ≈⟨ sym SQ≈S'Q' ⟩ 
                 join S♯Q   
                 ∎
    BQ≈SQ  : join B♯Q ≈ join S♯Q
    BQ≈SQ =  unq-join _ meetᵣ joinᵣ

    BQ≈BQ' : join B♯Q ≈ join H'.B♯Q
    BQ≈BQ' = unq-join _ joinₗ (joinᵣ ⇒⟨ trans QQ'≈SQ (sym BQ≈SQ) ⟩)
        

  
    case-O♯S♯S' :  (S♯S' : S ♯ S')
                   (O♯S  : O ♯ S)
                   (O♯S' : O ♯ S')
                → ⊥
    case-O♯S♯S' S♯S' O♯S O♯S' = D≈D' D♯D'
     where
       open import ProjectivePlane.CompleteNPoint PP
       open import ProjectivePlane.CompleteNPoint.Triangle PP 
       open import ProjectivePlane.CompleteNPoint.Triangle.Perspective PP as TP
       open import Data.Fin
       open import Data.Fin.Setoid
   
       QQ'≈SS' :  join Q♯Q' ≈ join S♯S'
       QQ'≈SS' = unq-join _ (joinₗ ⇒⟨ sym QQ'≈SQ ⟩) (joinₗ ⇒⟨ trans (sym SQ≈S'Q') (sym QQ'≈SQ) ⟩)
  
  
       O∈SS' : O ∈ join S♯S'
       O∈SS'  = O∈QQ' ⇒⟨ QQ'≈SS' ⟩
  
       import ProjectivePlane.CompleteNPoint.Quadrangle PP as Q 
  
       PS♯SQ : join (symmetry S♯P) ♯ join S♯Q
       PS♯SQ = ⟨ ≈join ⟩⇐ adjacent♯ PQRS {i♯j =  Q.0♯3} {symmetry Q.1♯3} {Q.0♯1} ⇒⟨ ≈join ⟩
  
       RS♯SQ : join R♯S ♯ join S♯Q
       RS♯SQ = ⟨ ≈join ⟩⇐ adjacent♯ PQRS {i♯j =  Q.2♯3} {symmetry Q.1♯3} {symmetry Q.1♯2} ⇒⟨ ≈join ⟩
  
       O∉PS : O ∉ join (symmetry S♯P)
       O∉PS = C7-b O♯S (symmetry PS♯SQ) joinₗ joinᵣ (O∈SS' ⇒⟨ trans (sym QQ'≈SS') QQ'≈SQ ⟩)
              
       O∉RS : O ∉ join R♯S
       O∉RS = C7-b O♯S (symmetry RS♯SQ) joinₗ joinᵣ ((O∈SS' ⇒⟨ trans (sym QQ'≈SS') QQ'≈SQ ⟩))
                 
  
       P'S'♯S'Q' : join (symmetry S'♯P') ♯ join S'♯Q'
       P'S'♯S'Q' =  ⟨ ≈join ⟩⇐ adjacent♯ HC'-4-6.PQRS {i♯j =  Q.0♯3} {symmetry Q.1♯3} {Q.0♯1} ⇒⟨ ≈join ⟩ 
  
                 
       O∉P'S' : O ∉ join (symmetry HC'-4-6.S♯P)
       O∉P'S' = C7-b O♯S' (symmetry P'S'♯S'Q') joinₗ joinᵣ (O∈SS' ⇒⟨ trans (sym QQ'≈SS') QQ'≈S'Q' ⟩)
  
       R'S'♯S'Q' : join H'.R♯S ♯ join S'♯Q'
       R'S'♯S'Q' = ⟨ ≈join ⟩⇐ adjacent♯ HC'-4-6.PQRS {i♯j =  Q.2♯3} {symmetry Q.1♯3} {symmetry Q.1♯2} ⇒⟨ ≈join ⟩
                 
       O∉R'S' : O ∉ join H'.R♯S
       O∉R'S' = C7-b O♯S' (symmetry R'S'♯S'Q') joinₗ joinᵣ ((O∈SS' ⇒⟨ trans (sym QQ'≈SS') QQ'≈S'Q' ⟩))
   
  
       tPRS  = triangle→Poly $ isT2T PRS
       t'PRS = triangle→Poly $ isT2T HC'-4-6.PRS
       perspectiveCenter-PRS : ArePerspectiveCenter tPRS t'PRS 
       perspectiveCenter-PRS 
         = toArePerspectiveCenter 
           (record
              { Center = O
              ; areDistinct = areDistinct
              ; perspective = persp
              ; O∉T-01 =  O∉PR  ⇒⟨  ≈join ⟩
              ; O∉T-02 = O∉PS ⇒⟨ ≈join ⟩  
              ; O∉T-12 = O∉RS ⇒⟨ ≈join ⟩ 
              ; O∉T'-01 = O∉P'R' ⇒⟨ ≈join ⟩
              ; O∉T'-02 = O∉P'S' ⇒⟨ ≈join ⟩
              ; O∉T'-12 = O∉R'S' ⇒⟨ ≈join ⟩
              })
  
         where 
           areDistinct : AreDistinct tPRS t'PRS
           areDistinct 
                = toAreDistinct 
                     record
                     { vrt-0 = P♯P'
                     ; vrt-1 = R♯R'
                     ; vrt-2 = S♯S'
                     ; sd-01 = ⟨  sym $ unq-join _ meetₗ joinₗ ⟩⇐ RB♯P'R' ⇒⟨ ≈join ⟩ 
                     ; sd-02 =  ⟨  join-comm ⟩⇐ SP♯S'P' ⇒⟨ join-comm ⟩
                     ; sd-12 = RS♯R'S'
                     }
           open AreDistinct areDistinct
           persp : ∀ i → O ∈ join (vrt♯ i)
           persp zero = meetₗ
           persp (suc zero) = O∈RR'
           persp (suc (suc zero)) = O∈QQ' ⇒⟨ QQ'≈SS' ⟩
           persp (suc (suc (suc ())))
   
       perspectiveAxis-PRS :  ArePerspectiveAxis tPRS t'PRS
       perspectiveAxis-PRS = desargues _ _  perspectiveCenter-PRS
       module apa-PRS =  ArePerspectiveAxis perspectiveAxis-PRS 
       axisPRS≈AB : apa-PRS.axis  ≈ join A♯B
       axisPRS≈AB = unq-join _ (⟨ unq-meet _ (joinₗ ⇒⟨ unq-join _ joinᵣ meetₗ ⟩) (joinₗ ⇒⟨ unq-join _ joinᵣ meetₗ ⟩) 
                                   ⟩⇐ apa-PRS.perspective 0♯2) 
                                 ( ⟨ unq-meet _ (joinᵣ ⇒⟨ unq-join _ meetₗ  joinₗ ⟩) (joinᵣ ⇒⟨ unq-join _ meetₗ  joinₗ ⟩) 
                                   ⟩⇐ apa-PRS.perspective 0♯1)
  
  
       D≈D' : D ≈ D'
       D≈D' = begin
                  D             
                    ≈⟨ sym $ unq-meet _ meetₗ ( apa-PRS.perspective 1♯2 ⇒⟨ axisPRS≈AB ⟩) ⟩
                  meet (AreDistinct.sd♯ apa-PRS.areDistinct 1♯2)  
                    ≈⟨ unq-meet _ meetᵣ ( apa-PRS.perspective 1♯2 ⇒⟨ axisPRS≈AB ⟩) ⟩
                  D'
               ∎

    S≈S' : S ≈ S'
    S≈S' S♯S' =  S≈S'₂ S♯S'
      where 
         O≈S : O ≈ S 
         O≈S O♯S =  S≈S'₁ S♯S' 
             where O≈S' : O ≈ S'
                   O≈S' O♯S' = case-O♯S♯S' S♯S' O♯S O♯S'
                   
   
                   open lemma-3-collinear O♯P P♯P' O♯P' meetₗ
                        renaming ( BC≈AB to PP''≈OP
                                 ; AC≈AB to OP'≈OP
                                 ; BC≈AC to PP'≈OP'
                                 )
                   open lemma-3-collinear (symmetry HC'-4-6.A♯S)   H'.A♯P S'♯P' meetₗ -- S'∈AP'
                        renaming ( BC≈AB to AP'≈S'A
                                 ; AC≈AB to S'P'≈S'A
                                 ; BC≈AC to AP'≈S'P'
                                 )

                   AP≈AP' :  join A♯P ≈ join H'.A♯P
                   AP≈AP' = sym $ unq-join _ 
                                          joinₗ
                                          (joinₗ  ⇒⟨ begin 
                                                       join P♯P'   ≈⟨ PP'≈OP' ⟩
                                                       join O♯P'   ≈⟨ join-cong O≈S' refl ⟩
                                                       join S'♯P'  ≈⟨ sym AP'≈S'P' ⟩
                                                       join H'.A♯P  ∎  
                                                    ⟩)
                                       
                   S≈S'₁ : S ≈ S'       
                   S≈S'₁ = unq-meet _ (meetₗ ⇒⟨  AP≈AP' ⟩) ( meetᵣ ⇒⟨ BQ≈BQ' ⟩)


         open lemma-3-collinear O♯P P♯P' O♯P' meetₗ
              renaming ( BC≈AB to PP'≈OP
                       ; AC≈AB to OP'≈OP
                       ; BC≈AC to PP'≈OP'
                       )
         open lemma-3-collinear (symmetry A♯S)  A♯P S♯P meetₗ -- S∈AP
                        renaming ( BC≈AB to AP≈SA
                                 ; AC≈AB to SP≈SA
                                 ; BC≈AC to AP≈SP
                                 )


         AP'≈AP :  join H'.A♯P ≈ join A♯P
         AP'≈AP = sym $ unq-join _ 
                                 joinₗ
                                 (joinᵣ  ⇒⟨ begin 
                                            join P♯P'  ≈⟨ PP'≈OP ⟩
                                            join O♯P   ≈⟨ join-cong O≈S refl ⟩
                                            join S♯P   ≈⟨ sym AP≈SP ⟩
                                            join A♯P  ∎  
                                 ⟩)
                                       
         S≈S'₂ : S ≈ S'       
         S≈S'₂ = unq-meet _ (meetₗ ⇒⟨  sym AP'≈AP ⟩) ( meetᵣ ⇒⟨ BQ≈BQ' ⟩)    
