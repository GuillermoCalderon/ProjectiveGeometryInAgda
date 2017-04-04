{-# OPTIONS --no-eta-equality #-} 

open import Relation.Nullary
open import Data.Empty
open import Level
open import Function using (_$_ ; case_of_)
open import Relation.Binary.Apartness
open import ProjectivePlane
open import ProjectivePlane.Desargues


module ProjectivePlane.Harmonic.Uniqueness.Base {a b c d e}
       (PPD : Desarguesian a b c d e)  where


open Desarguesian PPD 
     renaming (projective to PP)

open ProjectivePlane.Setoid♯Instances PP
open ProjectivePlane.Rel♯Instances PP
open ProjectivePlane.EqReasoningInstances PP

open import ProjectivePlane.PropertiesGeneral PP 
open import  ProjectivePlane.Harmonic.Base PPD
open import ProjectivePlane.Harmonic.Lemmas PPD
          



   

record  GeneralHypothesis : Set ( a ⊔ b ⊔ c ⊔ d ⊔ e) where 

  field
    A B C : Point
    A♯B   : A ♯ B
    C∈AB  : C ∈ join A♯B 
    HC HC' : HarmonicConf C∈AB
 

         
record  Case₁ : Set ( a ⊔ b ⊔ c ⊔ d ⊔ e) where 
  field
    GH : GeneralHypothesis
  open GeneralHypothesis GH

  open HarmonicConf HC 
  module H' = HarmonicConf HC'
  open H'   using ()
           renaming (l to l'; R to R';  D to D';
                     P to P'; Q to Q'; S to S')
  field
    D♯D' : D ♯ D'
    C♯A  : C ♯ A
    C♯B  : C ♯ B
    l♯l' : l ♯ l'
    R♯R' : R ♯ R'
       --

  open Lemma-4-6 HC C♯A C♯B  public
  module HC'-4-6 = Lemma-4-6 HC' C♯A C♯B
 

  D∉R'S' : D ∉ join H'.R♯S
  D∉R'S' = C7-b D♯D' (symmetry H'.RS♯AB) meetᵣ meetₗ meetᵣ

  
  RS♯R'S' : join R♯S ♯ join H'.R♯S
  RS♯R'S' = C5 meetₗ  D∉R'S'
  
  C≈l∙l' :  C ≈ meet l♯l'
  C≈l∙l' = unq-meet _ C∈l H'.C∈l

  P♯C : P ♯ C
  P♯C = C0 P∉AB C∈AB

  P♯l∙l' : P ♯ meet l♯l'
  P♯l∙l' = P♯C ⇒⟨ C≈l∙l' ⟩ 

  P∉l' : P ∉ l'
  P∉l' = C7-a _ P♯l∙l' meetᵣ

  P♯P' : P ♯ P'
  P♯P' = C0 P∉l' meetᵣ

  Q♯C : Q ♯ C
  Q♯C = C0 Q∉AB C∈AB

  Q∉l' : Q ∉ l'
  Q∉l' = C7-a _ (Q♯C ⇒⟨ C≈l∙l' ⟩) meetᵣ

  Q♯Q' : Q ♯ Q'
  Q♯Q' = C0 Q∉l' meetᵣ

  PQ≈l : join P♯Q ≈ l
  PQ≈l = sym (unq-join _ meetᵣ meetᵣ)

  P'Q'≈l' : join H'.P♯Q ≈ l'
  P'Q'≈l' = sym (unq-join _ meetᵣ meetᵣ)

  PQ♯P'Q' : join P♯Q ♯ join H'.P♯Q
  PQ♯P'Q' =  ⟨ PQ≈l ⟩⇐ l♯l' ⇒⟨ sym P'Q'≈l' ⟩

  Q'♯C : Q' ♯ C
  Q'♯C = C0 HC'-4-6.Q∉AB C∈AB

  
  Q'∉PQ : Q' ∉ join P♯Q
  Q'∉PQ = C7-b Q'♯C ( symmetry PQ♯P'Q') (H'.C∈l ⇒⟨  sym P'Q'≈l' ⟩) (C∈l ⇒⟨ sym PQ≈l ⟩) joinᵣ

  QQ'♯PQ : join Q♯Q' ♯ join P♯Q
  QQ'♯PQ = C5 joinᵣ Q'∉PQ

  P∉QQ' : P ∉ join Q♯Q'
  P∉QQ' = C7-b P♯Q (symmetry QQ'♯PQ) joinᵣ joinₗ joinₗ

  PP'♯QQ' : join P♯P' ♯ join Q♯Q'
  PP'♯QQ'  = C5 joinₗ P∉QQ'

  O : Point
  O = meet PP'♯QQ'

  -- R'∉RA|RB : R' ∉ join R♯A ⊎ R' ∉ join R♯B 
  -- R'∉RA|RB = C7 RA♯RB ( symmetry R♯R' ⇒⟨ unq-meet _ joinₗ joinₗ ⟩)  

  S'♯P' = HC'-4-6.S♯P
  S'♯Q' = HC'-4-6.S♯Q


record Case₁-R'∉RB  : Set ( a ⊔ b ⊔ c ⊔ d ⊔ e)  where
  field
    C1 : Case₁
  open Case₁ C1

  open GeneralHypothesis GH

  open HarmonicConf HC 
  open H'   using ()
           renaming (l to l'; R to R';  D to D';
                     P to P'; Q to Q'; S to S')
  field
    R'∉RB : R' ∉ join R♯B

  open import ProjectivePlane.Polygon PP
  open import ProjectivePlane.Polygon.Triangle PP 
  open import ProjectivePlane.Polygon.Triangle.Perspective PP as TP
  open import Data.Fin
  open import Data.Fin.Setoid

  module PerspectivePQR 
              (R'∉RA : R' ∉ join R♯A)
              where
         tPQR  = triangle→Poly $ isT2T PQR
         t'PQR = triangle→Poly $ isT2T HC'-4-6.PQR



         RA♯R'A' : join R♯A ♯ join H'.R♯A
         RA♯R'A' = symmetry $ C5 joinₗ R'∉RA

         RB♯P'R' : join R♯B ♯ join H'.P♯R
         RB♯P'R' = symmetry $ C5 joinᵣ R'∉RB


         perspectiveAxe-PQR : ArePerspectiveAxe tPQR t'PQR
         perspectiveAxe-PQR 
           = toPerspectiveAxe record
           { axe = join A♯B
           ; areDistinct 
             = toAreDistinct (record
               { vrt-0 = P♯P'
               ; vrt-1 = Q♯Q'
               ; vrt-2 = R♯R'
               ; sd-01 = ⟨ sym $ unq-join _ meetᵣ meetᵣ ⟩⇐ l♯l' ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩
               ; sd-02 = ⟨  sym $ unq-join _ meetₗ joinₗ ⟩⇐ RB♯P'R' ⇒⟨ ≈join ⟩
               ; sd-12 = ⟨ sym $ unq-join _ meetₗ joinₗ ⟩⇐ RA♯R'A' ⇒⟨ unq-join _ meetₗ joinₗ ⟩
               })
           ; axe-∉-T = λ {i} → t-∉-AB i
           ; axe-∉-T' = λ {i} → t'-∉-AB i
           ; persp01 = ⟨ sym (unq-meet _ 
                              ( C∈l    ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩) 
                              ( H'.C∈l ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩)) 
                       ⟩⇐ C∈AB
           ; persp02 = ⟨ sym (unq-meet _ (joinᵣ ⇒⟨ unq-join _ meetₗ joinₗ ⟩) 
                                         (joinᵣ ⇒⟨ unq-join _ meetₗ joinₗ ⟩)) 
                       ⟩⇐ joinᵣ
           ; persp12 = ⟨ sym (unq-meet _ (joinᵣ ⇒⟨ unq-join _ meetₗ joinₗ ⟩) 
                                         (joinᵣ ⇒⟨ unq-join _ meetₗ joinₗ ⟩) ) 
                       ⟩⇐ joinₗ
           }

                    where
                       t-∉-AB : (i : Fin 3) → tPQR $∙ i ∉ join A♯B
                       t-∉-AB zero = P∉AB
                       t-∉-AB (suc zero)    = Q∉AB
                       t-∉-AB (suc (suc zero))  = R∉AB
                       t-∉-AB (suc (suc (suc ())))

                       t'-∉-AB : (i : Fin 3) → t'PQR $∙ i ∉ join A♯B
                       t'-∉-AB zero = HC'-4-6.P∉AB
                       t'-∉-AB (suc zero)    = HC'-4-6.Q∉AB
                       t'-∉-AB (suc (suc zero))  = H'.R∉AB
                       t'-∉-AB (suc (suc (suc ())))


         perspectiveCenter-PQR :  ArePerspectiveCenter tPQR t'PQR
         perspectiveCenter-PQR = desargues← _ _  perspectiveAxe-PQR

         -- some useful corolaries

         -- center of perspectivity
         -- O = meet PP'♯QQ' (above defined)
         O∈RR' : O ∈ join R♯R'
         O∈RR' = ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.perspective perspectiveCenter-PQR  `2

         O∈QQ' : O ∈ join Q♯Q'
         O∈QQ' =  ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.perspective perspectiveCenter-PQR  `1

         O∉P'R' : O ∉ join H'.P♯R
         O∉P'R' = ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.Center-∉-T' perspectiveCenter-PQR {i♯j = 0♯2} ⇒⟨ ≈join ⟩
         O∉PR   : O ∉ join P♯R
         O∉PR   = ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.Center-∉-T perspectiveCenter-PQR {i♯j = 0♯2} ⇒⟨ ≈join ⟩

         
         O♯R' : O ♯ R'
         O♯R' = C0 O∉P'R' joinᵣ

         O♯R : O ♯ R
         O♯R = C0 O∉PR joinᵣ

         O♯P  =  C0 O∉PR joinₗ
         O♯P' =  C0 O∉P'R' joinₗ
  -------- end PerspectivePQR

  module PerspectivePQS
                  (R'∉RA : R' ∉ join R♯A)
                  (SP♯S'P' : join S♯P ♯ join S'♯P') 
                  (SQ♯S'Q' :  join S♯Q ♯ join S'♯Q') 
                  (S♯S' : S ♯ S')
                  where
           


              tPQS  = triangle→Poly $ isT2T PQS
              t'PQS = triangle→Poly $ isT2T HC'-4-6.PQS
              perspectiveAxe-PQS : ArePerspectiveAxe tPQS t'PQS
              perspectiveAxe-PQS 
                = toPerspectiveAxe 
                  (record
                    { axe = join A♯B
                    ; areDistinct = 
                         toAreDistinct (record
                                          { vrt-0 = P♯P'
                                          ; vrt-1 = Q♯Q'
                                          ; vrt-2 = S♯S'
                                          ; sd-01 = ⟨ sym $ unq-join _ meetᵣ meetᵣ ⟩⇐ l♯l' ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩
                                          ; sd-02 = ⟨  join-comm ⟩⇐ SP♯S'P' ⇒⟨ join-comm ⟩
                                          ; sd-12 = ⟨ join-comm ⟩⇐ SQ♯S'Q' ⇒⟨ join-comm ⟩ 
                                          })
                                  
                    ; axe-∉-T  = λ {i} → t-∉-AB i 
                    ; axe-∉-T' = λ {i} → t'-∉-AB i
                    ; persp01 =  ⟨ sym (unq-meet _ 
                                          ( C∈l    ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩) 
                                          ( H'.C∈l ⇒⟨ unq-join _ meetᵣ meetᵣ ⟩)) 
                                 ⟩⇐ C∈AB 
                    ; persp02 = ⟨ sym (unq-meet _ (joinₗ ⇒⟨ unq-join _ joinᵣ meetₗ ⟩) 
                                                  (joinₗ ⇒⟨ unq-join _ joinᵣ meetₗ ⟩)) 
                                ⟩⇐ joinₗ
                    ; persp12 = ⟨ sym (unq-meet _ (joinₗ ⇒⟨ unq-join _ joinᵣ meetᵣ ⟩ ) 
                                                                            (joinₗ ⇒⟨ unq-join _ joinᵣ meetᵣ ⟩)) 
                                                          ⟩⇐ joinᵣ
                    }
                  )


                 where
                   t-∉-AB : (i : Fin 3) → tPQS $∙ i ∉ join A♯B
                   t-∉-AB zero =  P∉AB
                   t-∉-AB (suc zero)    = Q∉AB
                   t-∉-AB (suc (suc zero))  = S∉AB
                   t-∉-AB (suc (suc (suc ())))

                   t'-∉-AB : (i : Fin 3) → t'PQS $∙ i ∉ join A♯B
                   t'-∉-AB zero = HC'-4-6.P∉AB
                   t'-∉-AB (suc zero)    = HC'-4-6.Q∉AB
                   t'-∉-AB (suc (suc zero))  = HC'-4-6.S∉AB
                   t'-∉-AB (suc (suc (suc ())))

              perspectiveCenter-PQS :  ArePerspectiveCenter tPQS t'PQS
              perspectiveCenter-PQS = desargues← _ _  perspectiveAxe-PQS

              O∈SS' : O ∈ join S♯S'
              O∈SS' = ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.perspective perspectiveCenter-PQS  `2

              O∉S'P' : O ∉ join S'♯P'
              O∉S'P' = ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.Center-∉-T' perspectiveCenter-PQS {i♯j = symmetry 0♯2} ⇒⟨ ≈join ⟩

              O∉SP : O ∉ join S♯P
              O∉SP = ⟨ ≈meet ⟩⇐ ArePerspectiveCenter.Center-∉-T perspectiveCenter-PQS {i♯j = symmetry 0♯2} ⇒⟨ ≈join ⟩

              O♯S' : O ♯ S'
              O♯S' = C0 O∉S'P' joinₗ

              O♯S : O ♯ S
              O♯S = C0 O∉SP joinₗ

  module case-S≈S' (S≈S' : S ≈ S')
                  where
             -- conlusions by assuming only S≈S' 

             AS≈AS' : join A♯S ≈ join HC'-4-6.A♯S
             AS≈AS' = join-cong refl S≈S'

             SP≈S'P' : join S♯P ≈ join S'♯P'
             SP≈S'P' =  begin
                        join S♯P  ≈⟨ sym $ unq-join _ meetₗ joinᵣ ⟩
                        join A♯P  ≈⟨ unq-join _ joinₗ meetₗ ⟩
                        join A♯S  ≈⟨ AS≈AS' ⟩
                        join HC'-4-6.A♯S ≈⟨ sym $ unq-join _ joinₗ meetₗ ⟩
                        join H'.A♯P  ≈⟨ unq-join _ meetₗ joinᵣ ⟩
                        join S'♯P'
                        ∎

             BS≈BS' : join B♯S ≈ join HC'-4-6.B♯S
             BS≈BS' = join-cong refl S≈S'

             SQ≈S'Q' : join S♯Q ≈ join S'♯Q'
             SQ≈S'Q' =  begin
                        join S♯Q  ≈⟨ sym $ unq-join _ meetᵣ joinᵣ ⟩
                        join B♯Q  ≈⟨ unq-join _ joinₗ meetᵣ ⟩
                        join B♯S  ≈⟨ BS≈BS' ⟩
                        join HC'-4-6.B♯S ≈⟨ sym $ unq-join _ joinₗ meetᵣ ⟩
                        join H'.B♯Q  ≈⟨ unq-join _ meetᵣ joinᵣ ⟩
                        join S'♯Q'
                        ∎

             QQ'≈SQ : join Q♯Q' ≈ join S♯Q
             QQ'≈SQ = begin
                           join Q♯Q'  ≈⟨ sym $ unq-join _ (joinᵣ ⇒⟨ SQ≈S'Q' ⟩) joinᵣ ⟩
                           join S'♯Q' ≈⟨ sym SQ≈S'Q' ⟩ 
                           join S♯Q   
                      ∎
                    

             PP'≈SP : join P♯P' ≈ join S♯P
             PP'≈SP = begin
                           join P♯P'  ≈⟨ sym $ unq-join _ (joinᵣ ⇒⟨ SP≈S'P' ⟩) joinᵣ ⟩
                           join S'♯P' ≈⟨ sym SP≈S'P' ⟩ 
                           join S♯P   
                      ∎
                    
             S∈QQ' : S ∈ join Q♯Q'
             S∈QQ' =  joinₗ ⇒⟨ sym QQ'≈SQ ⟩

             S∈PP' : S ∈ join P♯P'
             S∈PP' =  joinₗ ⇒⟨ sym PP'≈SP ⟩

             S≈O : S ≈ O
             S≈O = unq-meet _  S∈PP' S∈QQ'


             S'≈O : S' ≈ O
             S'≈O =  begin
                      S' ≈⟨ sym S≈S' ⟩ 
                      S  ≈⟨ S≈O      ⟩
                      O  ∎

             R'∈RA : R' ∈ join R♯A
             R'∈RA = C6 ¬R'∉RA
               where
                 ¬R'∉RA : ¬ (R' ∉ join R♯A)
                 ¬R'∉RA R'∉RA = RS≈R'S' RS♯R'S'
                      where open PerspectivePQR R'∉RA using (O∈RR')
                            RS≈R'S' : join R♯S ≈ join H'.R♯S 
                            RS≈R'S' =
                              begin
                                join R♯S  ≈⟨ sym $ unq-join _ joinₗ (⟨ S≈O ⟩⇐ O∈RR') ⟩ 
                                join R♯R' ≈⟨ unq-join _ joinᵣ (⟨ S'≈O ⟩⇐ O∈RR') ⟩
                                join H'.R♯S 
                              ∎

             RA≈R'A : join R♯A ≈ join H'.R♯A
             RA≈R'A = unq-join _ R'∈RA joinᵣ

             Q≈Q' : Q ≈ Q'
             Q≈Q' = begin
                      Q ≈⟨ unq-meet _ joinᵣ meetₗ ⟩
                      meet BQ♯RA    ≈⟨ meet-cong BQ≈SQ RA≈R'A ⟩
                      meet  SQ♯R'A  ≈⟨ sym $ unq-meet _ (joinᵣ ⇒⟨ sym SQ≈S'Q' ⟩) meetₗ ⟩
                      Q'
                     ∎
                   where 
                         BQ≈SQ :  join B♯Q ≈ join S♯Q
                         BQ≈SQ  = unq-join _ meetᵣ joinᵣ

                         SQ♯R'A : join S♯Q ♯ join H'.R♯A
                         SQ♯R'A =  ⟨ sym BQ≈SQ ⟩⇐ BQ♯RA ⇒⟨ RA≈R'A ⟩
             absurdity : ⊥
             absurdity = Q≈Q' Q♯Q'
           ----  end case-S≈S'




