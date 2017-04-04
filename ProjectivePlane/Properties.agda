
open import Relation.Binary.Apartness
import Relation.Binary.EqReasoning as EqR
open import Relation.Nullary
open import Data.Sum 
open import Data.Product
open import Level as L
open import Function renaming (_∋_ to _:∋:_)
open import ProjectivePlane

module ProjectivePlane.Properties {a b c d e} 
  (PP : ProjectivePlane a b c d e)  where
  
  open ProjectivePlane.ProjectivePlane PP
  open ProjectivePlane.Setoid♯Instances PP
  open ProjectivePlane.Rel♯Instances PP
       -- 
       -- Properties
       --

  ∉join : ∀ {A B C r} → (A♯B : A ♯ B) → A ∈ r → B ∈ r → C ∉ r → C ∉ join A♯B
  ∉join  A♯B A∈r B∈r C∉r =  C∉r ⇒⟨ unq-join A♯B A∈r B∈r ⟩




  join-comm :  ∀ {A B} {A♯B : A ♯ B} {B♯A : B ♯ A} 
                 →  join A♯B ≈ join B♯A
  join-comm = unq-join _ joinᵣ joinₗ


  sym-join : ∀ {A B} {A♯B : A ♯ B} → join A♯B ≈ join (symmetry A♯B)        
  sym-join  = join-comm


  
  -- the proof A♯B is irrelevant in join A♯B
  ≈join : ∀ {A B} → {A♯B other-A♯B : A ♯ B}
                       → join A♯B ≈  join other-A♯B
  ≈join   = unq-join _ joinₗ joinᵣ



  join-cong : ∀ {P Q P' Q' : Point} 
          → {P≠Q : P ♯ Q}
          → {P'≠Q' : P' ♯ Q'}
          → P ≈ P'
          → Q ≈ Q'
          → join P≠Q ≈ join P'≠Q'
  join-cong  P≈P' Q≈Q'  
    = unq-join _ (⟨ sym P≈P' ⟩⇐ joinₗ ) ( ⟨ sym Q≈Q' ⟩⇐ joinᵣ)
       -- where open Rel♯ PointInLine



  join-flip-cong : ∀ {P Q P' Q' : Point} 
          → {P♯Q : P ♯ Q}
          → {Q'♯P' : Q' ♯ P'}
          → P ≈ P'
          → Q ≈ Q'
          → join P♯Q ≈ join Q'♯P'
  join-flip-cong  {P♯Q = P♯Q} {Q'♯P'} P≈P' Q≈Q' = --trans sym-join (join-cong Q≈Q' P≈P') 
       begin 
          join P♯Q             ≈⟨ sym-join            ⟩ 
          join (symmetry P♯Q)  ≈⟨ join-cong Q≈Q' P≈P' ⟩ 
          join Q'♯P' 
       ∎
    where open EqR (toSetoid Line♯)


  --  no sé si son necesarios estas operaciones
  meet-joinᵣᵣ  : ∀ {Q P R} 
                    → {P♯Q : P ♯ Q}
                    → {R♯Q : R ♯ Q}
                    → {PQ♯RQ : join P♯Q ♯ join R♯Q}
                    → Q ≈ meet PQ♯RQ               
  meet-joinᵣᵣ = unq-meet _ joinᵣ joinᵣ

  meet-joinᵣₗ :  ∀ {Q P R} 
                    → {P♯Q : P ♯ Q}
                    → {Q♯R : Q ♯ R}
                    → {PQ♯QR : join P♯Q ♯ join Q♯R}
                    → Q ≈ meet PQ♯QR
  meet-joinᵣₗ  = unq-meet _ joinᵣ joinₗ  

  meet-joinₗᵣ :  ∀ {Q P R} 
                → {Q♯P : Q ♯ P}
                → {R♯Q : R ♯ Q}
                → {QP♯RQ : join Q♯P ♯ join R♯Q}
                → Q ≈ meet QP♯RQ
  meet-joinₗᵣ  = unq-meet _ joinₗ joinᵣ  

  meet-joinₗₗ :  ∀ {Q P R} 
                → {Q♯P : Q ♯ P}
                → {Q♯R : Q ♯ R}
                → {QP♯QR : join Q♯P ♯ join Q♯R}
                → Q ≈ meet QP♯QR
  meet-joinₗₗ  = unq-meet _ joinₗ joinₗ 




  -- Proposition 2.4 Mandelkern
  P-24→ : ∀ {P Q R} → (P♯Q : P ♯ Q) → (P♯R : P ♯ R) → (Q♯R : Q ♯ R) 
                       → P ∉ join Q♯R →  join P♯Q ♯ join P♯R  
  P-24→ {P} {Q} {R} P♯Q P♯R Q♯R P∉QR = C5 joinᵣ Q∉PR
           where
             PR♯QR : join P♯R ♯ join Q♯R
             PR♯QR = C5 joinₗ P∉QR

             Q∉PR : Q ∉ join P♯R
             Q∉PR = C7-b Q♯R (symmetry PR♯QR) joinᵣ joinᵣ joinₗ
           

  P-24← : ∀ P Q R → (P♯Q : P ♯ Q) → (P♯R : P ♯ R) → (Q♯R : Q ♯ R) 
                  →  join P♯Q ♯ join P♯R → P ∉ join Q♯R
  P-24← P Q R P♯Q P♯R Q♯R PQ♯PR  =
           let 
               Q∉PR : Q ∉ join P♯R
               Q∉PR = C7-b (symmetry P♯Q) PQ♯PR joinₗ joinₗ joinᵣ

               QR♯PR : join Q♯R ♯ join P♯R
               QR♯PR = C5 joinₗ Q∉PR
       
           in  C7-b P♯R (symmetry QR♯PR) joinᵣ joinᵣ joinₗ


  lemma-2-5 : ∀ l r → (l♯r : l ♯ r) → ∃ λ P → P ∈ l × P ♯ meet l♯r
  lemma-2-5 l r l♯r 
            = case cotransitivity (meet l♯r) (proj₁ $ point-i♯j l) of 
              \{ (inj₁ ♯P₁) → point₁ l , ∈-point₁ l , symmetry ♯P₁
               ; (inj₂ ♯P₂) → point₂ l , ∈-point₂ l , symmetry ♯P₂ 
               }
               
  -- Proposition 2.5
  Prop-2-5 : ∀ l r → l ♯ r → ∃ λ P → P ∈ l × P ∉ r
  Prop-2-5 l r l♯r with lemma-2-5 l r l♯r  
  ...               |   Q ,  Q∈l , Q♯l∙r = Q , Q∈l , C7-a l♯r Q♯l∙r Q∈l 




  lemma-♯∈ : ∀ P l → ∃ λ Q → P ♯ Q × Q ∈ l
  
  -- lemma-♯∈ P l with cotransitivity P  (proj₁ $ point-i♯j l)
  -- lemma-♯∈ P l | inj₁ P♯₁ =  _  , P♯₁ , ∈-point₁ l
  -- lemma-♯∈ P l | inj₂ P♯₂ =  _  , P♯₂ , ∈-point₂ l
  lemma-♯∈ P l =
      case  cotransitivity P  (proj₁ $ point-i♯j l) of
      \{  (inj₁ P♯₁) →  _  , P♯₁ , ∈-point₁ l
       ;  (inj₂ P♯₂) →  _  , P♯₂ , ∈-point₂ l
       }

  lemma-outside-line : ∀ (A C : Point) → (r : Line)   
                            →  A ∈ r → C ∉ r 
                            →  ∀ P → P ♯ A → ∃ λ l → P ∉ l
  lemma-outside-line A C  r  A∈r  C∉r P  P♯A  with P∉CA⊎r
           where
             C♯A : C ♯ A
             C♯A = C0 C∉r A∈r
             CA♯r : join C♯A ♯ r
             CA♯r = C5  joinₗ C∉r
             P∉CA⊎r : P ∉ join C♯A ⊎ P ∉ r
             P∉CA⊎r =  C7-c P♯A CA♯r joinᵣ A∈r
  ...        |   inj₁ P∉CA  =  join (C0 C∉r A∈r) ,  P∉CA
  ...        |   inj₂ P∉r   =  r        ,  P∉r 
  --
  -- I cannot write this function as a case (why?)
  -- Problem with levels
           
        

  outside-line : ∀ P → ∃  \l → P ∉ l
  outside-line P = 
         case  lemma-♯∈ P l₀ of 
             λ { (Q₀ , P♯Q₀ , Q₀∈l₀)  → lemma-outside-line Q₀ P₀ l₀ Q₀∈l₀ P₀∉l₀ P P♯Q₀ }


  module lemma-triangle {A B C}{B♯C : B ♯ C} (A∉BC : A ∉ join B♯C) where
         
         A♯B : A ♯ B
         A♯B = C0 A∉BC joinₗ
         A♯C : A ♯ C
         A♯C = C0 A∉BC joinᵣ
         
         AC♯BC : join A♯C ♯ join B♯C
         AC♯BC = C5 joinₗ A∉BC

         B∉AC : B ∉ join A♯C
         B∉AC = C7-b B♯C (symmetry AC♯BC) joinᵣ joinᵣ joinₗ

         AB♯AC : join A♯B ♯ join A♯C
         AB♯AC = C5 joinᵣ B∉AC

         C∉AB : C ∉ join A♯B
         C∉AB = C7-b (symmetry A♯C) (symmetry AB♯AC) joinₗ joinₗ joinᵣ

  module lemma-3-collinear {A B C}
         (A♯B : A ♯ B)(B♯C : B ♯ C)(A♯C : A ♯ C) (A∈BC : A ∈ join B♯C) where

       

         -- AB≈AC≈BC
         BC≈AB : join B♯C ≈ join A♯B
         BC≈AB = unq-join A♯B A∈BC joinₗ

         BC≈AC :  join B♯C   ≈ join A♯C 
         BC≈AC = unq-join A♯C A∈BC joinᵣ

         AC≈AB : join A♯C ≈ join A♯B
         AC≈AB =  begin   
                    join A♯C ≈⟨ sym BC≈AC ⟩ 
                    join B♯C ≈⟨ BC≈AB ⟩ 
                    join A♯B 
                  ∎ 
               where open EqR (toSetoid Line♯)

         
         B∈AC : B ∈ join A♯C
         B∈AC = joinᵣ  ⇒⟨ sym AC≈AB ⟩

             
         C∈AB : C ∈ join A♯B
         C∈AB = joinᵣ ⇒⟨ BC≈AB ⟩


      --  algunos lemas de existencia de puntos

       -- 
       --  Exist a collinear point different from 2 points A B
  ∃♯join :  ∀ {A B} → (A♯B : A ♯ B)
                      → ∃ λ C → C  ∈ join A♯B × C ♯ A × C ♯ B
  ∃♯join {A} {B} A♯B  = qed
         where X = point₁ $ join A♯B
               Y = point₂ $ join A♯B
               Z = point₃ $ join A♯B

               X♯Y : X ♯ Y
               X♯Y =  proj₁ $ point-i♯j (join A♯B)
               X♯Z : X ♯ Z
               X♯Z = proj₁ $ proj₂ $ point-i♯j (join A♯B)
               Y♯Z : Y ♯ Z
               Y♯Z = proj₂ $ proj₂ $ point-i♯j (join A♯B)
               
               qed : ∃ λ C → C  ∈ join A♯B × C ♯ A × C ♯ B
               qed with cotransitivity  A X♯Y  
               qed | inj₁ A♯X 
                     with cotransitivity B X♯Y 
               qed | inj₁ A♯X | inj₁ B♯X = X , ∈-point₁ _ , symmetry A♯X , symmetry B♯X
               qed | inj₁ A♯X | inj₂ B♯Y
                   with cotransitivity A Y♯Z 
               qed | inj₁ A♯X | inj₂ B♯Y | inj₁ A♯Y = Y , ∈-point₂ _ , symmetry A♯Y , symmetry B♯Y
               qed | inj₁ A♯X | inj₂ B♯Y | inj₂ A♯Z 
                   with cotransitivity B X♯Z
               qed | inj₁ A♯X | inj₂ B♯Y | inj₂ A♯Z | inj₁ B♯X =  X , ∈-point₁ _ , symmetry A♯X , symmetry B♯X
               qed | inj₁ A♯X | inj₂ B♯Y | inj₂ A♯Z | inj₂ B♯Z =  Z , ∈-point₃ _ , symmetry A♯Z , symmetry B♯Z
               qed | inj₂ A♯Y 
                   with cotransitivity B X♯Y
               qed | inj₂ A♯Y | inj₁ B♯X 
                   with cotransitivity B Y♯Z
               qed | inj₂ A♯Y | inj₁ B♯X | inj₁ B♯Y =  Y , ∈-point₂ _ , symmetry A♯Y , symmetry B♯Y
               qed | inj₂ A♯Y | inj₁ B♯X | inj₂ B♯Z
                   with cotransitivity A X♯Z 
               qed | inj₂ A♯Y | inj₁ B♯X | inj₂ B♯Z | inj₁ A♯X =  X , ∈-point₁ _ , symmetry A♯X , symmetry B♯X
               qed | inj₂ A♯Y | inj₁ B♯X | inj₂ B♯Z | inj₂ A♯Z =  Z , ∈-point₃ _ , symmetry A♯Z , symmetry B♯Z
               qed | inj₂ A♯Y | inj₂ B♯Y =  Y , ∈-point₂ _ , symmetry A♯Y , symmetry B♯Y

  -- There exists a point outside  2 distinct lines
  -- (useful to prove existence of harmonic conjugate)
  pointOutside2 : ∀ {l r} → l ♯ r  
                        → ∃ λ P → P ∉ l × P ∉ r
  pointOutside2 {l} {r} l♯r = 
                     case ∃♯join A♯B of
                     λ{ (P , P∈AB , P♯A , P♯B) → 
                           P  ,
                           C7-a  p♯l P♯A (P∈AB ⇒⟨ AB≈p ⟩)  ,
                           C7-a  p♯r P♯B (P∈AB ⇒⟨ AB≈p ⟩ )  
                       }
            where 
                  Q = meet l♯r
                  ∃l∌Q = outside-line Q
                  p : Line
                  p = proj₁ ∃l∌Q
                  Q∉p : Q ∉ p
                  Q∉p = proj₂ ∃l∌Q

                  p♯r : p ♯ r
                  p♯r = symmetry (C5 meetᵣ Q∉p)

                  p♯l : p ♯ l
                  p♯l = symmetry $ C5 meetₗ Q∉p

                  A = meet p♯l
                  B = meet p♯r

                  A∉r : A ∉ r
                  A∉r = C7-a  l♯r (symmetry (C0 Q∉p  meetₗ)) meetᵣ

                  A♯B : A ♯ B
                  A♯B = C0 A∉r  meetᵣ

                  AB≈p : join A♯B ≈ p
                  AB≈p = sym $ unq-join A♯B meetₗ meetₗ
                  

