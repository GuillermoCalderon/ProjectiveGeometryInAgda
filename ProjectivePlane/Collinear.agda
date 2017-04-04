
open import Relation.Nullary
open import Data.Sum
open import Data.Product
open import Level
open import Function hiding (_∋_)
open import Relation.Binary.Apartness
open import ProjectivePlane as P
import ProjectivePlane.Duality
       using (module Lemmas)

module ProjectivePlane.Collinear
       (PP : ProjectivePlane) 
       where

       open P.ProjectivePlane PP
       open  ProjectivePlane.Duality.Lemmas PP
             using (c7 ; ∌→∉)

       -- Definition 2.6: collinear set of points
       -- Note: a set of points is represented as a predicate S : Point → Set
       --       such that (S P) is inhabited iff  P belongs to the set

       -- Comentario: Estas definiciones no parecen ser muy útiles.  
       --             No me convence la utilización de predicados para
       --             representar conjuntos.
       --             Parecería que alcanza con tratar la no colinearidad de 3 puntos (triangulo)
       
       open TightApartness ⦃...⦄

       collinear   : (Point → Set) → Set
       collinear S = ∀ P Q R → S P → S Q → S R → (Q♯R : Q ♯ R) → P ∈ join Q♯R

       noncollinear : (Point → Set) → Set
       noncollinear S = ∃ λ P → ∃ λ Q → ∃ λ R → S P × S Q × S R × Σ (Q ♯ R) λ Q♯R → P ∉ join Q♯R

       ¬noncol→col : ∀ S → ¬ (noncollinear S) → collinear S
       ¬noncol→col  S ¬noncolS P Q R SP SQ SR Q♯R 
                    = C6→ P (join Q♯R) (λ P∉QR → ¬noncolS (P , (Q , R , SP , SQ , SR , Q♯R , P∉QR)))

       --
       -- (¬ col → noncol)  is not constructively valid
       --


       lemma-2-8 : ∀ S → noncollinear S →
                     ∀ l → ∃ λ A → ∃ λ B → Σ (A ♯ B)  λ A♯B →  S A × S B × l ♯ join A♯B
       lemma-2-8 S ( P , Q , R , SP , SQ , SR , Q♯R , P∉QR ) l = 
            case cotransitivity l QR♯PR  of λ
            { (inj₁ l♯QR)  →  Q , R , Q♯R , SQ , SR , l♯QR
            ; (inj₂ l♯PR)  →  P , R , P♯R , SP , SR , l♯PR
            }
            where
              P♯R : P ♯ R
              P♯R = P∉QR R joinᵣ
              QR♯PR : join Q♯R ♯ join P♯R
              QR♯PR = symmetry  $ C5  (join P♯R) (join Q♯R) P joinₗ P∉QR

       prop-2-8 : ∀ S → noncollinear S → ∀ l → ∃ λ P → S P × P ∉ l
       prop-2-8 S noncolS l with lemma-2-8 S noncolS l
       ...                     | (A , B , A♯B , SA , SB , l♯AB ) = 
          case c7  A♯B l♯AB of  λ 
          { (inj₁ l∌A)  →  A , SA , ∌→∉  l∌A
          ; (inj₂ l∌B)  →  B , SB , ∌→∉  l∌B
          }

