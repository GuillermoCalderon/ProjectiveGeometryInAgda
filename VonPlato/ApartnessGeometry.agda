module VonPlato.ApartnessGeometry where

open import Level
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function 
     using (case_of_ ; _$_ ; _∘_)



record ApartnessGeometry  a b c d e f : Set (suc (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f)) where

  field
    --
    -- Basic sets
    --
    Point : Set a
    Line  : Set b

    ---------------------------------------------------------
    -- Basic relations
    --
    -- distinct points and lines
    DiPt  : Point → Point → Set c  
    DiLn  : Line  → Line → Set d

    -- convergente lines
    Con : Line → Line → Set e

    -- outside  (Von Plato uses "apart")
    Apt : Point → Line → Set f


  -- negation of basic relations
  EqPt : Point → Point → Set c
  EqPt P Q = ¬ (DiPt P Q)

  EqLn : Line → Line → Set d
  EqLn r s = ¬ (DiLn r s)

  Par : Line → Line → Set e
  Par r s = ¬ (Con r s)

  Inc : Point → Line → Set f
  Inc P r = ¬ (Apt P r)


  
  -- rules of formation
  field

    ln : ∀ {A B : Point} → DiPt A B → Line

    pt : ∀ {r s : Line} → Con r s → Point 


  -- Apartness axioms for distinct points, distinct lines, and convergent lines
  
  -- irreflexivity
    irref-DiPt : ∀ {P} → ¬ (DiPt P P)
    irref-DiLn : ∀ {l} → ¬ (DiLn l l)
    irref-Con  : ∀ {l} → ¬ (Con l l)

  -- apartness (co-transitivity)
    apartness-DiPt : ∀ {A B} C → DiPt A B → DiPt A C ⊎ DiPt B C
    apartness-DiLn : ∀ {a b} c → DiLn a b → DiLn a c ⊎ DiLn b c
    apartness-Con  : ∀ {a b} c → Con a b → Con a c ⊎ Con b c

  -- Axioms for connecting lines and intersection points
    ln-left   : ∀ {A B} → (A≠B : DiPt A B) → Inc A (ln A≠B)
    ln-right  : ∀ {A B} → (A≠B : DiPt A B) → Inc B (ln A≠B)
    pt-left   : ∀ {a b} → (a×b : Con a b)  → Inc (pt a×b) a
    pt-right  : ∀ {a b} → (a×b : Con a b)  → Inc (pt a×b) b

  -- Constructive uniqueness axiom for lines and points
    uniqueness : ∀ {A B l m} 
                 → DiPt A B → DiLn l m 
                 → Apt A l ⊎ Apt A m ⊎ Apt B l ⊎ Apt B m

  -- Compatibility of equality with apartness and convergence
    compat-Apt-EqPt : ∀ A B l → Apt A l → DiPt A B ⊎ Apt B l 
    compat-Apt-EqLn : ∀ l m A → Apt A l → DiLn l m ⊎ Apt A m
    compat-Con-EqLn : ∀ l m n → Con l m → DiLn m n ⊎ Con l n

  -- Substitution in Apt
  subs-Apt₁ : ∀ {A B l} → Apt A l → EqPt A B → Apt B l
  subs-Apt₁ {B = B} A∉l A=B with compat-Apt-EqPt _ B _ A∉l 
  subs-Apt₁ A∉l A=B | inj₁ A≠B = ⊥-elim (A=B A≠B)
  subs-Apt₁ A∉l A=B | inj₂ B∉l = B∉l

  subs-Apt₂ : ∀ {A l r} → Apt A l → EqLn l r → Apt A r
  subs-Apt₂ {r = r} A∉l l=r with compat-Apt-EqLn _ r _ A∉l 
  subs-Apt₂ A∉l l=r | inj₁ l≠r = ⊥-elim (l=r l≠r)
  subs-Apt₂ A∉l l=r | inj₂ A∉r = A∉r


  
  -- Theoreme 3.1 (Uniqueness of constructed lines)
  unq-ln : ∀{A B l}→ (A≠B : DiPt A B) → Inc A l → Inc B l → EqLn l (ln A≠B)
  unq-ln A♯B A∈l B∈l l≠AB = 
    case uniqueness A♯B l≠AB of 
    \{ (inj₁ A∉l) → A∈l A∉l
     ; (inj₂ qq) → 
       case qq of
       \{ (inj₁ A∉AB) → ln-left A♯B A∉AB
        ; (inj₂ qq2) → 
          case qq2 of
          \{(inj₁ B∉l) → B∈l B∉l
           ;(inj₂ B∉AB) → ln-right A♯B B∉AB
           }
        }
     }

  -- symmetry
  sym-DiPt : ∀ {A B} → DiPt A B → DiPt B A
  sym-DiPt {A} {B} A≠B = 
    case apartness-DiPt A A≠B of 
    \{ (inj₁ A≠A) → ⊥-elim (irref-DiPt A≠A)
     ; (inj₂ B≠A) → B≠A
     }
  sym-DiLn : ∀ {r s} → DiLn r s → DiLn s r
  sym-DiLn {r} {s} r≠s = 
    case apartness-DiLn r r≠s of 
    \{ (inj₁ r≠r) → ⊥-elim (irref-DiLn r≠r)
     ; (inj₂ s≠r) → s≠r
     }

  sym-EqLn : ∀ {r s} → EqLn r s → EqLn s r
  sym-EqLn r=s = r=s ∘ sym-DiLn 

  sym-EqPt : ∀ {A B} → EqPt A B → EqPt B A
  sym-EqPt A=B = A=B ∘ sym-DiPt


  -- susbtitution for Inc
  subs-Inc₁ : ∀ {A B l} → Inc A l → EqPt A B → Inc B l
  subs-Inc₁ A∈l A=B = λ B∉l → A∈l (subs-Apt₁ B∉l (sym-EqPt A=B))

  subs-Inc₂ : ∀ {r s A} → Inc A r → EqLn r s → Inc A s
  subs-Inc₂ A∈r r=s = λ A∉s → A∈r (subs-Apt₂ A∉s (sym-EqLn r=s))

  -- Theoreme 3.2 
  Con→DiLn : ∀{l m} → Con l m → DiLn l m
  Con→DiLn {l} {m} l∤m = 
    case compat-Con-EqLn l m l l∤m of 
    \{ (inj₁ m≠l) → sym-DiLn m≠l
     ; (inj₂ l∤l) → ⊥-elim (irref-Con l∤l)
     }

  -- Symmetry in apartness and incidence

  -- Lemma 4.1
  lemma-4-1-ln→ : ∀ {A B l} → (A≠B : DiPt A B) 
                          → DiLn l (ln A≠B) → Apt A l ⊎ Apt B l
  lemma-4-1-ln→ A≠B  l≠AB = 
        case uniqueness A≠B l≠AB of 
        \{ (inj₁ A∉l) → inj₁ A∉l
         ; (inj₂ qq) → 
           case qq of 
           \{ (inj₁ A∉AB) → ⊥-elim (ln-left A≠B A∉AB)
            ; (inj₂ rr) → 
              case rr of 
              \{ (inj₁ B∉l) → inj₂ B∉l
               ; (inj₂ B∉AB) → ⊥-elim (ln-right A≠B B∉AB)
               }
            }
         }

  lemma-4-1-ln← : ∀ {A B l} → (A≠B : DiPt A B) 
                  → Apt A l ⊎ Apt B l → DiLn l (ln A≠B) 
  lemma-4-1-ln← {A} {B} {l} A≠B (inj₁ A∉l) = 
    case  compat-Apt-EqLn  l (ln A≠B) A A∉l of 
    \{ (inj₁ l≠AB) → l≠AB
     ; (inj₂ A∉AB) → ⊥-elim (ln-left A≠B A∉AB)
     }
  lemma-4-1-ln← {A} {B} {l} A≠B (inj₂ B∉l) = 
    case  compat-Apt-EqLn  l (ln A≠B) B B∉l of 
    \{ (inj₁ l≠AB) → l≠AB
     ; (inj₂ B∉AB) → ⊥-elim (ln-right A≠B B∉AB)
     }

  lemma-4-1-pt→ : ∀ {a b P} → (a∤b : Con a b) 
                          → DiPt P (pt a∤b) → Apt P a ⊎ Apt P b
  lemma-4-1-pt→ a∤b  P≠ab = 
        case uniqueness P≠ab (Con→DiLn a∤b) of 
        \{ (inj₁ P∉A) → inj₁ P∉A
         ; (inj₂ qq) → 
              case qq of 
              \{ (inj₁ P∉b) → inj₂ P∉b
               ; (inj₂ pp) → 
                 case pp of 
                 \{ (inj₁ ab∉a) → ⊥-elim (pt-left a∤b ab∉a)
                  ; (inj₂ ab∉b) → ⊥-elim (pt-right a∤b ab∉b)
                  }
               }
         }

  lemma-4-1-pt← : ∀ {a b P} → (a∤b : Con a b) 
                  → Apt P a ⊎ Apt P b → DiPt  P (pt a∤b)
  lemma-4-1-pt← {a} {b} {P} a∤b (inj₁ P∉a) = 
        case compat-Apt-EqPt  P (pt a∤b) a P∉a of 
        \{ (inj₁ P≠ab) → P≠ab
         ; (inj₂ ab∉a) → ⊥-elim (pt-left a∤b ab∉a)
         }
  lemma-4-1-pt← {a} {b} {P} a∤b (inj₂ P∉b) = 
        case compat-Apt-EqPt P (pt a∤b) b P∉b of 
        \{ (inj₁ P≠ab) → P≠ab
         ; (inj₂ ab∉b) → ⊥-elim (pt-right a∤b ab∉b)
         }

  -- Theorem 4.2 - Symmetry of Apt
  theorem-4-2 : ∀ {A B C D} → (A≠B : DiPt A B) → (C≠D : DiPt C D)
                →  Apt A (ln C≠D) ⊎ Apt B (ln C≠D)
                →  Apt C (ln A≠B) ⊎ Apt D (ln A≠B)
  theorem-4-2 A≠B C≠D Apt-A|B-CD  = lemma-4-1-ln→  _ AB≠CD
              where AB≠CD : DiLn (ln A≠B) (ln C≠D)
                    AB≠CD = sym-DiLn (lemma-4-1-ln← _ Apt-A|B-CD)

  lemma-4-3ᵢ :  ∀ {C A B} 
               → (A≠B : DiPt A B) → Apt C (ln A≠B)
               → DiPt C A × DiPt C B
  lemma-4-3ᵢ {C} {A} {B} A≠B C∉AB with compat-Apt-EqPt _ A (ln A≠B) C∉AB 
  lemma-4-3ᵢ {B = B} A≠B C∉AB | inj₁ C≠A 
                      with compat-Apt-EqPt _ B (ln A≠B) C∉AB 
  lemma-4-3ᵢ A≠B C∉AB | inj₁ C≠A | inj₁ C≠B = C≠A , C≠B
  lemma-4-3ᵢ A≠B C∉AB | inj₁ C≠A | inj₂ B∉AB = ⊥-elim (ln-right A≠B B∉AB)
  lemma-4-3ᵢ A≠B C∉AB | inj₂ A∉AB = ⊥-elim (ln-left A≠B A∉AB)

  lemma-4-3ᵢᵢ :  ∀ {C A B} 
                 → (A≠B : DiPt A B) → (C∉AB : Apt C (ln A≠B))
                 → let l43ᵢ = lemma-4-3ᵢ A≠B C∉AB
                       C≠A  = proj₁ l43ᵢ
                       C≠B  = proj₂ l43ᵢ
                 in DiLn (ln A≠B) (ln C≠A) × DiLn (ln A≠B) (ln C≠B)
  lemma-4-3ᵢᵢ A≠B C∉AB = qed
    where l43ᵢ = lemma-4-3ᵢ A≠B C∉AB
          C≠A  = proj₁ l43ᵢ
          C≠B  = proj₂ l43ᵢ

          qed : DiLn (ln A≠B) (ln C≠A) × DiLn (ln A≠B) (ln C≠B)
          qed  with compat-Apt-EqLn (ln A≠B) (ln C≠A) _ C∉AB 
          qed | inj₁ AB≠CA with compat-Apt-EqLn (ln A≠B) (ln C≠B) _ C∉AB  
          qed | inj₁ AB≠CA | inj₁ AB≠CB = AB≠CA , AB≠CB
          qed | inj₁ AB≠CA | inj₂ C∉CB =  ⊥-elim (ln-left C≠B C∉CB)
          qed | inj₂ C∉CA = ⊥-elim (ln-left C≠A C∉CA)

  -- triangle axioms
  triangle₁ : ∀ {A B C} → (A≠B : DiPt A B)
                        → (C∉AB : Apt C (ln A≠B))
                        → let C≠B = proj₂ (lemma-4-3ᵢ A≠B C∉AB)
                          in Apt A (ln C≠B)
  triangle₁ {A} A≠B C∉AB = qed
     where
       C≠B = proj₂ (lemma-4-3ᵢ A≠B C∉AB)
       AB≠CB = proj₂ (lemma-4-3ᵢᵢ A≠B C∉AB)

       qed : Apt A (ln C≠B)
       qed with uniqueness  A≠B AB≠CB 
       qed | inj₁ A∉AB = ⊥-elim (ln-left A≠B A∉AB)
       qed | inj₂ (inj₁ A∉CB) = A∉CB
       qed | inj₂ (inj₂ (inj₁ B∉AB)) = ⊥-elim (ln-right A≠B B∉AB)
       qed | inj₂ (inj₂ (inj₂ B∉CB)) = ⊥-elim (ln-right C≠B B∉CB)

  triangle₃ : ∀ {A B C} → (A≠B : DiPt A B)
                        → (C∉AB : Apt C (ln A≠B))
                        →  Apt C (ln $ sym-DiPt A≠B)

  triangle₃ A≠B C∉AB = subs-Apt₂ C∉AB (unq-ln _ (ln-right _) (ln-left _))
  

  triangle₂ : ∀ {A B C} → (A≠B : DiPt A B)
                        → (C∉AB : Apt C (ln A≠B))
                        → let A≠C = sym-DiPt $ proj₁ $ lemma-4-3ᵢ A≠B C∉AB
                          in Apt B (ln A≠C)
  triangle₂ {A} {B} {C} A≠B C∉AB 
           = triangle₃ _ (subs-Apt₂ B∉CA (unq-ln _ (ln-left _) (ln-right _)))
     where
       A≠C : DiPt A C
       A≠C =  sym-DiPt $ proj₁ (lemma-4-3ᵢ A≠B C∉AB)

       C∉BA = triangle₃ _ C∉AB
       B∉CA = triangle₁ _ C∉BA

  -- Lemma 4.5
  lemma-4-5ᵢ :  ∀ {A B l} 
               → (A≠B : DiPt A B)
               → EqLn l (ln A≠B)
               → Inc A l × Inc B l
  lemma-4-5ᵢ A≠B l=AB = subs-Inc₂ (ln-left A≠B) (sym-EqLn l=AB) ,  subs-Inc₂ (ln-right A≠B) (sym-EqLn l=AB)
