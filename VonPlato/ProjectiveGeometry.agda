module VonPlato.ProjectiveGeometry1 where

open import Level
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import VonPlato.ApartnessGeometry
open import ProjectivePlane
open import Relation.Binary
open import Relation.Binary.Apartness
open import Function using (case_of_ ; _∘_ ; id )

record ProjectiveGeometry a b c d e f : Set (suc (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f)) where
  field
    AG :  ApartnessGeometry a b c d e f
  open ApartnessGeometry AG public

  field
    -- all distinct lines are convergent
    DiLn→Con : ∀{r s} → DiLn r s → Con r s 



  instance
    Pt♯ : Setoid♯ a c
    Pt♯ = record { 
      _♯_ = DiPt ; 
      isApartness = record { irreflexive = irref-DiPt ; cotransitivity = cotrans } 
      }
      where  cotrans : {x y : Point} (z : Point) → DiPt x y → DiPt z x ⊎ DiPt z y
             cotrans z x≠y = 
               case apartness-DiPt z x≠y of 
                 \{ (inj₁ x≠z) → inj₁ (sym-DiPt x≠z)
                  ; (inj₂ y≠z) → inj₂ (sym-DiPt y≠z)
                  }
      



    Ln♯ : Setoid♯ b d 
    Ln♯ = record { 
      _♯_ = DiLn ; 
      isApartness = record { irreflexive = irref-DiLn ; cotransitivity = cotrans } 
      }
      where  cotrans : {x y : Line} (z : Line) → DiLn x y → DiLn z x ⊎ DiLn z y
             cotrans z x≠y = 
               case apartness-DiLn z x≠y of 
                 \{ (inj₁ x≠z) → inj₁ (sym-DiLn x≠z)
                  ; (inj₂ y≠z) → inj₂ (sym-DiLn y≠z)
                  }

  pt' : ∀ {l r} → (l♯r : DiLn l  r) → Point
  pt' = pt ∘ DiLn→Con

  -- Apt vs ∉
  _∈_ :  Point → Line → Set f
  P ∈ r = ¬ Apt P r


  _∀∈♯_ : Point → Line → Set (f ⊔ (c ⊔ a))
  P ∀∈♯ r = ∀{Q} → Q ∈ r → DiPt P  Q

  Apt→∉ : ∀ {P r} → Apt P r → P ∀∈♯ r
  Apt→∉ {P} {r} Apt-P-r {Q} Q∈r = 
    case compat-Apt-EqPt P Q r Apt-P-r of 
    \{ (inj₁ P♯Q) → P♯Q
     ; (inj₂ Apt-Q-r) → ⊥-elim (Q∈r Apt-Q-r)
     }

  incidence : Rel♯ _ Pt♯ Ln♯
  incidence = record { R = _∈_ ; isRel = record { sound = λ A≈B c≈d A∈c  → subs-Inc₁ (subs-Inc₂ A∈c c≈d) A≈B } }

  outside : Rel♯ _ Pt♯ Ln♯
  outside = record { R = Apt ; isRel = record { sound = λ A≈B c≈d A∉c  → subs-Apt₁ (subs-Apt₂ A∉c c≈d) A≈B } }
    

  record ExtensionAxiom : Set (a ⊔ b ⊔ c ⊔ f ) where
    field
       -- non degenerating axioms 
       P₀    : Point
       l₀    : Line
       P₀∉l₀ : Apt P₀ l₀

       point₁ point₂ point₃ : Line → Point
       ∈-point₁  : ∀ l → point₁ l ∈ l 
       ∈-point₂  : ∀ l → point₂ l ∈ l
       ∈-point₃  : ∀ l → point₃ l ∈ l
       point-i♯j : ∀ l → DiPt (point₁ l)  (point₂ l) ×
                         DiPt (point₁ l)  (point₃ l) ×
                         DiPt (point₂ l)  (point₃ l) 



    projectivePlane : ProjectivePlane a c b d f
    projectivePlane = record
                      { Point♯ = Pt♯
                      ; Line♯ = Ln♯
                      ; Outside = outside
                      ; Incidence = incidence
                      ; isProjectivePlane 
                        = record
                            {
                              P₀ = P₀
                            ; l₀ = l₀
                            ; P₀∉l₀ = P₀∉l₀
                            ; point₁ = point₁ 
                            ; point₂ = point₂ 
                            ; point₃ = point₃
                            ; ∈-point₁ = ∈-point₁
                            ; ∈-point₂ = ∈-point₂
                            ; ∈-point₃ = ∈-point₃
                            ; point-i♯j = point-i♯j
                            -------------------------------
                            ;  C0 = Apt→∉
                            ; join = ln
                            ; joinₗ = λ {_} {_} {A♯B} → ln-left A♯B
                            ; joinᵣ = λ {_} {_} {A♯B} → ln-right A♯B
                            ; unq-join =  λ P♯Q → unq-ln P♯Q
                            ; meet = pt'
                            ; meetₗ = λ {_} {_} {A♯B} → pt-left (DiLn→Con A♯B)
                            ; meetᵣ = λ {_} {_} {A♯B} → pt-right (DiLn→Con A♯B)
                            ; unq-meet = unqmt
                            ; C5 = axC5
                            ; C6 = id
                            ; C7 = axC7
                            }
                      } 

                  where
                       unqmt : ∀ {r s} → (r♯s : DiLn r  s) →  ∀ {P}
                                       → Inc P r → Inc P s → EqPt P  (pt (DiLn→Con r♯s))
                       unqmt r♯s  P∈r P∈s P♯rs = 
                             case uniqueness P♯rs r♯s of 
                             \{ (inj₁ P∉r) → P∈r P∉r
                              ; (inj₂ q) → case q of
                                      \{ (inj₁ P∉s) → P∈s P∉s
                                       ; (inj₂ s) → case s of 
                                               \{ (inj₁ rs∉r) → pt-left (DiLn→Con r♯s) rs∉r
                                                ; (inj₂ rs∉s) → pt-right (DiLn→Con r♯s) rs∉s
                                                }
                                       }
                              }


                       -- variaciones del axioma 5
                       axC5 : ∀ {l m P} → Inc P l 
                                        → Apt P m
                                        → DiLn l  m
                       axC5 {l} {m} {P} P∈l Apt-Pm =
                            case compat-Apt-EqLn m l P Apt-Pm of 
                            \{ (inj₁ m≠l) → sym-DiLn m≠l
                             ; (inj₂ Apt-Pl) → ⊥-elim (P∈l Apt-Pl)
                             }

                       axC7 : ∀ {l m : Line} {P : Point}
                              → (l♯m : DiLn l  m) → (DiPt P  (pt' l♯m)) → Apt P l ⊎ Apt P m
                       -- let O = pt l♯m
                       axC7 l♯m P♯O with uniqueness P♯O l♯m 
                       axC7 l♯m P♯O | inj₁ P∉l = inj₁ P∉l
                       axC7 l♯m P♯O | inj₂ (inj₁ P∉m) =  inj₂ P∉m
                       axC7 l♯m P♯O | inj₂ (inj₂ (inj₁ O∉l)) = ⊥-elim (pt-left (DiLn→Con l♯m) O∉l)
                       axC7 l♯m P♯O | inj₂ (inj₂ (inj₂ O∉m)) = ⊥-elim (pt-right (DiLn→Con l♯m) O∉m)


  fromProjectivePlane : ∀ {a b c d f} 
                        → ProjectivePlane a c b d  f 
                        → ProjectiveGeometry _ _ _ _ _ _
  fromProjectivePlane PP
    = record 
      { AG = record
               { Point = Po
               ; Line =  Li
               ; DiPt = _♯_
               ; DiLn = _♯_ 
               ; Con  = _♯_ 
               ; Apt = _∉_
               ; ln = join
               ; pt = meet
               ; irref-DiPt = irreflexive
               ; irref-DiLn = irreflexive
               ; irref-Con  = irreflexive
               ; apartness-DiPt = λ C A♯B → case cotransitivity C A♯B of
                                            \{ (inj₁ C♯A) → inj₁ (symmetry C♯A)
                                             ; (inj₂ C♯B) → inj₂ (symmetry C♯B)
                                             }
               ; apartness-DiLn = λ C A♯B → case cotransitivity C A♯B of
                                            \{ (inj₁ C♯A) → inj₁ (symmetry C♯A)
                                             ; (inj₂ C♯B) → inj₂ (symmetry C♯B)
                                             }
               ; apartness-Con = λ C A♯B → case cotransitivity C A♯B of
                                            \{ (inj₁ C♯A) → inj₁ (symmetry C♯A)
                                             ; (inj₂ C♯B) → inj₂ (symmetry C♯B)
                                             }
               ; ln-left = λ A♯B → C6← joinₗ
               ; ln-right =  λ A♯B → C6← joinᵣ
               ; pt-left = λ A♯B → C6← meetₗ
               ; pt-right = λ A♯B → C6← meetᵣ
               ; uniqueness 
                  = λ A♯B l♯m → case cotransitivity (meet l♯m) A♯B of 
                                \{ (inj₁ lm♯A) → 
                                         case C7 l♯m (symmetry lm♯A)  of 
                                         \{ (inj₁ A∉l) → inj₁ A∉l
                                          ; (inj₂ A∉m) → inj₂ (inj₁ A∉m)
                                          }
                                 ; (inj₂ lm♯B) → 
                                         case C7 l♯m (symmetry lm♯B)  of 
                                         \{ (inj₁ B∉l) → inj₂ (inj₂ (inj₁ B∉l))
                                          ; (inj₂ B∉m) → inj₂ (inj₂ (inj₂ B∉m))
                                          }
                                 }
               ; compat-Apt-EqPt = λ A B l A∉l → 
                                     let C = point₁ l
                                         A♯C : A ♯ C
                                         A♯C = C0 A∉l (∈-point₁ l)
                                         AC♯l : join A♯C ♯ l
                                         AC♯l = C5 joinₗ A∉l
                                     in  case cotransitivity B A♯C of 
                                         \{ (inj₁ B♯A) → inj₁ (symmetry B♯A)
                                          ; (inj₂ B♯C) → case C7-c B♯C AC♯l  joinᵣ (∈-point₁ l) of
                                                         \{ (inj₁ B∉AC) → inj₁ (symmetry (C0 B∉AC joinₗ))
                                                          ; (inj₂ B∉l)  → inj₂ B∉l
                                                          }
                                          }
               ; compat-Apt-EqLn = λ l m A A∉l → 
                                     let C = point₁ l
                                         A♯C : A ♯ C
                                         A♯C = C0 A∉l (∈-point₁ l)
                                         AC♯l : join A♯C ♯ l
                                         AC♯l = C5 joinₗ A∉l 
                                      in case cotransitivity m AC♯l of 
                                         \{ (inj₁ m♯AC)
                                                  → case cotransitivity (meet m♯AC) A♯C of
                                                     \{ (inj₁ M♯A) → inj₂  (C7-a (symmetry m♯AC) (symmetry M♯A  ⇒⟨ meet-comm ⟩) joinₗ) 
                                                      ; (inj₂ M♯C) → inj₁ (C5 (∈-point₁ l)
                                                                     (C7-a (symmetry m♯AC) (symmetry M♯C ⇒⟨ meet-comm ⟩) joinᵣ))
                                                      }
                                          ; (inj₂ m♯l)  → inj₁ (symmetry m♯l)
                                          }
                                         

               ; compat-Con-EqLn = λ l m n l♯m → case cotransitivity n l♯m of
                                                 \{ (inj₁ n♯l) → inj₂ (symmetry n♯l)
                                                  ; (inj₂ n♯m) → inj₁ (symmetry n♯m)
                                                  }
               } 
      ; DiLn→Con = id }

     where 
       open ProjectivePlane.Setoid♯Instances PP 
       open ProjectivePlane.Rel♯Instances PP
       open ProjectivePlane.ProjectivePlane PP
            renaming (Line to Li ; Point to Po)
       open import ProjectivePlane.PropertiesGeneral PP
            

                       

