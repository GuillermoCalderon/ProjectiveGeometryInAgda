{-# OPTIONS --no-eta-equality #-} 
{- Definition of a dedidable setoid for Fin n

-}

open import Data.Fin
open import Data.Nat hiding (_≟_)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.PropositionalEquality using (_≡_ ; decSetoid)
open import Relation.Binary.Apartness
open import Function using (case_of_ ; _$_)
import Level as Level

module Data.Fin.Setoid where


  -- propositional equality is decidable for Fin n
  FinEq : ∀ n → Decidable {A = Fin n} _≡_  
  FinEq zero () ()
  FinEq (suc n) zero zero = yes PropEq.refl
  FinEq (suc n) zero (suc b) = no (λ ())
  FinEq (suc n) (suc a) zero = no (λ ())
  FinEq (suc n) (suc a) (suc b) with FinEq n a b 
  FinEq (suc n) (suc a) (suc .a) | yes PropEq.refl = yes PropEq.refl
  FinEq (suc n) (suc a) (suc b) | no ¬a≡b = no (λ sa≡sb → ¬a≡b (aux a b sa≡sb)) 
        where  aux : ∀ {n} → (a b : Fin n) →  _≡_ {A = Fin (suc n)} (suc  a) (suc  b) → a ≡ b
               aux a .a PropEq.refl = PropEq.refl
  
  

  -- then we have a DecSetoid with carrier (Fin n)
  decSetoidFin : ∀ (n : ℕ) → DecSetoid♯ Level.zero Level.zero
  decSetoidFin n =  toDecSetoid♯ (decSetoid (FinEq n))

  -- a setoid with carrier (Fin n)
  setoidFin : (n : ℕ) → Setoid♯ Level.zero Level.zero
  setoidFin n = DecSetoid♯.S (decSetoidFin n)

  instance
    sf : ∀ {n : ℕ} → Setoid♯ _ _ 
    sf {n} = setoidFin n

  -- swap 
  swap : ∀ {n}
         → (i j : Fin n)
         → InjectiveFun♯ (setoidFin n) (setoidFin n) 
         → InjectiveFun♯ (setoidFin n) (setoidFin n) 
  swap {n} i j F = record { F = record { f = g  ; sound = λ {x y} → gsound x y } 
                          ; isInjective = λ {x y} → ginj x y }
     where 
           open Setoid♯ (setoidFin n)
           open DecSetoid♯ (decSetoidFin n)  using (_≟_)
           instance SetoidFin-n = setoidFin n

           g : (Fin n) → (Fin n)
           g u with u ≟ i 
           g u | yes u≡i           = ⟨_⟩$_  (fun♯ F)  j
           g u | no _  with u ≟ j 
           g u | no _  | yes u≡j   = ⟨ fun♯ F ⟩$ i
           g u | no _  | no _      = ⟨ fun♯ F ⟩$ u

           gsound : (x y : Fin n) → x ≈ y → g x ≈ g y
           gsound  x y x≈y with x ≟ i
           gsound x y x≈y | yes x≈i with y ≟ i
           gsound x y x≈y | yes x≈i | yes y≈i =   Fun♯.sound (fun♯ F)  refl
           gsound x y x≈y | yes x≈i | no ¬y≈i with y ≟ j 
           gsound x y x≈y | yes x≈i | no ¬y≈i | yes y≈j =  Fun♯.sound (fun♯ F) (trans (trans (sym y≈j) (sym x≈y)) x≈i)
           gsound x y x≈y | yes x≈i | no ¬y≈i | no ¬y≈j =  ⊥-elim (¬y≈i (trans (sym x≈y) x≈i ))
           gsound x y x≈y | no ¬x≈i with y ≟ i
           gsound x y x≈y | no ¬x≈i | yes y≈i with x ≟ j
           gsound x y x≈y | no ¬x≈i | yes y≈i | yes x≈j = Fun♯.sound (fun♯ F) (trans (sym y≈i) (trans (sym x≈y) x≈j))
           gsound x y x≈y | no ¬x≈i | yes y≈i | no ¬x≈j = ⊥-elim (¬x≈i (trans x≈y y≈i))
           gsound x y x≈y | no ¬x≈i | no ¬y≈i  with x ≟ j 
           gsound x y x≈y | no ¬x≈i | no ¬y≈i | yes x≈j with y ≟ j 
           gsound x y x≈y | no ¬x≈i | no ¬y≈i | yes x≈j | yes y≈j =  Fun♯.sound (fun♯ F)  refl
           gsound x y x≈y | no ¬x≈i | no ¬y≈i | yes x≈j | no ¬y≈j = ⊥-elim (¬y≈j (trans (sym x≈y) x≈j))
           gsound x y x≈y | no ¬x≈i | no ¬y≈i | no ¬x≈j with y ≟ j 
           gsound x y x≈y | no ¬x≈i | no ¬y≈i | no ¬x≈j | yes y≈j = ⊥-elim (¬x≈j (trans x≈y y≈j))
           gsound x y x≈y | no ¬x≈i | no ¬y≈i | no ¬x≈j | no ¬y≈j = Fun♯.sound (fun♯ F) x≈y

           open IsRel♯ (isRel♯-♯ {S = setoidFin n})
           open DecSetoid♯ (decSetoidFin n)  using (¬≈→♯)

           ginj : ∀ x y → x ♯ y →  (g x) ♯ (g y)
           ginj  x y x♯y with x ≟ i
           ginj x y x♯y | yes x≈i with y ≟ i
           ginj x y x♯y | yes x≈i | yes y≈i = ⊥-elim (trans x≈i (sym y≈i) x♯y)
           ginj x y x♯y | yes x≈i | no ¬y≈i with y ≟ j 
           ginj x y x♯y | yes x≈i | no ¬y≈i | yes y≈j =  isInjective F (symmetry (⟨ sym x≈i ⟩⇐ x♯y ⇒⟨ y≈j ⟩))
           ginj x y x♯y | yes x≈i | no ¬y≈i | no ¬y≈j = isInjective F  $ symmetry  $ ¬≈→♯ ¬y≈j
           ginj x y x♯y | no ¬x≈i with y ≟ i
           ginj x y x♯y | no ¬x≈i | yes y≈i with x ≟ j
           ginj x y x♯y | no ¬x≈i | yes y≈i | yes x≈j = isInjective F (symmetry (⟨ sym x≈j ⟩⇐ x♯y ⇒⟨ y≈i ⟩))
           ginj x y x♯y | no ¬x≈i | yes y≈i | no ¬x≈j = isInjective F (¬≈→♯ ¬x≈j)
           ginj x y x♯y | no ¬x≈i | no ¬y≈i  with x ≟ j 
           ginj x y x♯y | no ¬x≈i | no ¬y≈i | yes x≈j with y ≟ j 
           ginj x y x♯y | no ¬x≈i | no ¬y≈i | yes x≈j | yes y≈j = ⊥-elim (trans x≈j (sym y≈j) x♯y)
           ginj x y x♯y | no ¬x≈i | no ¬y≈i | yes x≈j | no ¬y≈j = isInjective F $ symmetry $ ¬≈→♯ ¬y≈i
           ginj x y x♯y | no ¬x≈i | no ¬y≈i | no ¬x≈j with y ≟ j 
           ginj x y x♯y | no ¬x≈i | no ¬y≈i | no ¬x≈j | yes y≈j = isInjective F $  ¬≈→♯ ¬x≈i
           ginj x y x♯y | no ¬x≈i | no ¬y≈i | no ¬x≈j | no ¬y≈j = isInjective F x♯y

