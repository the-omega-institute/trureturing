/- GID: D5/S3/FiniteGroups/NikolovSegal/BoundedSimpleTwistedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/BoundedSimpleTwistedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.SmallTwistedGeneration
import D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth

set_option autoImplicit false
open scoped Pointwise

namespace NikolovSegal.SmallTwistedProduct
open Equation47WordCoupling
universe u
variable {S : Type u} [Group S]

section Enumeration
variable [Fintype S] [DecidableEq S]

noncomputable def twistedFinset (a b : MulAut S) : Finset S := by
  classical
  exact (twistedSet a b).toFinset

@[simp] theorem mem_twistedFinset (a b : MulAut S) (t : S) :
    t ∈ twistedFinset a b ↔ ∃ x y, twistedValue a b x y = t := by
  classical
  exact Set.mem_toFinset

theorem one_mem_twistedFinset (a b : MulAut S) : 1 ∈ twistedFinset a b :=
  (mem_twistedFinset a b 1).mpr ⟨1,1,by simp [twistedValue]⟩

theorem twistedFinset_closure_top [IsSimpleGroup S] (hn : ¬IsMulCommutative S)
    (a b : MulAut S) : Subgroup.closure (twistedFinset a b : Set S) = ⊤ := by
  have he : (twistedFinset a b : Set S) = twistedSet a b := by
    ext t; exact mem_twistedFinset a b t
  rw [he]
  exact twisted_closure_top hn a b

/-- Actual ordered products for a prescribed arbitrary automorphism tuple. -/
noncomputable def productRange {d : ℕ} (a b : Fin d → MulAut S) : Finset S := by
  classical
  exact {t | ∃ xi eta : Fin d → S,
    orderedProduct (fun i => twistedValue (a i) (b i) (xi i) (eta i)) = t}.toFinset

@[simp] theorem mem_productRange {d : ℕ} (a b : Fin d → MulAut S) (t : S) :
    t ∈ productRange a b ↔ ∃ xi eta : Fin d → S,
      orderedProduct (fun i => twistedValue (a i) (b i) (xi i) (eta i)) = t := by
  classical
  simp [productRange]

theorem productRange_zero (a b : Fin 0 → MulAut S) : productRange a b = {1} := by
  classical
  ext t
  simp [orderedProduct,eq_comm]

theorem one_mem_productRange {d : ℕ} (a b : Fin d → MulAut S) : 1 ∈ productRange a b := by
  apply (mem_productRange a b 1).mpr
  refine ⟨fun _ => 1,fun _ => 1,?_⟩
  simp [orderedProduct,twistedValue]

/-- Append the LAST prescribed twisted factor, preserving the actual order.
The witnesses are constructed with Fin.snoc, not by commuting any factors. -/
theorem productRange_succ {d : ℕ} (a b : Fin (d+1) → MulAut S) :
    productRange a b =
      productRange (fun j => a j.castSucc) (fun j => b j.castSucc) *
        twistedFinset (a (Fin.last d)) (b (Fin.last d)) := by
  have hprod : ∀ f : Fin (d+1) → S, orderedProduct f =
      orderedProduct (fun j => f j.castSucc) * f (Fin.last d) := by
    intro f
    simp only [orderedProduct,List.ofFn_succ',List.prod_concat]
  ext t
  rw [mem_productRange,Finset.mem_mul]
  constructor
  · rintro ⟨xi,eta,he⟩
    refine ⟨orderedProduct (fun j : Fin d => twistedValue (a j.castSucc) (b j.castSucc)
      (xi j.castSucc) (eta j.castSucc)),?_,
      twistedValue (a (Fin.last d)) (b (Fin.last d)) (xi (Fin.last d)) (eta (Fin.last d)),?_,?_⟩
    · exact (mem_productRange _ _ _).mpr ⟨fun j => xi j.castSucc,fun j => eta j.castSucc,rfl⟩
    · exact (mem_twistedFinset _ _ _).mpr ⟨xi (Fin.last d),eta (Fin.last d),rfl⟩
    · rw [hprod] at he
      exact he
  · rintro ⟨u,hu,v,hv,he⟩
    obtain ⟨xi,eta,hprefix⟩ := (mem_productRange _ _ _).mp hu
    obtain ⟨x,y,hlast⟩ := (mem_twistedFinset _ _ _).mp hv
    refine ⟨Fin.snoc xi x,Fin.snoc eta y,?_⟩
    rw [hprod]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    rw [hprefix,hlast]
    exact he

/-- Every prefix contains 1, and each successive prescribed generating set
strictly grows the range until it becomes the whole finite group. -/
theorem productRange_full_or_card [IsSimpleGroup S] (hn : ¬IsMulCommutative S)
    (d : ℕ) (a b : Fin d → MulAut S) :
    productRange a b = Finset.univ ∨ d+1 ≤ (productRange a b).card := by
  induction d with
  | zero => right; rw [productRange_zero]; simp
  | succ d ih =>
    let A := productRange (fun j => a j.castSucc) (fun j => b j.castSucc)
    let T := twistedFinset (a (Fin.last d)) (b (Fin.last d))
    rcases ih (fun j => a j.castSucc) (fun j => b j.castSucc) with hfull | hcard
    · left
      rw [productRange_succ,hfull]
      exact Finset.univ_mul_of_one_mem (one_mem_twistedFinset _ _)
    · by_cases hfull : A = Finset.univ
      · left
        rw [productRange_succ]
        change A*T = Finset.univ
        rw [hfull]
        exact Finset.univ_mul_of_one_mem (one_mem_twistedFinset _ _)
      · right
        have hg : A.card < (A*T).card := card_mul_strict_of_generating A T
          ⟨1,one_mem_productRange _ _⟩ hfull (one_mem_twistedFinset _ _)
          (twistedFinset_closure_top hn _ _)
        rw [productRange_succ]
        change d+1+1 ≤ (A*T).card
        change d+1 ≤ A.card at hcard
        omega

theorem productRange_eq_univ [IsSimpleGroup S] (hn : ¬IsMulCommutative S)
    {d : ℕ} (a b : Fin d → MulAut S) (hcard : Fintype.card S ≤ d+1) :
    productRange a b = Finset.univ := by
  rcases productRange_full_or_card hn d a b with hfull | hsize
  · exact hfull
  · apply Finset.eq_univ_of_card
    have hle := (productRange a b).card_le_univ
    omega

end Enumeration

/-- Bounded-small actual twisted PRODUCT coverage for EVERY ordered tuple.
The sharp elementary growth bound is card(S)-1; no inner, constant or commuting
automorphism assumption, target restriction, perfectness or coverage input. -/
theorem twisted_input_of_card_le_succ [Finite S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) {D : ℕ} (hcard : Nat.card S ≤ D+1) :
    PartIITwistedProductInput S D := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  intro a b target
  have hsize : Fintype.card S ≤ D+1 := by simpa only [Nat.card_eq_fintype_card] using hcard
  have hfull := productRange_eq_univ hn a b hsize
  have htarget : target ∈ productRange a b := by rw [hfull]; simp
  exact (mem_productRange a b target).mp htarget

theorem twisted_input_of_card_le [Finite S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) {D : ℕ} (hcard : Nat.card S ≤ D) :
    PartIITwistedProductInput S D :=
  twisted_input_of_card_le_succ hn (hcard.trans (Nat.le_succ D))

/-- A single length C+1 covers ALL noncommutative finite simple groups of
cardinality at most C, uniformly before all automorphisms and targets. -/
theorem bounded_small_simple_twisted_input (C : ℕ) [Finite S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) (hcard : Nat.card S ≤ C) :
    PartIITwistedProductInput S (C+1) := by
  apply twisted_input_of_card_le_succ hn
  omega

end NikolovSegal.SmallTwistedProduct
