/- GID: D5/S3/PrimeForms/Splitting/HilbertReciprocityParity
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/HilbertReciprocityParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite sign code gives local recovery, omission witness, and degenerate audits. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Repository searches for four Hilbert-symbol spellings and parity-code names found no
     implementation. `ReciprocityParityErrorDetection` proves the already-bound flip theorem
     but defines no code or recovery law. `LocalReciprocityMatrix` is a three-valued Legendre
     matrix, not a global finite-support sign constraint.
   * Pinned Mathlib hits include `Finset.mul_prod_erase`, `Finset.prod_erase`,
     `Finset.prod_eq_one`, `Int.units_eq_one_or`, `Units.val`, `Function.mulSupport`,
     `Finsupp`, and `ZMod 2`. The proof uses the first and fourth hits. A `Finset` carrier
     keeps multiplicative identity as the off-support value without an additive recoding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.HilbertReciprocityParity

open scoped BigOperators

universe u

/-- Finite-support sign profiles satisfying one global multiplicative parity check. -/
def hilbertReciprocityCode {ι : Type u} [DecidableEq ι] : Set (ι → ℤˣ) :=
  { profile | ∃ places : Finset ι,
      (∀ place, place ∉ places → profile place = 1) ∧
        ∏ place ∈ places, profile place = 1 }

/-- A finite sign profile with product one is determined at one place by all other places. -/
theorem local_sign_eq_product_of_other_places {ι : Type u} [DecidableEq ι]
    (places : Finset ι) (profile : ι → ℤˣ) (chosen : ι)
    (hSupport : ∀ place, place ∉ places → profile place = 1)
    (hReciprocity : ∏ place ∈ places, profile place = 1) :
    profile chosen = ∏ place ∈ places.erase chosen, profile place := by
  by_cases hchosen : chosen ∈ places
  · have hfactor :
        profile chosen * (∏ place ∈ places.erase chosen, profile place) = 1 := by
      rw [Finset.mul_prod_erase places profile hchosen, hReciprocity]
    have hself : profile chosen * profile chosen = 1 := by
      rcases Int.units_eq_one_or (profile chosen) with hone | hneg
      · simp [hone]
      · simp [hneg]
    calc
      profile chosen = profile chosen * 1 := by simp
      _ = profile chosen *
          (profile chosen * ∏ place ∈ places.erase chosen, profile place) := by
        rw [hfactor]
      _ = (profile chosen * profile chosen) *
          ∏ place ∈ places.erase chosen, profile place := by
        rw [mul_assoc]
      _ = ∏ place ∈ places.erase chosen, profile place := by rw [hself, one_mul]
  · rw [Finset.erase_eq_self.mpr hchosen, hSupport chosen hchosen, hReciprocity]

#print axioms local_sign_eq_product_of_other_places

/-- Two negative signs pass globally, but omitting either coordinate leaves product `-1`. -/
theorem omitted_place_can_break_reciprocity_check :
    let profile : Fin 2 → ℤˣ := fun _ => -1
    profile ∈ hilbertReciprocityCode ∧
      (∏ place ∈ Finset.univ, profile place) = 1 ∧
        ∀ omitted : Fin 2,
          (∏ place ∈ Finset.univ.erase omitted, profile place) = -1 := by
  dsimp only
  constructor
  · change ∃ places : Finset (Fin 2),
      (∀ place, place ∉ places → (-1 : ℤˣ) = 1) ∧
        ∏ _place ∈ places, (-1 : ℤˣ) = 1
    refine ⟨Finset.univ, ?_, ?_⟩
    · simp
    · decide
  constructor
  · decide
  · intro omitted
    fin_cases omitted <;> decide

#print axioms omitted_place_can_break_reciprocity_check

/-- Empty, singleton, and all-one sign profiles have their expected boundary behavior. -/
theorem reciprocity_code_degeneracy_audit :
    (fun _ : Empty => (1 : ℤˣ)) ∈ hilbertReciprocityCode ∧
      (∀ profile : Unit → ℤˣ,
        profile ∈ hilbertReciprocityCode → profile () = 1) ∧
      ∀ (ι : Type u) [DecidableEq ι],
        (fun _ : ι => (1 : ℤˣ)) ∈ hilbertReciprocityCode := by
  constructor
  · change ∃ places : Finset Empty,
      (∀ place, place ∉ places → (1 : ℤˣ) = 1) ∧
        ∏ _place ∈ places, (1 : ℤˣ) = 1
    exact ⟨∅, by simp, by simp⟩
  constructor
  · intro profile hProfile
    change ∃ places : Finset Unit,
      (∀ place, place ∉ places → profile place = 1) ∧
        ∏ place ∈ places, profile place = 1 at hProfile
    rcases hProfile with ⟨places, hSupport, hReciprocity⟩
    have hlocal := local_sign_eq_product_of_other_places
      places profile () hSupport hReciprocity
    have herase : places.erase () = ∅ := by
      ext place
      simp [Subsingleton.elim place ()]
    simpa [herase] using hlocal
  · intro ι _
    change ∃ places : Finset ι,
      (∀ place, place ∉ places → (1 : ℤˣ) = 1) ∧
        ∏ _place ∈ places, (1 : ℤˣ) = 1
    exact ⟨∅, by simp, by simp⟩

#print axioms reciprocity_code_degeneracy_audit

/-- Without the product-one premise, a supported one-place profile violates recovery. -/
theorem reciprocity_product_is_necessary :
    let places : Finset (Fin 1) := Finset.univ
    let profile : Fin 1 → ℤˣ := fun _ => -1
    (∀ place, place ∉ places → profile place = 1) ∧
      (∏ place ∈ places, profile place) ≠ 1 ∧
      profile 0 ≠ ∏ place ∈ places.erase 0, profile place := by
  decide

#print axioms reciprocity_product_is_necessary

/-- Product one on a claimed carrier does not control a nontrivial sign outside it. -/
theorem finite_support_coverage_is_necessary :
    let places : Finset (Fin 2) := {0}
    let profile : Fin 2 → ℤˣ := fun place => if place = 1 then -1 else 1
    (∏ place ∈ places, profile place) = 1 ∧
      ¬(∀ place, place ∉ places → profile place = 1) ∧
      profile 1 ≠ ∏ place ∈ places.erase 1, profile place := by
  decide

#print axioms finite_support_coverage_is_necessary

/- Assumption and degeneracy audit:
   * `hReciprocity` is assumed, not proved. For Hilbert symbols it is supplied by the external
     classical product formula, which is intentionally not a Lean anchor in this module.
   * `hSupport` and `hReciprocity` are both used. The two named necessity theorems show that
     deleting either condition invalidates local recovery. `DecidableEq` is only the
     computational interface required by `Finset`; it has no proposition-level counterexample.
   * No field, characteristic, place, or primality hypothesis survives abstraction. Primality
     is therefore not load-bearing here: the index type is arbitrary.
   * The audit theorem covers the empty carrier, a singleton carrier, and an all-one profile.
     The omission theorem supplies the exactly-two-negative profile and the load-bearing-place
     witness required by the source principle. Hilbert symbols are instances, not constructed. -/

end D5.S3.PrimeForms.Splitting.HilbertReciprocityParity
