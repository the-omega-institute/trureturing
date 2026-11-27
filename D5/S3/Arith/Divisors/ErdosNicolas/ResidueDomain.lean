/- GID: D5/S3/Arith/Divisors/ErdosNicolas/ResidueDomain
   generality: I
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: none
   digest: Prime-list exponent coordinates faithfully represent the original residue box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Classification
import D5.S3.Arith.Divisors.ErdosNicolas.DivisorChecker
import D5.S3.Arith.Divisors.ErdosNicolas.ResidueTree
import Mathlib.Data.List.FinRange

/-! Remove only forced-zero composite coordinates, retaining every prime exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- A prime absent from all prime bases cannot divide the represented factorization. -/
private theorem prime_not_dvd_factorValue {p : ℕ} (hp : p.Prime) (fs : List (ℕ × ℕ))
    (hfs : ∀ v ∈ fs, v.1.Prime ∧ p ≠ v.1) : ¬p ∣ factorValue fs := by
  induction fs with
  | nil => simpa [factorValue] using hp.not_dvd_one
  | cons v fs ih =>
    rcases v with ⟨q, a⟩
    have hq := hfs (q, a) (by simp)
    intro hd
    rcases hp.dvd_mul.mp hd with hpow | htail
    · exact hq.2 ((Nat.prime_dvd_prime_iff_eq hp hq.1).mp (hp.dvd_of_dvd_pow hpow))
    · exact ih (fun v hv => hfs v (by simp [hv])) htail

/-- Distinct prime bases certify every choice of their natural exponents. -/
private theorem checkFactors_of_primes {fs : List (ℕ × ℕ)}
    (hn : (fs.map Prod.fst).Nodup) (hp : ∀ v ∈ fs, v.1.Prime) :
    checkFactors fs = true := by
  induction fs with
  | nil => rfl
  | cons v fs ih =>
    have hn' := List.nodup_cons.mp hn
    have hpv := hp v (by simp)
    have hfree : ¬v.1 ∣ factorValue fs := by
      apply prime_not_dvd_factorValue hpv fs
      intro w hw
      refine ⟨hp w (by simp [hw]), ?_⟩
      intro he
      exact hn'.1 (List.mem_map.mpr ⟨w, hw, he.symm⟩)
    simp only [checkFactors, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hpv, hfree⟩, ih hn'.2 (fun w hw => hp w (by simp [hw]))⟩

/-- All prime coordinates strictly below the maximum prime, in increasing order. -/
def residuePrimeCoords (p : ℕ) : List (Fin p) :=
  (List.finRange p).filter fun q => q.val.Prime

/-- Exact exponent list presented to the finite prefix tree. -/
def residueExponents (p : ℕ) (v : Fin p → ℕ) : List ℕ :=
  (residuePrimeCoords p).map v

/-- Exponent caps in the same order as the prime coordinates. -/
def residueCaps (p : ℕ) : List ℕ :=
  (residuePrimeCoords p).map fun q => residueCap q.val

/-- Prime factor data for the part below the maximum prime. -/
def residueFactorData (p : ℕ) (v : Fin p → ℕ) : List (ℕ × ℕ) :=
  (residuePrimeCoords p).map fun q => (q.val, v q)

private theorem residue_coord_prime {p : ℕ} {q : Fin p}
    (hq : q ∈ residuePrimeCoords p) : q.val.Prime := by
  exact of_decide_eq_true (List.mem_filter.mp hq).2

private theorem residue_coords_nodup (p : ℕ) : (residuePrimeCoords p).Nodup :=
  (List.nodup_finRange p).filter _

/-- Every original vector, including all prime exponents, satisfies the tree's list caps. -/
theorem residueExponents_bounded {p : ℕ} {v : Fin p → ℕ} (hv : v ∈ residueBox p) :
    List.Forall₂ (· ≤ ·) (residueExponents p v) (residueCaps p) := by
  have hb : ∀ q ∈ residuePrimeCoords p, v q ≤ residueCap q.val := by
    intro q hq
    have hh := (Fintype.mem_piFinset.mp hv) q
    have hp := residue_coord_prime hq
    simpa only [if_pos hp, mem_range, Nat.lt_add_one_iff] using hh
  unfold residueExponents residueCaps
  revert hb
  induction residuePrimeCoords p with
  | nil => intro _; exact List.Forall₂.nil
  | cons q qs ih =>
    intro hb
    exact List.Forall₂.cons (hb q (by simp)) (ih (fun r hr => hb r (by simp [hr])))

private theorem factorValue_map {α : Type*} (xs : List α) (p a : α → ℕ) :
    factorValue (xs.map fun x => (p x, a x)) = (xs.map fun x => p x ^ a x).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [factorValue, ih]

private theorem prod_list_finset {α : Type*} [DecidableEq α]
    (xs : List α) (hx : xs.Nodup) (g : α → ℕ) :
    (xs.map g).prod = ∏ x ∈ xs.toFinset, g x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := List.nodup_cons.mp hx
    simp [List.toFinset_cons, hh.1, ih hh.2]

/-- Removing forced-zero coordinates preserves the integer represented by the original box. -/
private theorem residueFactorData_value {p : ℕ} {v : Fin p → ℕ} (hv : v ∈ residueBox p) :
    factorValue (residueFactorData p v) = ∏ q, q.val ^ v q := by
  rw [residueFactorData, factorValue_map,
    prod_list_finset _ (residue_coords_nodup p)]
  have he : (residuePrimeCoords p).toFinset = univ.filter fun q : Fin p => q.val.Prime := by
    ext q
    simp [residuePrimeCoords]
  rw [he]
  apply prod_subset (filter_subset _ _)
  intro q hq hnot
  have hprime : ¬q.val.Prime := by simpa using hnot
  have hb := (Fintype.mem_piFinset.mp hv) q
  have hz : v q = 0 := by
    simpa only [if_neg hprime, zero_add, mem_range, Nat.lt_one_iff] using hb
  simp [hz]

/-- Every factor list obtained from the original box is a valid complete prime factorization. -/
theorem residueFactorData_checked (p : ℕ) (v : Fin p → ℕ) :
    checkFactors (residueFactorData p v) = true := by
  apply checkFactors_of_primes
  · simp only [residueFactorData, List.map_map, Function.comp_def]
    apply (residue_coords_nodup p).map
    exact Fin.val_injective
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
    exact residue_coord_prime hq

/-- The largest prime is absent from all remaining factor bases. -/
theorem residueFactorData_primeFree {p : ℕ} (hp : p.Prime) (v : Fin p → ℕ) :
    ¬p ∣ factorValue (residueFactorData p v) := by
  apply prime_not_dvd_factorValue hp
  intro w hw
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
  exact ⟨residue_coord_prime hq, by have := q.isLt; omega⟩

/-- The original target value is exactly the maximum prime times the factor-list value. -/
private theorem residueBoxValue_factorData {p : ℕ} {v : Fin p → ℕ} (hv : v ∈ residueBox p) :
    residueBoxValue p v = p * factorValue (residueFactorData p v) := by
  rw [residueBoxValue, residueFactorData_value hv]

/-- A verified list-domain theorem suffices for the original coordinate-domain certificate. -/
theorem residueBox_step_of_factorData {p : ℕ} (hp : p.Prime)
    (h : ∀ v ∈ residueBox p,
      hHat (factorValue (residueFactorData p v)) ≤
          ((factorValue (residueFactorData p v)).divisors.card : ℚ) →
      hHat (p * factorValue (residueFactorData p v)) <
          ((p * factorValue (residueFactorData p v)).divisors.card : ℚ)) :
    ∀ v ∈ residueBox p,
      hHat (residueBoxValue p v / p) ≤ ((residueBoxValue p v / p).divisors.card : ℚ) →
      hHat (residueBoxValue p v) < ((residueBoxValue p v).divisors.card : ℚ) := by
  intro v hv hinput
  rw [residueBoxValue_factorData hv, Nat.mul_div_right _ hp.pos] at hinput
  rw [residueBoxValue_factorData hv]
  exact h v hv hinput

#print axioms prime_not_dvd_factorValue
#print axioms checkFactors_of_primes
#print axioms residueExponents_bounded
#print axioms residueFactorData_value
#print axioms residueFactorData_checked
#print axioms residueFactorData_primeFree
#print axioms residueBoxValue_factorData
#print axioms residueBox_step_of_factorData

end D5.S3.Arith.ErdosNicolas
