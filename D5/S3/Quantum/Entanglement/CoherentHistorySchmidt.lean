/- GID: D5/S3/Quantum/Entanglement/CoherentHistorySchmidt
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/CoherentHistorySchmidt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform word histories have exact cut ranks and binomial Schmidt weights. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import Mathlib.LinearAlgebra.Matrix.Rank

/- Continuation at the frozen OccupancyWordSectors foundation. The new constructions
are the actual word-matrix factorization and representative diagonal restriction;
counting and sector Gram identities are reused. The 5040 values are transported
from BoundedTimeSlice, with no new enumeration. This general foundation does not
construct the fixed-register pure-state circuit required by the complete atom. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.CoherentHistorySchmidt

noncomputable section
open scoped BigOperators
open OccupancyWordSectors

variable {α : Type*} [Fintype α] [DecidableEq α]

def historyAmplitude (a : Multiset α) (n : ℕ) : ℂ :=
  (Real.sqrt (multiplicity n a : ℝ) : ℂ)⁻¹

/-- The bipartite coefficients of the uniform state on actual legal words. -/
def coefficientMatrix (a : Multiset α) (t s : ℕ) : Matrix (Word α t) (Word α s) ℂ :=
  fun u v => if occupation (Fin.append u v) = a then historyAmplitude a (t + s) else 0

theorem coefficient_eq_uniform_word (a : Multiset α) (t s : ℕ)
    (u : Word α t) (v : Word α s) :
    coefficientMatrix a t s u v = sectorVector (t + s) a (Fin.append u v) := by
  simp [coefficientMatrix, sectorVector, sectorWords, historyAmplitude]

private theorem amplitude_ne_zero {a : Multiset α} {n : ℕ} (h : a.card = n) :
    historyAmplitude a n ≠ 0 := by
  have hp : (0 : ℝ) < multiplicity n a := by exact_mod_cast multiplicity_pos a h
  apply inv_ne_zero
  exact_mod_cast (Real.sqrt_pos.mpr hp).ne'

omit [Fintype α] in
private theorem complement_iff {a b c : Multiset α} (hb : b ≤ a) :
    b + c = a ↔ c = a - b := by
  constructor
  · intro h
    rw [← h, add_comm b c, Multiset.add_sub_cancel_right]
  · intro h
    rw [h, add_comm, Multiset.sub_add_cancel hb]

omit [Fintype α] in
theorem legal_iff {a : Multiset α} {t s : ℕ} (u : Word α t) (v : Word α s) :
    occupation (Fin.append u v) = a ↔
      ∃ b : Boundary a t, occupation u = b.val ∧ occupation v = a - b.val := by
  rw [occupation_append]
  constructor
  · intro h
    have hu : occupation u ≤ a := h ▸ Multiset.le_add_right (occupation u) (occupation v)
    let b : Boundary a t := ⟨occupation u, by
      simp [boundaries, Multiset.mem_powersetCard, hu]⟩
    exact ⟨b, rfl, (complement_iff hu).mp h⟩
  · rintro ⟨b, hu, hv⟩
    rw [hu]
    exact (complement_iff (boundary_spec a t b).1).mpr hv

omit [Fintype α] in
private theorem sum_sector {a : Multiset α} {t s : ℕ}
    (u : Word α t) (v : Word α s) (z : ℂ) :
    (∑ b : Boundary a t, if occupation u = b.val ∧ occupation v = a - b.val
      then z else 0) = if occupation (Fin.append u v) = a then z else 0 := by
  classical
  by_cases h : occupation (Fin.append u v) = a
  · obtain ⟨b, hu, hv⟩ := (legal_iff u v).mp h
    rw [Finset.sum_eq_single b]
    · simp [h, hu, hv]
    · intro c _ hcb
      have hc : occupation u ≠ c.val := by
        intro hc
        exact hcb (Subtype.ext (hc.symm.trans hu))
      simp [hc]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    exact if_neg (fun hb => h ((legal_iff u v).mpr ⟨b, hb⟩))

def prefixIncidence (a : Multiset α) (t : ℕ) : Matrix (Word α t) (Boundary a t) ℂ :=
  fun u b => if occupation u = b.val then 1 else 0

def suffixAmplitude (a : Multiset α) (t s : ℕ) : Matrix (Boundary a t) (Word α s) ℂ :=
  fun b v => if occupation v = a - b.val then historyAmplitude a (t + s) else 0

theorem coefficient_factorization (a : Multiset α) (t s : ℕ) :
    coefficientMatrix a t s = prefixIncidence a t * suffixAmplitude a t s := by
  classical
  ext u v
  rw [Matrix.mul_apply]
  change (if occupation (Fin.append u v) = a then historyAmplitude a (t + s) else 0) = _
  rw [← sum_sector u v (historyAmplitude a (t + s))]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hu : occupation u = b.val <;> by_cases hv : occupation v = a - b.val <;>
    simp [prefixIncidence, suffixAmplitude, hu, hv]

def prefixRepresentative {a : Multiset α} {t : ℕ} (b : Boundary a t) : Word α t :=
  representative b.val (boundary_spec a t b).2

def suffixRepresentative {a : Multiset α} {t s : ℕ} (h : a.card = t + s)
    (b : Boundary a t) : Word α s := representative (a - b.val) (complement_card h b)

/-- A diagonal restriction selected from the full word matrix, not a replacement matrix. -/
theorem coefficient_diagonal_restriction {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) :
    (coefficientMatrix a t s).submatrix prefixRepresentative (suffixRepresentative h) =
      Matrix.diagonal (fun _ : Boundary a t => historyAmplitude a (t + s)) := by
  classical
  ext b c
  simp only [Matrix.submatrix_apply, coefficientMatrix, occupation_append,
    prefixRepresentative, suffixRepresentative, occupation_representative, Matrix.diagonal_apply]
  have hc : b.val + (a - c.val) = a ↔ b = c := by
    rw [complement_iff (boundary_spec a t b).1]
    constructor
    · exact fun he => (complement_injective a t he).symm
    · intro he
      subst c
      rfl
  simp only [hc]

/-- Schmidt rank is the rank over C of the actual coefficient matrix. -/
theorem coefficient_rank {a : Multiset α} {t s : ℕ} (h : a.card = t + s) :
    (coefficientMatrix a t s).rank = (boundaries a t).card := by
  classical
  have hcard : Fintype.card (Boundary a t) = (boundaries a t).card :=
    Fintype.card_coe _
  apply le_antisymm
  · rw [coefficient_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans_eq hcard)
  · have hminor := Matrix.rank_submatrix_le (coefficientMatrix a t s)
      (prefixRepresentative (a := a)) (suffixRepresentative h)
    rw [coefficient_diagonal_restriction h, Matrix.rank_diagonal] at hminor
    simpa [amplitude_ne_zero h, hcard] using hminor

def schmidtCoefficient (a : Multiset α) (t s : ℕ) (b : Boundary a t) : ℝ :=
  Real.sqrt (multiplicity t b.val : ℝ) * Real.sqrt (multiplicity s (a - b.val) : ℝ) /
    Real.sqrt (multiplicity (t + s) a : ℝ)

theorem schmidt_coefficient_pos {a : Multiset α} {t s : ℕ} (h : a.card = t + s)
    (b : Boundary a t) : 0 < schmidtCoefficient a t s b := by
  unfold schmidtCoefficient
  apply div_pos (mul_pos (Real.sqrt_pos.mpr _) (Real.sqrt_pos.mpr _)) (Real.sqrt_pos.mpr _)
  · exact_mod_cast multiplicity_pos b.val (boundary_spec a t b).2
  · exact_mod_cast multiplicity_pos (a - b.val) (complement_card h b)
  · exact_mod_cast multiplicity_pos a h

theorem schmidt_coefficient_sq (a : Multiset α) (t s : ℕ) (b : Boundary a t) :
    schmidtCoefficient a t s b ^ 2 =
      (multiplicity t b.val : ℝ) * multiplicity s (a - b.val) / multiplicity (t + s) a := by
  simp [schmidtCoefficient, div_pow, mul_pow, Real.sq_sqrt]

private theorem multiplicity_factorial_spec (a : Multiset α) {n : ℕ} (h : a.card = n) :
    (∏ z : α, Nat.factorial (a.count z)) * multiplicity n a = Nat.factorial n := by
  rw [OccupancyWordSectors.multiplicity, sector_words_card_multinomial a h, Nat.multinomial_spec,
    Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _), h]

/-- The binomial weights are derived from the cardinalities of actual word sectors. -/
theorem schmidt_coefficient_sq_binomial {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) (b : Boundary a t) :
    schmidtCoefficient a t s b ^ 2 =
      (∏ z : α, ((a.count z).choose (b.val.count z) : ℝ)) / ((t + s).choose t : ℝ) := by
  let P (c : Multiset α) := ∏ z : α, Nat.factorial (c.count z)
  let Q := ∏ z : α, (a.count z).choose (b.val.count z)
  have hp (c : Multiset α) : 0 < P c := Finset.prod_pos (fun _ _ => Nat.factorial_pos _)
  have hb : P b.val * multiplicity t b.val = Nat.factorial t :=
    multiplicity_factorial_spec b.val (boundary_spec a t b).2
  have hc : P (a - b.val) * multiplicity s (a - b.val) = Nat.factorial s :=
    multiplicity_factorial_spec (a - b.val) (complement_card h b)
  have ha : P a * multiplicity (t + s) a = Nat.factorial (t + s) :=
    multiplicity_factorial_spec a h
  have hq : Q * P b.val * P (a - b.val) = P a := by
    dsimp [Q, P]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro z _
    rw [Multiset.count_sub]
    exact Nat.choose_mul_factorial_mul_factorial
      (Multiset.count_le_of_le z (boundary_spec a t b).1)
  have hcut : (t + s).choose t * Nat.factorial t * Nat.factorial s =
      Nat.factorial (t + s) := by
    simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right t s)
  have hratio : multiplicity t b.val * multiplicity s (a - b.val) * (t + s).choose t =
      Q * multiplicity (t + s) a := by
    apply Nat.mul_left_cancel (mul_pos (hp b.val) (hp (a - b.val)))
    calc
      (P b.val * P (a - b.val)) *
          (multiplicity t b.val * multiplicity s (a - b.val) * (t + s).choose t) =
          (t + s).choose t * (P b.val * multiplicity t b.val) *
            (P (a - b.val) * multiplicity s (a - b.val)) := by ring
      _ = Nat.factorial (t + s) := by rw [hb, hc, hcut]
      _ = P a * multiplicity (t + s) a := ha.symm
      _ = (P b.val * P (a - b.val)) * (Q * multiplicity (t + s) a) := by
        rw [← hq]
        ring
  have hm : (multiplicity (t + s) a : ℝ) ≠ 0 := by
    exact_mod_cast (multiplicity_pos a h).ne'
  have hn : ((t + s).choose t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right t s)).ne'
  rw [schmidt_coefficient_sq]
  apply (div_eq_div_iff hm hn).mpr
  exact_mod_cast hratio

theorem schmidt_coefficient_eq_sqrt_binomial {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) (b : Boundary a t) :
    schmidtCoefficient a t s b = Real.sqrt
      ((∏ z : α, ((a.count z).choose (b.val.count z) : ℝ)) / ((t + s).choose t : ℝ)) := by
  rw [← schmidt_coefficient_sq_binomial h b, Real.sqrt_sq (schmidt_coefficient_pos h b).le]

theorem normalized_coefficient_factorization {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) (u : Word α t) (v : Word α s) :
    coefficientMatrix a t s u v = ∑ b : Boundary a t,
      (schmidtCoefficient a t s b : ℂ) * sectorVector t b.val u *
        sectorVector s (a - b.val) v := by
  classical
  change (if occupation (Fin.append u v) = a then historyAmplitude a (t + s) else 0) = _
  rw [← sum_sector u v (historyAmplitude a (t + s))]
  apply Finset.sum_congr rfl
  intro b _
  have hpReal : (0 : ℝ) < multiplicity t b.val := by
    exact_mod_cast multiplicity_pos b.val (boundary_spec a t b).2
  have hsReal : (0 : ℝ) < multiplicity s (a - b.val) := by
    exact_mod_cast multiplicity_pos (a - b.val) (complement_card h b)
  have hp : (Real.sqrt (multiplicity t b.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpReal).ne'
  have hs : (Real.sqrt (multiplicity s (a - b.val) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hsReal).ne'
  by_cases hu : occupation u = b.val <;> by_cases hv : occupation v = a - b.val
  · simp only [hu, hv, and_self, if_true, sectorVector, sectorWords, Finset.mem_filter,
      Finset.mem_univ, schmidtCoefficient, Complex.ofReal_div, Complex.ofReal_mul,
      historyAmplitude]
    field_simp
  · simp [sectorVector, sectorWords, hu, hv]
  · simp [sectorVector, sectorWords, hu, hv]
  · simp [sectorVector, sectorWords, hu, hv]

theorem cut_sector_gram {a : Multiset α} {t s : ℕ} (h : a.card = t + s)
    (b c : Boundary a t) :
    (∑ u : Word α t, star (sectorVector t b.val u) * sectorVector t c.val u =
      if b = c then 1 else 0) ∧
    (∑ v : Word α s, star (sectorVector s (a - b.val) v) * sectorVector s (a - c.val) v =
      if b = c then 1 else 0) := by
  constructor
  · rw [sector_gram b.val c.val (boundary_spec a t b).2]
    simp only [Subtype.val_inj]
  · rw [sector_gram (a - b.val) (a - c.val) (complement_card h b)]
    simp only [(complement_injective a t).eq_iff]

/-- The largest actual boundary carrier, including the zero and full cuts. -/
def boundaryMaximum (a : Multiset α) : ℕ :=
  (Finset.range (a.card + 1)).sup (fun t => (boundaries a t).card)

theorem history_max_schmidt_rank (a : Multiset α) :
    (Finset.range (a.card + 1)).sup (fun t => (coefficientMatrix a t (a.card - t)).rank) =
      boundaryMaximum a := by
  apply Finset.sup_congr rfl
  intro t ht
  exact coefficient_rank (by have := Finset.mem_range.mp ht; omega)

open D5.S1.Ledger.BoundedTimeSlice

def occupation5040 : Multiset (Option (Fin 3)) := capacityOccupation 4 tailCapacities5040

theorem occupation_5040_card : occupation5040.card = 8 := by
  rw [occupation5040, capacity_occupation_card, time_slice_5040_capacities.2.1]

theorem history_5040_rank_eq_sliceCount (t : ℕ) (ht : t ≤ 8) :
    (coefficientMatrix occupation5040 t (8 - t)).rank = timeSlice5040Count t := by
  rw [coefficient_rank (by rw [occupation_5040_card]; omega)]
  exact boundary_count_eq_sliceCount 4 tailCapacities5040 t

theorem history_5040_rank_sequence :
    (List.range 9).map (fun t => (coefficientMatrix occupation5040 t (8 - t)).rank) =
      [1, 4, 8, 11, 12, 11, 8, 4, 1] := by
  rw [← time_slice_5040_sequence]
  apply List.map_congr_left
  intro t ht
  exact history_5040_rank_eq_sliceCount t (by have := List.mem_range.mp ht; omega)

theorem history_5040_rank_bound (t : ℕ) (ht : t ≤ 8) :
    (coefficientMatrix occupation5040 t (8 - t)).rank ≤ 12 ∧
      ((coefficientMatrix occupation5040 t (8 - t)).rank = 12 ↔ t = 4) := by
  rw [history_5040_rank_eq_sliceCount t ht]
  exact time_slice_5040_unique_maximum t

theorem occupation_5040_boundary_maximum : boundaryMaximum occupation5040 = 12 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro t _
    rw [occupation5040, boundary_count_eq_sliceCount]
    exact (time_slice_5040_unique_maximum t).1
  · have h4 : (boundaries occupation5040 4).card = 12 := by
      rw [occupation5040, boundary_count_eq_sliceCount]
      exact (time_slice_5040_unique_maximum 4).2.mpr rfl
    exact Finset.le_sup_of_le (by simp [occupation_5040_card]) (le_of_eq h4.symm)

theorem history_5040_max_schmidt_rank :
    (Finset.range 9).sup (fun t => (coefficientMatrix occupation5040 t (8 - t)).rank) = 12 ∧
      (coefficientMatrix occupation5040 4 4).rank = 12 := by
  constructor
  · have h := history_max_schmidt_rank occupation5040
    rw [occupation_5040_card, occupation_5040_boundary_maximum] at h
    exact h
  · exact (history_5040_rank_bound 4 (by decide)).2.mpr rfl

example : ∃ a : Multiset Bool, a.card = 1 + 2 := ⟨{true, false, true}, by decide⟩

example : (coefficientMatrix ({true, false, true} : Multiset Bool) 1 2).rank =
    (boundaries ({true, false, true} : Multiset Bool) 1).card := coefficient_rank (by decide)

example (a : Multiset α) : (coefficientMatrix a 0 a.card).rank = (boundaries a 0).card :=
  coefficient_rank (by simp)

example (a : Multiset α) : (coefficientMatrix a a.card 0).rank =
    (boundaries a a.card).card := coefficient_rank (by simp)

example : ∃ a : Multiset (Fin 4), a.card = 4 + 4 ∧
    (coefficientMatrix a 4 4).rank = (boundaries a 4).card :=
  ⟨{0, 0, 0, 0, 1, 1, 2, 3}, by decide, coefficient_rank (by decide)⟩

end
end D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
