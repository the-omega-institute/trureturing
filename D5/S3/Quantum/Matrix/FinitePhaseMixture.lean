/- GID: D5/S3/Quantum/Matrix/FinitePhaseMixture
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/FinitePhaseMixture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small total off-diagonal mass gives an exact finite mixture of phase outer products. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
open scoped BigOperators ComplexConjugate
open Finset
namespace D5.S3.Quantum.Matrix.FinitePhaseMixture

/-- A Hermitian unit-diagonal matrix of off-diagonal mass at most one is an
exact finite convex mixture of unit-coordinate outer products. -/
theorem result (d : ℕ) (_hd : 1 ≤ d) (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (hdiag : ∀ i, H i i = 1)
    (hmass : (∑ i, ∑ j, if i < j then ‖H i j‖ else 0) ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ (p : Fin n → ℝ) (z : Fin n → Fin d → ℂ),
      (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
      (∀ a i, ‖z a i‖ = 1) ∧
      ∀ i j, H i j = ∑ a, (p a : ℂ) * z a i * conj (z a j) := by
  classical
  -- Uniform signs cancel every moment between distinct coordinates.
  let S := Fin d → Bool
  let e : S → Fin d → ℂ := fun s i => if s i then -1 else 1
  have he (s : S) (i : Fin d) : ‖e s i‖ = 1 := by
    dsimp [e]; split <;> simp
  have heconj (s : S) (i : Fin d) : conj (e s i) = e s i := by
    dsimp [e]; split <;> simp
  have hesq (s : S) (i : Fin d) : e s i * e s i = 1 := by
    dsimp [e]; split <;> norm_num
  have hmoment (i j : Fin d) :
      (∑ s : S, e s i * e s j) = if i = j then (Fintype.card S : ℂ) else 0 := by
    by_cases hij : i = j
    · subst j; simp [hesq]
    · rw [if_neg hij]
      let flip : S → S := fun s => Function.update s i (!(s i))
      have hf (s : S) : e (flip s) i = -e s i := by
        simp only [e, flip, Function.update_self]
        cases s i <;> norm_num
      have hg (s : S) : e (flip s) j = e s j := by
        simp [e, flip, Function.update_of_ne (Ne.symm hij)]
      apply Finset.sum_ninvolution flip
      · intro s; rw [hf, hg]; ring
      · intro s _ h
        have hh := congrFun h i
        simp only [flip, Function.update_self] at hh
        cases s i <;> simp_all
      · intro s; exact mem_univ _
      · intro s; funext k
        by_cases hk : k = i
        · subst k; simp [flip]
        · simp [flip, Function.update_of_ne hk]
  let N : ℝ := Fintype.card S
  have hN : 0 < N := by
    dsimp [N]; exact_mod_cast Fintype.card_pos
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  -- The zero entry receives an arbitrary unit phase and zero outer weight.
  let phase : ℂ → ℂ := fun c => if c = 0 then 1 else conj c / (‖c‖ : ℂ)
  have hp (c : ℂ) : ‖phase c‖ = 1 := by
    by_cases hc : c = 0
    · simp [phase, hc]
    · simp [phase, hc, Complex.norm_real]
  have hpval (c : ℂ) : (‖c‖ : ℂ) * conj (phase c) = c := by
    by_cases hc : c = 0
    · simp [hc]
    · have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
      simp [phase, hc, map_div₀, mul_div_cancel₀ _ hn]
  let mass : Fin d × Fin d → ℝ := fun q => if q.1 < q.2 then ‖H q.1 q.2‖ else 0
  let total : ℝ := ∑ q, mass q
  have ht : total ≤ 1 := by simpa [total, mass, Fintype.sum_prod_type] using hmass
  let w : Option (Fin d × Fin d) → ℝ := fun q =>
    match q with | none => 1 - total | some q => mass q
  let v : Option (Fin d × Fin d) → S → Fin d → ℂ := fun q s k =>
    match q with
    | none => e s k
    | some q => if k = q.2 then phase (H q.1 q.2) * e s q.1 else e s k
  have hw (q) : 0 ≤ w q := by
    cases q with
    | none => exact sub_nonneg.mpr ht
    | some q => dsimp [w, mass]; split <;> positivity
  have hw_sum : ∑ q, w q = 1 := by
    simp [w, Fintype.sum_option, total]
  have hv (q s k) : ‖v q s k‖ = 1 := by
    cases q with
    | none => exact he s k
    | some q => dsimp [v]; split <;> simp [hp, he]
  have hvmoment (q : Fin d × Fin d) (hq : q.1 < q.2) (i j : Fin d) :
      (∑ s : S, v (some q) s i * conj (v (some q) s j)) =
        (N : ℂ) * (if i = j then 1 else
          if i = q.1 ∧ j = q.2 then conj (phase (H q.1 q.2)) else
          if i = q.2 ∧ j = q.1 then phase (H q.1 q.2) else 0) := by
    have hqne := ne_of_lt hq
    by_cases hij : i = j
    · subst j
      simp only [Complex.mul_conj', hv, one_pow, Complex.ofReal_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      simp [N]
    · by_cases hi : i = q.2 <;> by_cases hj : j = q.2
      · exact (hij (hi.trans hj.symm)).elim
      · subst i
        simp only [v, if_pos rfl, if_neg hj, heconj]
        simp_rw [mul_assoc, ← Finset.mul_sum, hmoment]
        by_cases hj1 : j = q.1
        · subst j; simp [hqne, Ne.symm hqne, N, mul_comm]
        · simp [Ne.symm hqne, hj, hij, hj1, Ne.symm hj1]
      · subst j
        simp only [v, if_neg hi, if_pos rfl, map_mul, heconj]
        simp_rw [mul_left_comm (e _ _) (conj _), ← Finset.mul_sum, hmoment]
        by_cases hi1 : i = q.1
        · subst i; simp [N, mul_comm]
        · simp [hi, hi1]
      · simp [v, hi, hj, heconj, hmoment, hij]
  -- Duplicate labels keep a uniform sign space in every dimension.
  let A := Option (Fin d × Fin d) × S
  let p : A → ℝ := fun a => w a.1 / N
  let z : A → Fin d → ℂ := fun a => v a.1 a.2
  have hpnonneg (a : A) : 0 ≤ p a := div_nonneg (hw _) (le_of_lt hN)
  have hpsum : ∑ a : A, p a = 1 := by
    dsimp [A] at p ⊢
    simp only [p, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    change (∑ q, N * (w q / N)) = 1
    simp_rw [mul_div_cancel₀ _ (ne_of_gt hN)]
    exact hw_sum
  have hz (a : A) (i) : ‖z a i‖ = 1 := hv _ _ _
  have hupper (i j : Fin d) (hij : i < j) :
      (∑ a : A, (p a : ℂ) * z a i * conj (z a j)) = H i j := by
    change (∑ a : Option (Fin d × Fin d) × S,
      ((w a.1 / N : ℝ) : ℂ) * v a.1 a.2 i * conj (v a.1 a.2 j)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [Complex.ofReal_div, mul_assoc, ← Finset.mul_sum]
    rw [Fintype.sum_option]
    have hnone : (∑ s : S, v none s i * conj (v none s j)) = 0 := by
      simpa only [v, heconj, if_neg (ne_of_lt hij)] using hmoment i j
    rw [hnone, mul_zero, zero_add]
    have hterm (q : Fin d × Fin d) :
        (w (some q) : ℂ) / N * (∑ s : S, v (some q) s i * conj (v (some q) s j)) =
          if q = (i,j) then H i j else 0 := by
      by_cases hq : q.1 < q.2
      · rw [hvmoment q hq, if_neg (ne_of_lt hij)]
        have hrev : ¬ (i = q.2 ∧ j = q.1) := by
          rintro ⟨rfl, rfl⟩; exact (lt_asymm hq hij)
        rw [if_neg hrev]
        by_cases heq : q = (i,j)
        · subst q
          simp only [and_self, w, mass, if_pos hij, ite_true]
          rw [← mul_assoc, div_mul_cancel₀ _ hNc, hpval]
        · have hneq : ¬ (i = q.1 ∧ j = q.2) := by
            rintro ⟨rfl, rfl⟩; exact heq (Prod.eta q).symm
          simp [hneq, heq]
      · have hneq : q ≠ (i,j) := by rintro rfl; exact hq hij
        simp [w, mass, hq, hneq]
    simp_rw [hterm]
    simp
  have hentry (i j : Fin d) : H i j = ∑ a : A, (p a : ℂ) * z a i * conj (z a j) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hupper i j hij).symm
    · subst j
      rw [hdiag]
      simp only [mul_assoc, Complex.mul_conj', hz, one_pow, Complex.ofReal_one, mul_one]
      exact_mod_cast hpsum.symm
    · have hh := congrArg (conj : ℂ → ℂ) (hupper j i hij)
      rw [map_sum] at hh
      simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply] at hh
      have hherm : conj (H j i) = H i j := hH.apply i j
      rw [hherm] at hh
      convert hh.symm using 1
      apply Finset.sum_congr rfl
      intro a _; ring
  let E := Fintype.equivFin A
  refine ⟨Fintype.card A, Fintype.card_pos, p ∘ E.symm, z ∘ E.symm,
    fun a => hpnonneg _, ?_, fun a i => hz _ _, ?_⟩
  · simpa only [Function.comp_def] using (E.symm.sum_comp p).trans hpsum
  · intro i j
    rw [hentry]
    exact (E.symm.sum_comp (fun a => (p a : ℂ) * z a i * conj (z a j))).symm

end D5.S3.Quantum.Matrix.FinitePhaseMixture
