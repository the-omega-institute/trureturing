/- GID: D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/OverlapIntervalPropagationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.claim; result=D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result; claim=D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.claim
   digest: Five pure-state overlaps force a sixth beyond three-state interval propagation. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Notation
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The one-unknown-edge procedure can miss the exact feasible lower endpoint. -/

set_option autoImplicit false

namespace D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation

open scoped InnerProductSpace Matrix

noncomputable section

/-- The three-pure-state upper bound of Galvão and Brod. -/
def upper (x y : ℝ) : ℝ :=
  (Real.sqrt (x * y) + Real.sqrt ((1 - x) * (1 - y))) ^ 2

/-- The lower bound is zero when the two known overlaps sum to at most one. -/
def lower (x y : ℝ) : ℝ :=
  if 1 < x + y then (Real.sqrt (x * y) - Real.sqrt ((1 - x) * (1 - y))) ^ 2 else 0

/-- Squared overlap of two pure-state vectors. -/
def overlap {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) : ℝ := ‖inner ℂ u v‖ ^ 2

/-- Unit vectors realizing every given edge except the unordered unknown pair. -/
def realizes {n m : ℕ} (i₀ j₀ : Fin m) (r : Fin m → Fin m → ℝ)
    (ψ : Fin m → EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ k, ‖ψ k‖ = 1) ∧ ∀ i j, i ≠ j →
    ({i, j} : Finset (Fin m)) ≠ {i₀, j₀} → overlap (ψ i) (ψ j) = r i j

/-- Feasible values of the unknown overlap, allowing every finite dimension. -/
def feasible (m : ℕ) (i₀ j₀ : Fin m) (r : Fin m → Fin m → ℝ) : Set ℝ :=
  {t | ∃ (n : ℕ) (ψ : Fin m → EuclideanSpace ℂ (Fin n)),
    realizes i₀ j₀ r ψ ∧ t = overlap (ψ i₀) (ψ j₀)}

/-- Maximum of all common-neighbour lower bounds; the finite set is nonempty for `3 ≤ m`. -/
def procLower (m : ℕ) (i₀ j₀ : Fin m) (r : Fin m → Fin m → ℝ) : ℝ :=
  sSup {t | ∃ k : Fin m, k ≠ i₀ ∧ k ≠ j₀ ∧ t = lower (r k i₀) (r k j₀)}

/-- Minimum of all common-neighbour upper bounds. -/
def procUpper (m : ℕ) (i₀ j₀ : Fin m) (r : Fin m → Fin m → ℝ) : ℝ :=
  sInf {t | ∃ k : Fin m, k ≠ i₀ ∧ k ≠ j₀ ∧ t = upper (r k i₀) (r k j₀)}

/-- Tightness of interval propagation for every realizable one-unknown-edge instance. -/
def claim : Prop :=
  ∀ (m : ℕ) (i₀ j₀ : Fin m) (r : Fin m → Fin m → ℝ), 3 ≤ m → i₀ ≠ j₀ →
    (feasible m i₀ j₀ r).Nonempty →
    procLower m i₀ j₀ r = sInf (feasible m i₀ j₀ r) ∧
      procUpper m i₀ j₀ r = sSup (feasible m i₀ j₀ r)

private def givenOverlaps : Fin 4 → Fin 4 → ℝ :=
  ![![1, 0, 1 / 2, 1 / 2], ![0, 1, 1 / 2, 0],
    ![1 / 2, 1 / 2, 1, 0], ![1 / 2, 0, 0, 1]]

private def witness : Fin 4 → EuclideanSpace ℂ (Fin 3) :=
  ![WithLp.toLp 2 ![1, 0, 0], WithLp.toLp 2 ![0, 1, 0],
    WithLp.toLp 2 ![(Real.sqrt (1 / 2) : ℂ), (Real.sqrt (1 / 2) : ℂ), 0],
    WithLp.toLp 2 ![(Real.sqrt (1 / 2) : ℂ), 0, (Real.sqrt (1 / 2) : ℂ)]]

private lemma lower_half_half : lower (1 / 2) (1 / 2) = 0 := by
  change (if (1 : ℝ) < 1 / 2 + 1 / 2 then _ else 0) = 0
  norm_num

private lemma lower_half_zero : lower (1 / 2) 0 = 0 := by
  change (if (1 : ℝ) < 1 / 2 + 0 then _ else 0) = 0
  norm_num

private lemma instance_lower : procLower 4 2 3 givenOverlaps = 0 := by
  change sSup {t | ∃ k : Fin 4, k ≠ 2 ∧ k ≠ 3 ∧
    t = lower (givenOverlaps k 2) (givenOverlaps k 3)} = 0
  have hs : {t | ∃ k : Fin 4, k ≠ 2 ∧ k ≠ 3 ∧
      t = lower (givenOverlaps k 2) (givenOverlaps k 3)} = ({0} : Set ℝ) := by
    ext t
    constructor
    · rintro ⟨k, h₂, h₃, rfl⟩
      fin_cases k
      · exact lower_half_half
      · exact lower_half_zero
      · exact (h₂ rfl).elim
      · exact (h₃ rfl).elim
    · intro ht
      have ht0 : t = 0 := ht
      refine ⟨0, by decide, by decide, ?_⟩
      exact ht0.trans lower_half_half.symm
  rw [hs, csSup_singleton]

private lemma witness_realizes : realizes 2 3 givenOverlaps witness := by
  have hs : Real.sqrt (1 / 2) ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : ‖(Real.sqrt (1 / 2) : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact hs
  constructor
  · intro k
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    fin_cases k
    · change ‖(1 : ℂ)‖ ^ 2 + (‖(0 : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) = 1 ^ 2
      norm_num
    · change ‖(0 : ℂ)‖ ^ 2 + (‖(1 : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) = 1 ^ 2
      norm_num
    · change ‖(Real.sqrt (1 / 2) : ℂ)‖ ^ 2 +
        (‖(Real.sqrt (1 / 2) : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) = 1 ^ 2
      norm_num only [hn, norm_zero]
    · change ‖(Real.sqrt (1 / 2) : ℂ)‖ ^ 2 +
        (‖(0 : ℂ)‖ ^ 2 + ‖(Real.sqrt (1 / 2) : ℂ)‖ ^ 2) = 1 ^ 2
      norm_num only [hn, norm_zero]
  · intro i j hij hp
    have hinner (i j : Fin 4) : inner ℂ (witness i) (witness j) =
        star (witness i 0) * witness j 0 +
          (star (witness i 1) * witness j 1 + star (witness i 2) * witness j 2) := by
      rw [PiLp.inner_apply]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, RCLike.inner_apply']
    change ‖inner ℂ (witness i) (witness j)‖ ^ 2 = givenOverlaps i j
    rw [hinner]
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact (hp (by decide)).elim
      | change ‖star (1 : ℂ) * 0 + (star (0 : ℂ) * 1 + star (0 : ℂ) * 0)‖ ^ 2 = 0
        norm_num
      | change ‖star (0 : ℂ) * 1 + (star (1 : ℂ) * 0 + star (0 : ℂ) * 0)‖ ^ 2 = 0
        norm_num
      | change ‖star (1 : ℂ) * (Real.sqrt (1 / 2) : ℂ) +
          (star (0 : ℂ) * (Real.sqrt (1 / 2) : ℂ) + star (0 : ℂ) * 0)‖ ^ 2 = 1 / 2
        simpa only [star_one, star_zero, one_mul, zero_mul, add_zero, zero_add] using hn
      | change ‖star (1 : ℂ) * (Real.sqrt (1 / 2) : ℂ) +
          (star (0 : ℂ) * 0 + star (0 : ℂ) * (Real.sqrt (1 / 2) : ℂ))‖ ^ 2 = 1 / 2
        simpa only [star_one, star_zero, one_mul, zero_mul, add_zero, zero_add] using hn
      | change ‖star (0 : ℂ) * (Real.sqrt (1 / 2) : ℂ) +
          (star (1 : ℂ) * (Real.sqrt (1 / 2) : ℂ) + star (0 : ℂ) * 0)‖ ^ 2 = 1 / 2
        simpa only [star_one, star_zero, one_mul, zero_mul, add_zero, zero_add] using hn
      | change ‖star (0 : ℂ) * (Real.sqrt (1 / 2) : ℂ) +
          (star (1 : ℂ) * 0 + star (0 : ℂ) * (Real.sqrt (1 / 2) : ℂ))‖ ^ 2 = 0
        simp only [star_zero, star_one, zero_mul, one_mul, add_zero, norm_zero, zero_pow,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      | change ‖star (Real.sqrt (1 / 2) : ℂ) * 1 +
          (star (Real.sqrt (1 / 2) : ℂ) * 0 + star (0 : ℂ) * 0)‖ ^ 2 = 1 / 2
        simpa only [mul_one, mul_zero, star_zero, add_zero, Complex.star_def,
          Complex.conj_ofReal] using hn
      | change ‖star (Real.sqrt (1 / 2) : ℂ) * 0 +
          (star (Real.sqrt (1 / 2) : ℂ) * 1 + star (0 : ℂ) * 0)‖ ^ 2 = 1 / 2
        simpa only [mul_one, mul_zero, star_zero, zero_add, add_zero, Complex.star_def,
          Complex.conj_ofReal] using hn
      | change ‖star (Real.sqrt (1 / 2) : ℂ) * 1 +
          (star (0 : ℂ) * 0 + star (Real.sqrt (1 / 2) : ℂ) * 0)‖ ^ 2 = 1 / 2
        simpa only [mul_one, mul_zero, zero_add, add_zero, Complex.star_def,
          Complex.conj_ofReal] using hn
      | change ‖star (Real.sqrt (1 / 2) : ℂ) * 0 +
          (star (0 : ℂ) * 1 + star (Real.sqrt (1 / 2) : ℂ) * 0)‖ ^ 2 = 0
        norm_num

private lemma span_saturation {n : ℕ} (a b c : EuclideanSpace ℂ (Fin n))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : overlap a b = 0) (hac : overlap a c = 1 / 2)
    (hbc : overlap b c = 1 / 2) :
    c = (inner ℂ a c) • a + (inner ℂ b c) • b := by
  have hab0 : inner ℂ a b = 0 := by
    apply norm_eq_zero.mp
    have h : ‖inner ℂ a b‖ ^ 2 = 0 := hab
    exact sq_eq_zero_iff.mp h
  have horth : inner ℂ ((inner ℂ a c) • a) ((inner ℂ b c) • b) = 0 := by
    rw [inner_smul_left, inner_smul_right, hab0, mul_zero, mul_zero]
  have hp : ‖(inner ℂ a c) • a + (inner ℂ b c) • b‖ ^ 2 = 1 := by
    rw [norm_add_sq (𝕜 := ℂ), horth]
    simp only [map_zero, mul_zero, add_zero, norm_smul, ha, hb, mul_one]
    change ‖inner ℂ a c‖ ^ 2 = 1 / 2 at hac
    change ‖inner ℂ b c‖ ^ 2 = 1 / 2 at hbc
    linarith
  have hip : (inner ℂ c ((inner ℂ a c) • a + (inner ℂ b c) • b)).re = 1 := by
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      ← inner_conj_symm c a, ← inner_conj_symm c b,
      Complex.mul_conj', Complex.mul_conj']
    simp only [Complex.add_re, Complex.ofReal_re]
    change ‖inner ℂ a c‖ ^ 2 = 1 / 2 at hac
    change ‖inner ℂ b c‖ ^ 2 = 1 / 2 at hbc
    linarith
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [norm_sub_sq (𝕜 := ℂ), hc, hip, hp]
  norm_num

private lemma forced_overlap {n : ℕ} (ψ : Fin 4 → EuclideanSpace ℂ (Fin n))
    (hψ : realizes 2 3 givenOverlaps ψ) : overlap (ψ 2) (ψ 3) = 1 / 4 := by
  have hab : overlap (ψ 0) (ψ 1) = 0 := hψ.2 0 1 (by decide) (by decide)
  have hac : overlap (ψ 0) (ψ 2) = 1 / 2 := hψ.2 0 2 (by decide) (by decide)
  have had : overlap (ψ 0) (ψ 3) = 1 / 2 := hψ.2 0 3 (by decide) (by decide)
  have hbc : overlap (ψ 1) (ψ 2) = 1 / 2 := hψ.2 1 2 (by decide) (by decide)
  have hbd : overlap (ψ 1) (ψ 3) = 0 := hψ.2 1 3 (by decide) (by decide)
  have hc := span_saturation (ψ 0) (ψ 1) (ψ 2)
    (hψ.1 0) (hψ.1 1) (hψ.1 2) hab hac hbc
  have hbd0 : inner ℂ (ψ 1) (ψ 3) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hbd)
  change ‖inner ℂ (ψ 2) (ψ 3)‖ ^ 2 = 1 / 4
  rw [hc, inner_add_left, inner_smul_left, inner_smul_left, hbd0,
    mul_zero, add_zero, norm_mul, RCLike.norm_conj, mul_pow]
  change ‖inner ℂ (ψ 0) (ψ 2)‖ ^ 2 = 1 / 2 at hac
  change ‖inner ℂ (ψ 0) (ψ 3)‖ ^ 2 = 1 / 2 at had
  rw [hac, had]
  norm_num

private lemma feasible_nonempty : (feasible 4 2 3 givenOverlaps).Nonempty := by
  exact ⟨overlap (witness 2) (witness 3), 3, witness, witness_realizes, rfl⟩

private lemma feasible_singleton : feasible 4 2 3 givenOverlaps = {1 / 4} := by
  ext t
  constructor
  · rintro ⟨n, ψ, hψ, rfl⟩
    exact forced_overlap ψ hψ
  · intro ht
    have htq : t = 1 / 4 := ht
    exact ⟨3, witness, witness_realizes, htq.trans (forced_overlap witness witness_realizes).symm⟩

private lemma instance_infimum : sInf (feasible 4 2 3 givenOverlaps) = 1 / 4 := by
  rw [feasible_singleton, csInf_singleton]

/-- Three-state interval propagation is not always tight for four pure states. -/
theorem result : ¬ claim := by
  intro h
  have hbound := (h 4 2 3 givenOverlaps (by norm_num) (by decide) feasible_nonempty).1
  rw [instance_lower, instance_infimum] at hbound
  norm_num at hbound

end

end D5.S3.Quantum.PureState.OverlapIntervalPropagationRefutation
