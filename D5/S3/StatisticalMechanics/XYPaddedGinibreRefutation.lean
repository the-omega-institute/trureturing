/- GID: D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/XYPaddedGinibreRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.claim; result=D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.result; claim=D5/S3/StatisticalMechanics/XYPaddedGinibreRefutation.claim
   digest: The XY model violates a padded general Ginibre inequality on a five-cycle. -/

/-
proof_shape: freeMeasure, spin, observable, monomial, parity, pgg, claim: definitions
proof_shape: result: bind-only (Fourier orthogonality and product integration from pinned
  Mathlib, finite expansion, and exact rational normalization)
escape_witness: none
admission_basis: open-problem-resolution (#13353; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open MeasureTheory Finset
open scoped ComplexConjugate
set_option allowUnsafeReducibility true in
attribute [local reducible] Real.Angle
namespace D5.S3.StatisticalMechanics.XYPaddedGinibreRefutation

/-- The free O(2) probability measure on p sites (arXiv:2207.07603v2, p. 2).
The rotation-invariant probability measure on S¹ is the image of normalized Haar measure
on angles under θ ↦ (cos θ, sin θ); configurations use that angle parametrization. -/
noncomputable def freeMeasure (p : ℕ) : Measure (Fin p → Real.Angle) :=
  Measure.pi (fun _ => (@AddCircle.haarAddCircle (2 * Real.pi) ⟨Real.two_pi_pos⟩ : Measure Real.Angle))

/-- The unit spin θ ↦ (cos θ, sin θ) in the angle convention of the O(2) model. -/
noncomputable def spin (θ : Real.Angle) : Fin 2 → ℝ := ![Real.Angle.cos θ, Real.Angle.sin θ]

/-- The basic observable σ_i · σ_j for an unordered pair represented by i < j (p. 2). -/
noncomputable def observable {p : ℕ} (x : Fin p → Real.Angle)
    (e : {e : Fin p × Fin p // e.1 < e.2}) : ℝ :=
  dotProduct (spin (x e.1.1)) (spin (x e.1.2))

/-- The monomial O(x)^u = ∏_e O_e(x)^(u_e) (p. 2). -/
noncomputable def monomial {p : ℕ} (u : {e : Fin p × Fin p // e.1 < e.2} → ℕ)
    (x : Fin p → Real.Angle) : ℝ :=
  ∏ e, observable x e ^ u e

/-- The O(N) parity homomorphism: each pair has one parity bit at each endpoint (p. 5). -/
def parity (p : ℕ) : ({e : Fin p × Fin p // e.1 < e.2} → ℤ) →+ (Fin p → ZMod 2) where
  toFun a i := ∑ e : {e : Fin p × Fin p // e.1 < e.2}, ((if e.1.1 = i then (a e : ZMod 2) else 0) +
    (if e.1.2 = i then (a e : ZMod 2) else 0))
  map_zero' := by ext i; simp
  map_add' a b := by
    ext i
    simp only [Pi.add_apply, Int.cast_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> ring

/-- The duplicated padded general Ginibre functional with even padding u (p. 6). -/
noncomputable def pgg {p m : ℕ} (V : Fin m → {e : Fin p × Fin p // e.1 < e.2} → ℕ)
    (ε : Fin m → ℝ)
    (u : {e : Fin p × Fin p // e.1 < e.2} → ℕ) : ℝ :=
  ∫ xy : (Fin p → Real.Angle) × (Fin p → Real.Angle),
    monomial u xy.1 * monomial u xy.2 *
      ∏ i, (monomial (V i) xy.1 + ε i * monomial (V i) xy.2) ∂(freeMeasure p).prod (freeMeasure p)

/-- Problem 2, p. 14: "For the XY model, or $O(2)$ model, the GG inequalities were
proved by Ginibre~\cite{Ginibre2}. What about the padded generalizations given by the PGG
inequalities?" This is the assertion that every p ≥ 1 O(2) model satisfies every PGG
inequality, with all natural rows, signs in {−1,1}, and even natural padding. -/
def claim : Prop :=
  ∀ p : ℕ, 0 < p → ∀ (m : ℕ) (V : Fin m → {e : Fin p × Fin p // e.1 < e.2} → ℕ)
    (ε : Fin m → ℝ) (u : {e : Fin p × Fin p // e.1 < e.2} → ℕ),
    (∀ i, ε i = -1 ∨ ε i = 1) → parity p (fun e => (u e : ℤ)) = 0 → 0 ≤ pgg V ε u

/-- Problem 2 has a negative answer: five cycle edges, two identical rows and negative
signs give PGG value −45/131072. Fourier orthogonality gives cycle moments
M₁ = 1/16, M₂ = 17/512 and M₃ = 61/4096. -/
theorem result : ¬ claim := by
  classical
  let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let ν : Measure Real.Angle := AddCircle.haarAddCircle
  have hchar (n : ℤ) : (∫ θ : Real.Angle, fourier n θ ∂ν) = if n = 0 then 1 else 0 := by
    by_cases hn : n = 0
    · simp [hn, ν]
    · rw [if_neg hn]
      exact integral_eq_zero_of_add_right_eq_neg
        (fourier_add_half_inv_index hn (by positivity : 0 < 2 * Real.pi))
  have hangle (θ : Real.Angle) : AddCircle.toCircle θ = Real.Angle.toCircle θ := by
    induction θ using QuotientAddGroup.induction_on
    rename_i x
    change AddCircle.toCircle (x : AddCircle (2 * Real.pi)) = Circle.exp x
    rw [AddCircle.toCircle_apply_mk]
    congr 1
    rw [div_self (by positivity : (2 * Real.pi) ≠ 0), one_mul]
  have hre (θ : Real.Angle) : (fourier 1 θ).re = Real.Angle.cos θ := by
    rw [fourier_one, hangle, Real.Angle.coe_toCircle]
    simp
  have hdot (θ φ : Real.Angle) : dotProduct (spin θ) (spin φ) = Real.Angle.cos (θ - φ) := by
    induction θ using QuotientAddGroup.induction_on
    induction φ using QuotientAddGroup.induction_on
    rename_i a b
    simp only [dotProduct, spin, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    change Real.cos a * Real.cos b + Real.sin a * Real.sin b = Real.cos (a - b)
    exact (Real.cos_sub a b).symm
  have hdotf (θ φ : Real.Angle) : ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) =
      (fourier 1 (θ - φ) + fourier (-1) (θ - φ)) / 2 := by
    rw [hdot, fourier_neg, Complex.add_conj, hre]
    push_cast
    ring
  have hshift (n : ℤ) (θ φ : Real.Angle) : fourier n (θ - φ) =
      fourier n θ * fourier (-n) φ := by
    simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, neg_smul,
      AddCircle.toCircle_add, Circle.coe_mul]
  have : IsProbabilityMeasure (freeMeasure 5) := by dsimp [freeMeasure]; infer_instance
  let next : Fin 5 → Fin 5 := ![1, 2, 3, 4, 0]
  let prev : Fin 5 → Fin 5 := ![4, 0, 1, 2, 3]
  have hcycle (n : ℕ) (c : Fin n → ℂ) (t : Fin n → ℤ)
      (ht : Function.Injective t) :
      (∫ x : Fin 5 → Real.Angle, ∏ i, ∑ r : Fin n,
        c r * fourier (t r) (x i - x (next i)) ∂freeMeasure 5) = ∑ r : Fin n, c r ^ 5 := by
    have hterm (a : Fin 5 → Fin n) (x : Fin 5 → Real.Angle) :
        (∏ i, c (a i) * fourier (t (a i)) (x i - x (next i))) =
        (∏ i, c (a i)) * ∏ i, fourier (t (a i) - t (a (prev i))) (x i) := by
      simp only [Fin.prod_univ_five]
      change (c (a 0) * fourier (t (a 0)) (x 0 - x 1)) * (c (a 1) * fourier (t (a 1)) (x 1 - x 2)) * (c (a 2) * fourier (t (a 2)) (x 2 - x 3)) * (c (a 3) * fourier (t (a 3)) (x 3 - x 4)) * (c (a 4) * fourier (t (a 4)) (x 4 - x 0)) =
        (c (a 0) * c (a 1) * c (a 2) * c (a 3) * c (a 4)) * (fourier (t (a 0) - t (a 4)) (x 0) * fourier (t (a 1) - t (a 0)) (x 1) * fourier (t (a 2) - t (a 1)) (x 2) * fourier (t (a 3) - t (a 2)) (x 3) * fourier (t (a 4) - t (a 3)) (x 4))
      simp_rw [hshift, sub_eq_add_neg, fourier_add]
      ring
    have htermint (a : Fin 5 → Fin n) :
        Integrable (fun x : Fin 5 → Real.Angle => ∏ i,
          c (a i) * fourier (t (a i)) (x i - x (next i))) (freeMeasure 5) := by
      have hc : Continuous (fun x : Fin 5 → Real.Angle => ∏ i,
          c (a i) * fourier (t (a i)) (x i - x (next i))) := by fun_prop
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have heval (a : Fin 5 → Fin n) :
        (∫ x : Fin 5 → Real.Angle, ∏ i,
          c (a i) * fourier (t (a i)) (x i - x (next i)) ∂freeMeasure 5) =
        if a = (fun _ => a 0) then c (a 0) ^ 5 else 0 := by
      simp_rw [hterm]
      rw [integral_const_mul]
      change (∏ i, c (a i)) *
        (∫ x : Fin 5 → Real.Angle, ∏ i, fourier (t (a i) - t (a (prev i))) (x i)
          ∂Measure.pi (fun _ => ν)) = _
      rw [integral_fintype_prod_eq_prod]
      simp_rw [hchar]
      by_cases ha : a = (fun _ => a 0)
      · rw [if_pos ha]
        conv_lhs => rw [ha]
        simp
      · rw [if_neg ha]
        have hne : ∃ i : Fin 5, a i ≠ a (prev i) := by
          by_contra h
          push Not at h
          have h1 : a 1 = a 0 := h 1
          have h2 : a 2 = a 1 := h 2
          have h3 : a 3 = a 2 := h 3
          have h4 : a 4 = a 3 := h 4
          apply ha
          funext i
          fin_cases i
          · rfl
          · exact h1
          · exact h2.trans h1
          · exact h3.trans (h2.trans h1)
          · exact h4.trans (h3.trans (h2.trans h1))
        obtain ⟨i, hi⟩ := hne
        have hz : t (a i) - t (a (prev i)) ≠ 0 :=
          sub_ne_zero.mpr (fun h => hi (ht h))
        have hp : (∏ j : Fin 5, if t (a j) - t (a (prev j)) = 0
            then (1 : ℂ) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hz)
        rw [hp, mul_zero]
    calc
      _ = ∫ x : Fin 5 → Real.Angle, ∑ a : Fin 5 → Fin n,
          ∏ i, c (a i) * fourier (t (a i)) (x i - x (next i)) ∂freeMeasure 5 := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact Fintype.prod_sum _
      _ = ∑ a : Fin 5 → Fin n, ∫ x : Fin 5 → Real.Angle,
          ∏ i, c (a i) * fourier (t (a i)) (x i - x (next i)) ∂freeMeasure 5 := by
        exact integral_finsetSum _ (fun a _ => htermint a)
      _ = ∑ a : Fin 5 → Fin n, if a = (fun _ => a 0) then c (a 0) ^ 5 else 0 := by
        simp_rw [heval]
      _ = ∑ a : Fin 5 → Fin n, ∑ r : Fin n,
          if a = (fun _ => r) then c r ^ 5 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        symm
        apply Finset.sum_eq_single (a 0)
        · intro r hr hne
          have hn : a ≠ (fun _ => r) := by
            intro h
            exact hne ((congrFun h 0).symm)
          simp [hn]
        · simp
      _ = ∑ r : Fin n, c r ^ 5 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        simp
  let Z (x : Fin 5 → Real.Angle) : ℝ := ∏ i, dotProduct (spin (x i)) (spin (x (next i)))
  have hfpow (n : ℤ) (k : ℕ) (θ : Real.Angle) :
      fourier n θ ^ k = fourier ((k : ℤ) * n) θ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, ← fourier_add]
      congr 2
      push_cast
      ring
  have hpow1 (θ φ : Real.Angle) : ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) ^ 1 =
      ∑ r : Fin 2, (1 / 2 : ℂ) * fourier (![1, -1] r) (θ - φ) := by
    simp only [pow_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hdotf]
    ring
  have hpow2 (θ φ : Real.Angle) : ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) ^ 2 =
      ∑ r : Fin 3, (![1 / 4, 1 / 2, 1 / 4] r : ℂ) *
        fourier (![2, 0, -2] r) (θ - φ) := by
    have h2 : fourier 2 (θ - φ) = fourier 1 (θ - φ) ^ 2 := by
      simpa using (hfpow 1 2 (θ - φ)).symm
    have hn2 : fourier (-2) (θ - φ) = fourier (-1) (θ - φ) ^ 2 := by
      simpa using (hfpow (-1) 2 (θ - φ)).symm
    have hm : fourier 1 (θ - φ) * fourier (-1) (θ - φ) = 1 := by
      rw [← fourier_add]
      norm_num
    rw [Fin.sum_univ_three]
    change ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) ^ 2 = (1 / 4 : ℂ) * fourier 2 (θ - φ) +
      (1 / 2 : ℂ) * fourier 0 (θ - φ) + (1 / 4 : ℂ) * fourier (-2) (θ - φ)
    rw [hdotf, h2, hn2, fourier_zero]
    linear_combination (1 / 2 : ℂ) * hm
  have hpow3 (θ φ : Real.Angle) : ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) ^ 3 =
      ∑ r : Fin 4, (![1 / 8, 3 / 8, 3 / 8, 1 / 8] r : ℂ) *
        fourier (![3, 1, -1, -3] r) (θ - φ) := by
    have h3 : fourier 3 (θ - φ) = fourier 1 (θ - φ) ^ 3 := by
      simpa using (hfpow 1 3 (θ - φ)).symm
    have hn3 : fourier (-3) (θ - φ) = fourier (-1) (θ - φ) ^ 3 := by
      simpa using (hfpow (-1) 3 (θ - φ)).symm
    have hm : fourier 1 (θ - φ) * fourier (-1) (θ - φ) = 1 := by
      rw [← fourier_add]
      norm_num
    rw [Fin.sum_univ_four]
    change ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) ^ 3 = (1 / 8 : ℂ) * fourier 3 (θ - φ) +
      (3 / 8 : ℂ) * fourier 1 (θ - φ) + (3 / 8 : ℂ) * fourier (-1) (θ - φ) +
      (1 / 8 : ℂ) * fourier (-3) (θ - φ)
    rw [hdotf, h3, hn3]
    linear_combination (3 / 8 : ℂ) *
      (fourier 1 (θ - φ) + fourier (-1) (θ - φ)) * hm
  have hmoment (k n : ℕ) (c : Fin n → ℂ) (t : Fin n → ℤ)
      (ht : Function.Injective t)
      (hp : ∀ θ φ : Real.Angle, ((dotProduct (spin θ) (spin φ) : ℝ) : ℂ) ^ k =
        ∑ r : Fin n, c r * fourier (t r) (θ - φ)) :
      ((∫ x : Fin 5 → Real.Angle, Z x ^ k ∂freeMeasure 5 : ℝ) : ℂ) = ∑ r : Fin n, c r ^ 5 := by
    rw [← integral_complex_ofReal]
    calc
      _ = ∫ x : Fin 5 → Real.Angle, ∏ i, ((dotProduct (spin (x i)) (spin (x (next i))) : ℝ) : ℂ) ^ k ∂freeMeasure 5 := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Z, ← Finset.prod_pow, Complex.ofReal_prod, Complex.ofReal_pow]
      _ = ∫ x : Fin 5 → Real.Angle, ∏ i, ∑ r : Fin n,
          c r * fourier (t r) (x i - x (next i)) ∂freeMeasure 5 := by simp_rw [hp]
      _ = _ := hcycle n c t ht
  have hM1 : (∫ x : Fin 5 → Real.Angle, Z x ^ 1 ∂freeMeasure 5) = 1 / 16 := by
    apply Complex.ofReal_inj.mp
    calc
      _ = ∑ r : Fin 2, (1 / 2 : ℂ) ^ 5 :=
        hmoment 1 2 (fun _ => 1 / 2) ![1, -1]
          (by decide) hpow1
      _ = _ := by norm_num [Fin.sum_univ_two]
  have hM2 : (∫ x : Fin 5 → Real.Angle, Z x ^ 2 ∂freeMeasure 5) = 17 / 512 := by
    apply Complex.ofReal_inj.mp
    calc
      _ = ∑ r : Fin 3, (![1 / 4, 1 / 2, 1 / 4] r : ℂ) ^ 5 :=
        hmoment 2 3 ![1 / 4, 1 / 2, 1 / 4] ![2, 0, -2]
          (by decide) hpow2
      _ = _ := by
        rw [Fin.sum_univ_three]
        change (1 / 4 : ℂ) ^ 5 + (1 / 2 : ℂ) ^ 5 + (1 / 4 : ℂ) ^ 5 = ((17 / 512 : ℝ) : ℂ)
        norm_num
  have hM3 : (∫ x : Fin 5 → Real.Angle, Z x ^ 3 ∂freeMeasure 5) = 61 / 4096 := by
    apply Complex.ofReal_inj.mp
    calc
      _ = ∑ r : Fin 4, (![1 / 8, 3 / 8, 3 / 8, 1 / 8] r : ℂ) ^ 5 :=
        hmoment 3 4 ![1 / 8, 3 / 8, 3 / 8, 1 / 8] ![3, 1, -1, -3]
          (by decide) hpow3
      _ = _ := by
        rw [Fin.sum_univ_four]
        change (1 / 8 : ℂ) ^ 5 + (3 / 8 : ℂ) ^ 5 + (3 / 8 : ℂ) ^ 5 + (1 / 8 : ℂ) ^ 5 =
          ((61 / 4096 : ℝ) : ℂ)
        norm_num
  let e01 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(0, 1), by decide⟩
  let e02 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(0, 2), by decide⟩
  let e03 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(0, 3), by decide⟩
  let e04 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(0, 4), by decide⟩
  let e12 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(1, 2), by decide⟩
  let e13 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(1, 3), by decide⟩
  let e14 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(1, 4), by decide⟩
  let e23 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(2, 3), by decide⟩
  let e24 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(2, 4), by decide⟩
  let e34 : {e : Fin 5 × Fin 5 // e.1 < e.2} := ⟨(3, 4), by decide⟩
  have huniv : (univ : Finset ({e : Fin 5 × Fin 5 // e.1 < e.2})) =
      {e01, e02, e03, e04, e12, e13, e14, e23, e24, e34} := by decide
  let C : Finset ({e : Fin 5 × Fin 5 // e.1 < e.2}) := {e01, e12, e23, e34, e04}
  let u (e : {e : Fin 5 × Fin 5 // e.1 < e.2}) : ℕ := if e ∈ C then 1 else 0
  have heven : parity 5 (fun e => (u e : ℤ)) = 0 := by
    decide
  have hmono (x : Fin 5 → Real.Angle) : monomial u x = Z x := by
    unfold monomial
    rw [huniv]
    simp [u, C, e01, e02, e03, e04, e12, e13, e14, e23, e24, e34, observable]
    dsimp only [Z]
    rw [Fin.prod_univ_five]
    simp [next, dotProduct, Fin.sum_univ_two]; ring
  have hZc : Continuous Z := by
    dsimp only [Z]
    apply continuous_finsetProd
    intro i hi
    simp_rw [hdot, ← hre]
    fun_prop
  have hZi (k : ℕ) : Integrable (fun x : Fin 5 → Real.Angle => Z x ^ k) (freeMeasure 5) :=
    (hZc.pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdup : (∫ xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle),
      Z xy.1 * Z xy.2 * (Z xy.1 - Z xy.2) ^ 2 ∂(freeMeasure 5).prod (freeMeasure 5)) =
      2 * ((∫ x : Fin 5 → Real.Angle, Z x ^ 1 ∂freeMeasure 5) * (∫ x : Fin 5 → Real.Angle, Z x ^ 3 ∂freeMeasure 5) -
        (∫ x : Fin 5 → Real.Angle, Z x ^ 2 ∂freeMeasure 5) ^ 2) := by
    have h31 : Integrable (fun xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle) => Z xy.1 ^ 3 * Z xy.2 ^ 1)
        ((freeMeasure 5).prod (freeMeasure 5)) := (hZi 3).mul_prod (hZi 1)
    have h13 : Integrable (fun xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle) => Z xy.1 ^ 1 * Z xy.2 ^ 3)
        ((freeMeasure 5).prod (freeMeasure 5)) := (hZi 1).mul_prod (hZi 3)
    have h22 : Integrable (fun xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle) => Z xy.1 ^ 2 * Z xy.2 ^ 2)
        ((freeMeasure 5).prod (freeMeasure 5)) := (hZi 2).mul_prod (hZi 2)
    calc
      _ = ∫ xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle),
          (Z xy.1 ^ 3 * Z xy.2 ^ 1 + Z xy.1 ^ 1 * Z xy.2 ^ 3) -
            2 * (Z xy.1 ^ 2 * Z xy.2 ^ 2) ∂(freeMeasure 5).prod (freeMeasure 5) := by
        apply integral_congr_ae
        filter_upwards [] with xy
        ring
      _ = (∫ xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle), Z xy.1 ^ 3 * Z xy.2 ^ 1 ∂(freeMeasure 5).prod (freeMeasure 5)) +
          (∫ xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle), Z xy.1 ^ 1 * Z xy.2 ^ 3 ∂(freeMeasure 5).prod (freeMeasure 5)) -
          2 * (∫ xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle), Z xy.1 ^ 2 * Z xy.2 ^ 2 ∂(freeMeasure 5).prod (freeMeasure 5)) := by
        rw [integral_sub
          (f := fun xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle) => Z xy.1 ^ 3 * Z xy.2 ^ 1 +
            Z xy.1 ^ 1 * Z xy.2 ^ 3)
          (g := fun xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle) => 2 * (Z xy.1 ^ 2 * Z xy.2 ^ 2))
          (h31.add h13) (h22.const_mul 2)]
        rw [integral_add h31 h13, integral_const_mul]
      _ = _ := by
        rw [integral_prod_mul (fun x : Fin 5 → Real.Angle => Z x ^ 3) (fun x : Fin 5 → Real.Angle => Z x ^ 1),
          integral_prod_mul (fun x : Fin 5 → Real.Angle => Z x ^ 1) (fun x : Fin 5 → Real.Angle => Z x ^ 3),
          integral_prod_mul (fun x : Fin 5 → Real.Angle => Z x ^ 2) (fun x : Fin 5 → Real.Angle => Z x ^ 2)]
        ring
  have hraw : pgg (fun _ : Fin 2 => u) (fun _ => -1) u =
      ∫ xy : (Fin 5 → Real.Angle) × (Fin 5 → Real.Angle),
        Z xy.1 * Z xy.2 * (Z xy.1 - Z xy.2) ^ 2 ∂(freeMeasure 5).prod (freeMeasure 5) := by
    unfold pgg
    apply integral_congr_ae
    filter_upwards [] with xy
    simp only [hmono, Fin.prod_univ_two]
    ring
  have hnegative : pgg (fun _ : Fin 2 => u) (fun _ => -1) u = -45 / 131072 := by
    rw [hraw, hdup, hM1, hM2, hM3]
    norm_num
  intro h
  have hnonneg := h 5 (by norm_num) 2 (fun _ => u) (fun _ => -1) u
    (by intro i; exact Or.inl rfl) heven
  rw [hnegative] at hnonneg
  norm_num at hnonneg
end D5.S3.StatisticalMechanics.XYPaddedGinibreRefutation
