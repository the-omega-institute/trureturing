/- GID: D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex
   generality: I
   mirror-B: D5/B/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.claim; result=D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.result; claim=D5/S3/Analytic/NumericalRange/SpatialNumericalRangeNonconvex.claim
   digest: A complex nonunital normed algebra has a nonconvex spatial numerical range. -/

/- Source: Dedania–Patel, arXiv:2306.16172, §1.
   admission_basis: open-problem-resolution (#15580; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Reuse: Prod.norm_def, pi_norm_le_iff_of_nonneg, norm_le_pi_norm,
     ContinuousLinearMap.proj, ContinuousLinearMap.snd,
     ContinuousLinearMap.opNorm_le_bound, ContinuousLinearMap.le_opNorm,
     Complex.norm_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
     Complex.sq_norm, Complex.re_le_norm, Complex.im_le_norm.
   Definitions:
     Alg: proof_shape definition; consumers=algNormedAddCommGroup, algMul,
       algNonUnitalRing, algNormedSpace, algNonUnitalNormedRing,
       algIsScalarTower, algSMulCommClass, phi0, phi1, e, x₁, x₂, result
     P: proof_shape definition; consumers=mulDef, P_add, P_smul, P_sq,
       alg_norm_mul_le, e_mul, z_points, midpoint_not_mem
     mulDef: proof_shape definition; consumer=algMul
     algNormedAddCommGroup: proof_shape definition; consumers=algNonUnitalRing,
       algNormedSpace, algNonUnitalNormedRing
     algMul: proof_shape definition; consumer=algNonUnitalRing
     algNonUnitalRing: proof_shape definition; consumer=algNonUnitalNormedRing
     algNormedSpace: proof_shape definition; consumers=phi0, phi1, result
     algNonUnitalNormedRing: proof_shape definition; consumers=z_points,
       midpoint_not_mem, nonconvex, result
     algIsScalarTower: proof_shape definition; consumers=z_points,
       midpoint_not_mem, nonconvex, result
     algSMulCommClass: proof_shape definition; consumers=z_points,
       midpoint_not_mem, nonconvex, result
     spatialNumericalRange: proof_shape definition; consumers=claim,
       z_points, midpoint_not_mem, nonconvex
     claim: proof_shape definition; consumer=result
     phi0: proof_shape definition; consumers=phi0_norm, z_points
     phi1: proof_shape definition; consumers=phi1_norm, z_points
     e: proof_shape definition; consumers=e_mul, z_points, midpoint_not_mem,
       nonconvex, result
     x₁: proof_shape definition; consumers=x₁_norm, phi0_norm, z_points
     x₂: proof_shape definition; consumers=x₂_norm, phi1_norm, z_points
     z₁: proof_shape definition; consumers=z_points, nonconvex
     z₂: proof_shape definition; consumers=z_points, nonconvex
     m: proof_shape definition; consumers=midpoint_not_mem, nonconvex
     phase: proof_shape definition; consumers=phase_norm, phase_mul,
       coeff_sum_le_one
   Per-declaration proof_shape and live consumers:
     P_add: bind-only; consumers=alg_mul_assoc, alg_left_distrib
     P_smul: bind-only; consumers=alg_mul_assoc, alg_mul_smul
     P_sq: bind-only; consumer=alg_mul_assoc
     alg_mul_assoc: bind-only; consumer=algNonUnitalRing
     alg_left_distrib: bind-only; consumer=algNonUnitalRing
     alg_right_distrib: bind-only; consumer=algNonUnitalRing
     alg_mul_zero: bind-only; consumer=algNonUnitalRing
     alg_zero_mul: bind-only; consumer=algNonUnitalRing
     alg_smul_mul: bind-only; consumer=algIsScalarTower
     alg_mul_smul: bind-only; consumer=algSMulCommClass
     alg_norm_mul_le: bind-only; consumer=algNonUnitalNormedRing
     x₁_norm: bind-only; consumers=phi0_norm, z_points
     x₂_norm: bind-only; consumers=phi1_norm, z_points
     phi0_norm: bind-only; consumer=z_points
     phi1_norm: bind-only; consumer=z_points
     e_mul: bind-only; consumers=z_points, midpoint_not_mem
     z_points: bind-only; consumer=nonconvex
     phase_norm: bind-only; consumer=coeff_sum_le_one
     phase_mul: bind-only; consumer=coeff_sum_le_one
     coeff_sum_le_one: content; consumer=midpoint_not_mem
     phi_eval: bind-only; consumers=coeff_sum_le_one, midpoint_not_mem
     norm_mul_bound: bind-only; consumer=midpoint_not_mem
     extremal_re: bind-only; consumer=support_im_zero
     extremal_im: bind-only; consumer=midpoint_not_mem
     support_im_zero: bind-only; consumer=midpoint_not_mem
     midpoint_not_mem: content; consumer=nonconvex
     nonconvex: content; consumer=result
     result: content; designated refutation conclusion
   Testing a functional on its coefficient phases bounds the sum of coefficient
   norms. A norming vector makes the diagonal products real. At the maximal
   imaginary height the cross products are purely imaginary; their common
   product identity excludes the midpoint of the two exhibited points. -/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace D5.S3.Analytic.NumericalRange.SpatialNumericalRangeNonconvex

private abbrev Alg := ℂ × (Fin 2 → ℂ)

private def P (y : Fin 2 → ℂ) : Fin 2 → ℂ := ![(y 0 + 2 * y 1) / 5, (2 * y 0 + 4 * y 1) / 5]

private def mulDef (u v : Alg) : Alg :=
  (u.1 * v.1 / 3, (u.1 / 3) • P v.2 + (v.1 / 3) • u.2)

private local instance algNormedAddCommGroup : NormedAddCommGroup Alg :=
  inferInstanceAs (NormedAddCommGroup (ℂ × (Fin 2 → ℂ)))
private local instance algMul : Mul Alg := ⟨mulDef⟩

private lemma P_add (x y : Fin 2 → ℂ) : P (x + y) = P x + P y := by
  funext i
  fin_cases i <;> simp [P] <;> ring

private lemma P_smul (c : ℂ) (x : Fin 2 → ℂ) : P (c • x) = c • P x := by
  funext i
  fin_cases i <;> simp [P] <;> ring

private lemma P_sq (x : Fin 2 → ℂ) : P (P x) = P x := by
  funext i
  fin_cases i <;> simp [P] <;> ring

private lemma alg_mul_assoc (u v w : Alg) : u * v * w = u * (v * w) := by
  rcases u with ⟨u₀,u⟩; rcases v with ⟨v₀,v⟩; rcases w with ⟨w₀,w⟩
  apply Prod.ext
  · change (u₀ * v₀ / 3) * w₀ / 3 = u₀ * (v₀ * w₀ / 3) / 3
    ring
  · change ((u₀ * v₀ / 3) / 3) • P w + (w₀ / 3) • ((u₀ / 3) • P v + (v₀ / 3) • u) =
      (u₀ / 3) • P ((v₀ / 3) • P w + (w₀ / 3) • v) + ((v₀ * w₀ / 3) / 3) • u
    rw [smul_add, P_add, P_smul, P_smul, P_sq]
    ring_nf
    module

private lemma alg_left_distrib (u v w : Alg) : u * (v + w) = u * v + u * w := by
  rcases u with ⟨u₀,u⟩; rcases v with ⟨v₀,v⟩; rcases w with ⟨w₀,w⟩
  apply Prod.ext
  · change u₀ * (v₀ + w₀) / 3 = u₀ * v₀ / 3 + u₀ * w₀ / 3
    ring
  · change (u₀ / 3) • P (v + w) + ((v₀ + w₀) / 3) • u =
      (u₀ / 3) • P v + (v₀ / 3) • u + ((u₀ / 3) • P w + (w₀ / 3) • u)
    rw [P_add, add_div, add_smul]
    ring_nf
    module

private lemma alg_right_distrib (u v w : Alg) : (u + v) * w = u * w + v * w := by
  rcases u with ⟨u₀,u⟩; rcases v with ⟨v₀,v⟩; rcases w with ⟨w₀,w⟩
  apply Prod.ext
  · change (u₀ + v₀) * w₀ / 3 = u₀ * w₀ / 3 + v₀ * w₀ / 3
    ring
  · change ((u₀ + v₀) / 3) • P w + (w₀ / 3) • (u + v) =
      ((u₀ / 3) • P w + (w₀ / 3) • u) + ((v₀ / 3) • P w + (w₀ / 3) • v)
    rw [add_div, add_smul]
    ring_nf
    module

private lemma alg_mul_zero (u : Alg) : u * 0 = 0 := by
  rcases u with ⟨u₀,u⟩
  apply Prod.ext
  · change u₀ * 0 / 3 = 0
    simp
  · change (u₀ / 3) • P 0 + (0 / 3) • u = 0
    simp [P]
private lemma alg_zero_mul (u : Alg) : 0 * u = 0 := by
  rcases u with ⟨u₀,u⟩
  apply Prod.ext
  · change 0 * u₀ / 3 = 0
    simp
  · change (0 / 3) • P u + (u₀ / 3) • 0 = 0
    simp [P]

private local instance algNonUnitalRing : NonUnitalRing Alg where
  __ := (inferInstance : AddCommGroup Alg)
  __ := (inferInstance : Mul Alg)
  left_distrib := alg_left_distrib
  right_distrib := alg_right_distrib
  zero_mul := alg_zero_mul
  mul_zero := alg_mul_zero
  mul_assoc := alg_mul_assoc

private local instance algNormedSpace : NormedSpace ℂ Alg :=
  inferInstanceAs (NormedSpace ℂ (ℂ × (Fin 2 → ℂ)))

private lemma alg_smul_mul (c : ℂ) (u v : Alg) : (c • u) * v = c • (u * v) := by
  rcases u with ⟨u₀,u⟩; rcases v with ⟨v₀,v⟩
  apply Prod.ext
  · change (c * u₀) * v₀ / 3 = c * (u₀ * v₀ / 3)
    ring
  · change ((c * u₀ / 3) • P v) + (v₀ / 3) • (c • u) = c • ((u₀ / 3) • P v + (v₀ / 3) • u)
    rw [smul_add]
    congr 1
    · rw [smul_smul]
      congr 1
      ring
    · rw [smul_smul, smul_smul]
      congr 1
      ring

private lemma alg_mul_smul (c : ℂ) (u v : Alg) : u * (c • v) = c • (u * v) := by
  rcases u with ⟨u₀,u⟩; rcases v with ⟨v₀,v⟩
  apply Prod.ext
  · change u₀ * (c * v₀) / 3 = c * (u₀ * v₀ / 3)
    ring
  · change (u₀ / 3) • P (c • v) + (c * v₀ / 3) • u = c • ((u₀ / 3) • P v + (v₀ / 3) • u)
    rw [P_smul, smul_add]
    congr 1
    · rw [smul_smul, smul_smul]
      congr 1
      ring
    · rw [smul_smul]
      congr 1
      ring

private lemma alg_norm_mul_le (u v : Alg) : ‖u * v‖ ≤ ‖u‖ * ‖v‖ := by
  have hu0 : ‖u.1‖ ≤ ‖u‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hv0 : ‖v.1‖ ≤ ‖v‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hu (i : Fin 2) : ‖u.2 i‖ ≤ ‖u‖ := by
    exact (norm_le_pi_norm u.2 i).trans (le_max_right _ _)
  have hv (i : Fin 2) : ‖v.2 i‖ ≤ ‖v‖ := by
    exact (norm_le_pi_norm v.2 i).trans (le_max_right _ _)
  have hP (i : Fin 2) : ‖P v.2 i‖ ≤ 2 * ‖v‖ := by
    fin_cases i
    · change ‖(v.2 0 + 2 * v.2 1) / (5 : ℂ)‖ ≤ 2 * ‖v‖
      rw [norm_div, show ‖(5 : ℂ)‖ = 5 by norm_num]
      calc
        ‖v.2 0 + 2 * v.2 1‖ / 5 ≤
            (‖v.2 0‖ + 2 * ‖v.2 1‖) / 5 := by
              have h := norm_add_le (v.2 0) (2 * v.2 1)
              norm_num at h ⊢
              exact div_le_div_of_nonneg_right h (by norm_num)
        _ ≤ 2 * ‖v‖ := by
              nlinarith [hv 0, hv 1, norm_nonneg (v.2 0), norm_nonneg (v.2 1), norm_nonneg v]
    · change ‖(2 * v.2 0 + 4 * v.2 1) / (5 : ℂ)‖ ≤ 2 * ‖v‖
      rw [norm_div, show ‖(5 : ℂ)‖ = 5 by norm_num]
      calc
        ‖2 * v.2 0 + 4 * v.2 1‖ / 5 ≤
            (2 * ‖v.2 0‖ + 4 * ‖v.2 1‖) / 5 := by
              have h := norm_add_le (2 * v.2 0) (4 * v.2 1)
              norm_num at h ⊢
              exact div_le_div_of_nonneg_right h (by norm_num)
        _ ≤ 2 * ‖v‖ := by
              nlinarith [hv 0, hv 1, norm_nonneg (v.2 0), norm_nonneg (v.2 1), norm_nonneg v]
  rw [Prod.norm_def]
  apply max_le
  · change ‖u.1 * v.1 / 3‖ ≤ ‖u‖ * ‖v‖
    rw [norm_div, norm_mul]
    norm_num
    have h := mul_le_mul hu0 hv0 (norm_nonneg _) (norm_nonneg _)
    have hdiv : ‖u.1‖ * ‖v.1‖ / 3 ≤ ‖u.1‖ * ‖v.1‖ := by
      nlinarith [mul_nonneg (norm_nonneg u.1) (norm_nonneg v.1)]
    exact hdiv.trans h
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mpr
    intro i
    fin_cases i
    · change ‖(u.1 / 3) • P v.2 0 + (v.1 / 3) • u.2 0‖ ≤ ‖u‖ * ‖v‖
      calc
        ‖(u.1 / 3) • P v.2 0 + (v.1 / 3) • u.2 0‖ ≤
            ‖(u.1 / 3) • P v.2 0‖ + ‖(v.1 / 3) • u.2 0‖ := norm_add_le _ _
        _ = ‖u.1 / 3‖ * ‖P v.2 0‖ + ‖v.1 / 3‖ * ‖u.2 0‖ := by rw [norm_smul, norm_smul]
        _ ≤ ‖u‖ * ‖v‖ := by
          rw [norm_div, norm_div]
          norm_num
          have hA := mul_le_mul hu0 (hP 0) (norm_nonneg _) (norm_nonneg _)
          have hB := mul_le_mul hv0 (hu 0) (norm_nonneg _) (norm_nonneg _)
          nlinarith
    · change ‖(u.1 / 3) • P v.2 1 + (v.1 / 3) • u.2 1‖ ≤ ‖u‖ * ‖v‖
      calc
        ‖(u.1 / 3) • P v.2 1 + (v.1 / 3) • u.2 1‖ ≤
            ‖(u.1 / 3) • P v.2 1‖ + ‖(v.1 / 3) • u.2 1‖ := norm_add_le _ _
        _ = ‖u.1 / 3‖ * ‖P v.2 1‖ + ‖v.1 / 3‖ * ‖u.2 1‖ := by rw [norm_smul, norm_smul]
        _ ≤ ‖u‖ * ‖v‖ := by
          rw [norm_div, norm_div]
          norm_num
          have hA := mul_le_mul hu0 (hP 1) (norm_nonneg _) (norm_nonneg _)
          have hB := mul_le_mul hv0 (hu 1) (norm_nonneg _) (norm_nonneg _)
          nlinarith

private local instance algNonUnitalNormedRing : NonUnitalNormedRing Alg where
  __ := (inferInstance : NonUnitalRing Alg)
  __ := (inferInstance : NormedAddCommGroup Alg)
  norm_mul_le := alg_norm_mul_le

private local instance algIsScalarTower : IsScalarTower ℂ Alg Alg := ⟨alg_smul_mul⟩
private local instance algSMulCommClass : SMulCommClass ℂ Alg Alg := ⟨fun c u v => by
  simpa only [smul_eq_mul] using (alg_mul_smul c u v).symm⟩

/-- The spatial numerical range of `a` in the normed algebra `A`. -/
def spatialNumericalRange {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (a : A) : Set ℂ :=
  {z | ∃ x : A, ‖x‖ = 1 ∧ ∃ φ : A →L[ℂ] ℂ, ‖φ‖ = 1 ∧ φ x = 1 ∧ φ (a * x) = z}

def claim : Prop :=
  ∀ (A : Type) [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (a : A), Convex ℝ (spatialNumericalRange a)

private def phi0 : Alg →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).comp
    (ContinuousLinearMap.snd ℂ ℂ (Fin 2 → ℂ))
private def phi1 : Alg →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).comp
    (ContinuousLinearMap.snd ℂ ℂ (Fin 2 → ℂ))

private def e : Alg := (3, 0)
private def x₁ : Alg := (0, ![1, Complex.I])
private def x₂ : Alg := (0, ![Complex.I, 1])
private def z₁ : ℂ := 1 / 5 + (2 / 5) * Complex.I
private def z₂ : ℂ := 4 / 5 + (2 / 5) * Complex.I
private def m : ℂ := 1 / 2 + (2 / 5) * Complex.I

private lemma x₁_norm : ‖x₁‖ = 1 := by
  apply le_antisymm
  · rw [Prod.norm_def]
    apply max_le
    · norm_num [x₁]
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro i
      fin_cases i <;> norm_num [x₁]
  · rw [Prod.norm_def]
    calc
      (1 : ℝ) = ‖x₁.2 0‖ := by norm_num [x₁]
      _ ≤ ‖x₁.2‖ := norm_le_pi_norm x₁.2 0
      _ ≤ max ‖x₁.1‖ ‖x₁.2‖ := le_max_right _ _

private lemma x₂_norm : ‖x₂‖ = 1 := by
  apply le_antisymm
  · rw [Prod.norm_def]
    apply max_le
    · norm_num [x₂]
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro i
      fin_cases i <;> norm_num [x₂]
  · rw [Prod.norm_def]
    calc
      (1 : ℝ) = ‖x₂.2 1‖ := by norm_num [x₂]
      _ ≤ ‖x₂.2‖ := norm_le_pi_norm x₂.2 1
      _ ≤ max ‖x₂.1‖ ‖x₂.2‖ := le_max_right _ _

private lemma phi0_norm : ‖phi0‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound phi0 (by norm_num)
    intro x
    simpa [phi0, Prod.norm_def] using
      (norm_le_pi_norm x.2 0).trans (le_max_right ‖x.1‖ ‖x.2‖)
  · have h := ContinuousLinearMap.le_opNorm phi0 x₁
    rw [x₁_norm, mul_one] at h
    simpa [phi0, x₁] using h

private lemma phi1_norm : ‖phi1‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound phi1 (by norm_num)
    intro x
    simpa [phi1, Prod.norm_def] using
      (norm_le_pi_norm x.2 1).trans (le_max_right ‖x.1‖ ‖x.2‖)
  · have h := ContinuousLinearMap.le_opNorm phi1 x₂
    rw [x₂_norm, mul_one] at h
    simpa [phi1, x₂] using h

private lemma e_mul (x : Alg) : e * x = (x.1, P x.2) := by
  rcases x with ⟨x₀,x⟩
  apply Prod.ext
  · change (3 : ℂ) * x₀ / 3 = x₀
    ring
  · change ((3 : ℂ) / 3) • P x + (x₀ / 3) • 0 = P x
    simp

private lemma z_points : z₁ ∈ spatialNumericalRange e ∧ z₂ ∈ spatialNumericalRange e := by
  constructor
  · refine ⟨x₁, ?_, phi0, phi0_norm, ?_, ?_⟩
    · exact x₁_norm
    · norm_num [phi0, x₁]
    · rw [e_mul]
      norm_num [phi0, x₁, P, z₁]
      ring
  · refine ⟨x₂, ?_, phi1, phi1_norm, ?_, ?_⟩
    · exact x₂_norm
    · norm_num [phi1, x₂]
    · rw [e_mul]
      norm_num [phi1, x₂, P, z₂]
      ring

private def phase (c : ℂ) : ℂ := if c = 0 then 1 else (starRingEnd ℂ) c / ‖c‖

private lemma phase_norm (c : ℂ) : ‖phase c‖ = 1 := by
  by_cases hc : c = 0
  · simp [phase, hc]
  · rw [phase, if_neg hc, norm_div, Complex.norm_conj, Complex.norm_real]
    rw [Real.norm_of_nonneg (norm_nonneg c)]
    exact div_self (ne_of_gt (norm_pos_iff.mpr hc))

private lemma phase_mul (c : ℂ) : c * phase c = ‖c‖ := by
  by_cases hc : c = 0
  · simp [phase, hc]
  · rw [phase, if_neg hc]
    have hn : (‖c‖ : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (norm_pos_iff.mpr hc))
    calc
      c * ((starRingEnd ℂ) c / ‖c‖) = (c * (starRingEnd ℂ) c) / ‖c‖ := by ring
      _ = (Complex.normSq c : ℂ) / ‖c‖ := by rw [Complex.mul_conj]
      _ = ((‖c‖ ^ 2 : ℝ) : ℂ) / ‖c‖ := by rw [Complex.normSq_eq_norm_sq]
      _ = ‖c‖ := by
        apply (div_eq_iff hn).2
        norm_num [pow_two]

private lemma phi_eval (φ : Alg →L[ℂ] ℂ) (x : Alg) :
    φ x = φ (1, 0) * x.1 + φ (0, ![1, 0]) * x.2 0 + φ (0, ![0, 1]) * x.2 1 := by
  rcases x with ⟨x₀, x⟩
  have hdecomp : (x₀, x) = x₀ • (1, 0) + x 0 • (0, ![1, 0]) + x 1 • (0, ![0, 1]) := by
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp
  rw [hdecomp, map_add, map_add, map_smul, map_smul, map_smul]
  simp [smul_eq_mul, mul_comm, add_comm]

private lemma coeff_sum_le_one (φ : Alg →L[ℂ] ℂ)
    (hφ : ‖φ‖ = 1) :
    ‖φ (1, 0)‖ + ‖φ (0, ![1, 0])‖ + ‖φ (0, ![0, 1])‖ ≤ 1 := by
  let c₀ := φ (1, 0)
  let c₁ := φ (0, ![1, 0])
  let c₂ := φ (0, ![0, 1])
  let q : Alg := (phase c₀, ![phase c₁, phase c₂])
  have hq : ‖q‖ ≤ 1 := by
    dsimp [q]
    apply max_le
    · exact (phase_norm c₀).le
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro i
      fin_cases i
      · exact (phase_norm c₁).le
      · exact (phase_norm c₂).le
  have hlin : φ q = c₀ * phase c₀ + c₁ * phase c₁ + c₂ * phase c₂ := by
    rw [phi_eval]
    rfl
  have hbound : ‖φ q‖ ≤ 1 := by
    calc
      ‖φ q‖ ≤ ‖φ‖ * ‖q‖ := ContinuousLinearMap.le_opNorm φ q
      _ ≤ 1 := by rw [hφ]; nlinarith [hφ, hq]
  rw [hlin, phase_mul, phase_mul, phase_mul] at hbound
  have hbound' : ‖((‖c₀‖ + ‖c₁‖ + ‖c₂‖ : ℝ) : ℂ)‖ ≤ 1 := by
    convert hbound using 1
    norm_num [Complex.ofReal_add]
  rw [Complex.norm_real, Real.norm_of_nonneg
    (by positivity : 0 ≤ ‖c₀‖ + ‖c₁‖ + ‖c₂‖)] at hbound'
  simpa [c₀, c₁, c₂] using hbound'

private lemma norm_mul_bound (c y : ℂ) (hy : ‖y‖ ≤ 1) : ‖c * y‖ ≤ ‖c‖ := by
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (norm_nonneg c)

private lemma extremal_re (z : ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hn : ‖z‖ ≤ b) (hr : z.re = b) : z.im = 0 := by
  have hs := Complex.sq_norm z
  rw [Complex.normSq_apply, hr] at hs
  nlinarith only [hs, hn, hb, norm_nonneg z, sq_nonneg z.im]

private lemma extremal_im (z : ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hn : ‖z‖ ≤ b) (hi : z.im = b) : z.re = 0 := by
  have hs := Complex.sq_norm z
  rw [Complex.normSq_apply, hi] at hs
  nlinarith only [hs, hn, hb, norm_nonneg z, sq_nonneg z.re]

private lemma support_im_zero (a b c : ℂ) (hs : a + b + c = 1)
    (hn : ‖a‖ + ‖b‖ + ‖c‖ ≤ 1) : a.im = 0 ∧ b.im = 0 ∧ c.im = 0 := by
  have ha := Complex.re_le_norm a
  have hb := Complex.re_le_norm b
  have hc := Complex.re_le_norm c
  have hr : a.re + b.re + c.re = 1 := by
    simpa only [Complex.add_re, Complex.one_re] using congrArg Complex.re hs
  have ea : a.re = ‖a‖ := by linarith only [ha, hb, hc, hr, hn]
  have eb : b.re = ‖b‖ := by linarith only [ha, hb, hc, hr, hn]
  have ec : c.re = ‖c‖ := by linarith only [ha, hb, hc, hr, hn]
  exact ⟨extremal_re a ‖a‖ (norm_nonneg a) le_rfl ea,
    extremal_re b ‖b‖ (norm_nonneg b) le_rfl eb,
    extremal_re c ‖c‖ (norm_nonneg c) le_rfl ec⟩

private lemma midpoint_not_mem : m ∉ spatialNumericalRange e := by
  rintro ⟨x, hx, φ, hφ, hφx, hval⟩
  let c₀ : ℂ := φ (1, 0)
  let c₁ : ℂ := φ (0, ![1, 0])
  let c₂ : ℂ := φ (0, ![0, 1])
  have hp : ‖x.1‖ ≤ 1 ∧ ‖x.2‖ ≤ 1 := by
    exact max_le_iff.mp (by simpa only [Prod.norm_def] using hx.le)
  have hx1 : ‖x.2 0‖ ≤ 1 := (norm_le_pi_norm x.2 0).trans hp.2
  have hx2 : ‖x.2 1‖ ≤ 1 := (norm_le_pi_norm x.2 1).trans hp.2
  have hsum : ‖c₀‖ + ‖c₁‖ + ‖c₂‖ ≤ 1 := by
    simpa only [c₀, c₁, c₂] using coeff_sum_le_one φ hφ
  have hs : c₀ * x.1 + c₁ * x.2 0 + c₂ * x.2 1 = 1 := by
    rw [phi_eval] at hφx
    exact hφx
  have hd0 := norm_mul_bound c₀ x.1 hp.1
  have hd1 := norm_mul_bound c₁ (x.2 0) hx1
  have hd2 := norm_mul_bound c₂ (x.2 1) hx2
  obtain ⟨hi0, hi1, hi2⟩ := support_im_zero (c₀ * x.1) (c₁ * x.2 0) (c₂ * x.2 1) hs
    (by linarith only [hd0, hd1, hd2, hsum])
  have hv : c₀ * x.1 + (c₁ * x.2 0) / 5 + (2 / 5) * (c₁ * x.2 1) +
      (2 / 5) * (c₂ * x.2 0) + (4 / 5) * (c₂ * x.2 1) = m := by
    rw [e_mul, phi_eval] at hval
    change c₀ * x.1 + c₁ * ((x.2 0 + 2 * x.2 1) / 5) +
      c₂ * ((2 * x.2 0 + 4 * x.2 1) / 5) = m at hval
    convert hval using 1
    ring
  rw [show (2 / 5 : ℂ) = ((2 / 5 : ℝ) : ℂ) by norm_num,
    show (4 / 5 : ℂ) = ((4 / 5 : ℝ) : ℂ) by norm_num] at hv
  have hiv := congrArg Complex.im hv
  have hmi : m.im = 2 / 5 := by norm_num [m]
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.im_ofReal_mul,
    hi0, hi1, hi2, hmi] at hiv
  have hcross : (c₁ * x.2 1).im + (c₂ * x.2 0).im = 1 := by
    linarith only [hiv]
  have hn12 := norm_mul_bound c₁ (x.2 1) hx2
  have hn21 := norm_mul_bound c₂ (x.2 0) hx1
  have hu12 : (c₁ * x.2 1).im ≤ ‖c₁‖ := (Complex.im_le_norm _).trans hn12
  have hu21 : (c₂ * x.2 0).im ≤ ‖c₂‖ := (Complex.im_le_norm _).trans hn21
  have hc0 : ‖c₀‖ = 0 := by
    linarith only [hcross, hu12, hu21, hsum, norm_nonneg c₀]
  have hab : ‖c₁‖ + ‖c₂‖ = 1 := by
    linarith only [hcross, hu12, hu21, hsum, hc0]
  have he12 : (c₁ * x.2 1).im = ‖c₁‖ := by
    linarith only [hcross, hu12, hu21, hab]
  have he21 : (c₂ * x.2 0).im = ‖c₂‖ := by
    linarith only [hcross, hu12, hu21, hab]
  have hr12 := extremal_im (c₁ * x.2 1) ‖c₁‖ (norm_nonneg c₁) hn12 he12
  have hr21 := extremal_im (c₂ * x.2 0) ‖c₂‖ (norm_nonneg c₂) hn21 he21
  have hc0z : c₀ = 0 := norm_eq_zero.mp hc0
  have hdreal : (c₁ * x.2 0).re + (c₂ * x.2 1).re = 1 := by
    rw [hc0z, zero_mul, zero_add] at hs
    simpa only [Complex.add_re, Complex.one_re] using congrArg Complex.re hs
  have hu1 : (c₁ * x.2 0).re ≤ ‖c₁‖ := (Complex.re_le_norm _).trans hd1
  have hu2 : (c₂ * x.2 1).re ≤ ‖c₂‖ := (Complex.re_le_norm _).trans hd2
  have he1 : (c₁ * x.2 0).re = ‖c₁‖ := by linarith only [hdreal, hu1, hu2, hab]
  have he2 : (c₂ * x.2 1).re = ‖c₂‖ := by linarith only [hdreal, hu1, hu2, hab]
  have hrv := congrArg Complex.re hv
  have hmr : m.re = 1 / 2 := by norm_num [m]
  rw [hc0z, zero_mul] at hrv
  simp only [Complex.add_re, Complex.zero_re, Complex.div_ofNat_re,
    Complex.re_ofReal_mul, hr12, hr21, he1, he2, hmr] at hrv
  have ha : ‖c₁‖ = 1 / 2 := by linarith only [hrv, hab]
  have hb : ‖c₂‖ = 1 / 2 := by linarith only [hrv, hab]
  have hprod : (c₁ * x.2 0) * (c₂ * x.2 1) = (c₁ * x.2 1) * (c₂ * x.2 0) := by ring
  have hpre := congrArg Complex.re hprod
  rw [Complex.mul_re (c₁ * x.2 0) (c₂ * x.2 1),
    Complex.mul_re (c₁ * x.2 1) (c₂ * x.2 0), hi1, hi2, hr12, hr21,
    he1, he2, he12, he21, ha, hb] at hpre
  norm_num at hpre

private lemma nonconvex : ¬ Convex ℝ (spatialNumericalRange e) := by
  intro h
  have hm := h z_points.1 z_points.2
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  apply midpoint_not_mem
  convert hm using 1
  norm_num [m, z₁, z₂, Complex.real_smul]
  ring

theorem result : ¬ claim := by
  intro h
  exact nonconvex (h Alg e)

end D5.S3.Analytic.NumericalRange.SpatialNumericalRangeNonconvex
