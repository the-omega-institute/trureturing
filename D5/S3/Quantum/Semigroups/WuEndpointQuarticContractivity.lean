/- GID: D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointQuarticContractivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict tracial three-to-four contractivity for the signed Wu endpoint. -/

import D5.S3.Quantum.Semigroups.WuEndpointQuarticMajorization
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Tracial Wu endpoint contractivity

For a nonscalar PSD input, join its mean-scaled identity to the input
along a trace-preserving segment. The quartic floor forces the ratio
of the integer powers of the two moments to decrease strictly.

With mean `a`, the variance of the input at time `t` is `t ^ 2`
times its initial value at `X`. The derivative of the ratio is
`-12 * a * m₄(Yₜ)^2 * Dₜ / (t * m₃(Xₜ)^5)`, where `Dₜ` is the
Euler expression in `A1_quartic_floor`. The floor is strictly
positive for nonscalar `X` and `0 < t < 1`.
-/

noncomputable section

open Matrix Set Unitary
open scoped BigOperators ComplexOrder

namespace WuRankOneEndpointFloor

private def radial (a : ℝ) (X : TwoMode) (t : ℝ) : TwoMode :=
  ((a * (1 - t) : ℝ) : ℂ) • (1 : TwoMode) + (t : ℂ) • X

private def radialValue (a x t : ℝ) : ℝ := a * (1 - t) + t * x

private theorem radial_zero (a : ℝ) (X : TwoMode) :
    radial a X 0 = (a : ℂ) • (1 : TwoMode) := by
  simp [radial]

private theorem radial_one (a : ℝ) (X : TwoMode) : radial a X 1 = X := by
  simp [radial]

private theorem A1_radial (a : ℝ) (X : TwoMode) (t : ℝ) :
    A₁ (radial a X t) = radial a (A₁ X) t := by
  simp only [radial, map_add, map_smul, A₁_one]

private theorem radial_posSemidef {a t : ℝ} {X : TwoMode}
    (ha : 0 ≤ a) (hX : X.PosSemidef) (ht : t ∈ Icc (0 : ℝ) 1) :
    (radial a X t).PosSemidef := by
  have hI : (1 : TwoMode).PosSemidef := Matrix.PosSemidef.one
  exact (hI.smul (Complex.zero_le_real.mpr (mul_nonneg ha (sub_nonneg.mpr ht.2)))).add
    (hX.smul (Complex.zero_le_real.mpr ht.1))

private def modeMoment (k : ℕ) (x : Mode → ℝ) : ℝ :=
  (∑ i, x i ^ k) / 4

/-- The input eigenbasis works along the entire radial segment. -/
private theorem traceMoment_radial {X : TwoMode} (hX : X.IsHermitian)
    (k : ℕ) (a t : ℝ) :
    endpointTraceMoment k (radial a X t) =
      modeMoment k (fun i => radialValue a (hX.eigenvalues i) t) := by
  let F := conjStarAlgAut ℂ TwoMode hX.eigenvectorUnitary
  let d : Mode → ℂ := fun i => (hX.eigenvalues i : ℂ)
  let e : Mode → ℂ := fun i => (radialValue a (hX.eigenvalues i) t : ℂ)
  have hd : X = F (diagonal d) := hX.spectral_theorem
  have he : diagonal e =
      ((a * (1 - t) : ℝ) : ℂ) • (1 : TwoMode) + (t : ℂ) • diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [e, d, radialValue, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_add, Complex.ofReal_mul]
    · simp [Matrix.smul_apply, hij]
  have hrad : radial a X t = F (diagonal e) := by
    simp only [radial, he, map_add, map_smul, map_one, ← hd]
  have hpow : radial a X t ^ k = F (diagonal (e ^ k)) := by
    rw [← diagonal_pow e k, map_pow F (diagonal e) k, hrad]
  unfold endpointTraceMoment modeMoment
  rw [hpow]
  change ((conjStarAlgAut ℂ TwoMode hX.eigenvectorUnitary (diagonal (e ^ k))).trace).re / 4 = _
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul,
    trace_diagonal, Complex.re_sum]
  refine congrArg (fun s : ℝ => s / 4) ?_
  apply Finset.sum_congr rfl
  intro i _
  change ((radialValue a (hX.eigenvalues i) t : ℂ) ^ k).re = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

private theorem traceMoment_eigenvalues {X : TwoMode} (hX : X.IsHermitian) (k : ℕ) :
    endpointTraceMoment k X = modeMoment k hX.eigenvalues := by
  simpa only [radial_one, radialValue, sub_self, mul_zero, one_mul, zero_add] using
    traceMoment_radial hX k 0 1

private theorem traceMoment_scalar (a : ℝ) (k : ℕ) :
    endpointTraceMoment k ((a : ℂ) • (1 : TwoMode)) = a ^ k := by
  rw [← radial_zero a (0 : TwoMode), traceMoment_radial Matrix.isHermitian_zero]
  simp only [radialValue, sub_zero, mul_one, zero_mul, add_zero, modeMoment,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private theorem scalar_of_eigenvalues_eq {X : TwoMode} (hX : X.IsHermitian) {a : ℝ}
    (ha : ∀ i, hX.eigenvalues i = a) : X = (a : ℂ) • (1 : TwoMode) := by
  have hd : diagonal (RCLike.ofReal ∘ hX.eigenvalues) = (a : ℂ) • (1 : TwoMode) := by
    ext i j
    by_cases hij : i = j
    · subst j
      change diagonal (fun i => (hX.eigenvalues i : ℂ)) i i =
        ((a : ℂ) • (1 : TwoMode)) i i
      simp [ha, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.smul_apply, hij]
  calc
    X = conjStarAlgAut ℂ TwoMode hX.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hX.eigenvalues)) := hX.spectral_theorem
    _ = _ := by rw [hd, map_smul, map_one]

private theorem traceMoment_pos_of_eigenvalues {X : TwoMode} (hX : X.IsHermitian)
    (hX₀ : X ≠ 0) (k : ℕ) (hpow : ∀ i : Mode, 0 ≤ hX.eigenvalues i ^ k) :
    0 < endpointTraceMoment k X := by
  have hne : hX.eigenvalues ≠ 0 := fun h => hX₀ (hX.eigenvalues_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [traceMoment_eigenvalues hX, modeMoment]
  refine div_pos (Finset.sum_pos' (fun j _ => hpow j) ?_) (by norm_num)
  exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hpow i) (pow_ne_zero k hi).symm⟩

private theorem traceMoment_pos_of_psd {X : TwoMode} (hX : X.PosSemidef)
    (hX₀ : X ≠ 0) (k : ℕ) : 0 < endpointTraceMoment k X := by
  refine traceMoment_pos_of_eigenvalues hX.isHermitian hX₀ k (fun i => ?_)
  exact pow_nonneg (hX.eigenvalues_nonneg i) k

private theorem radial_mean {X : TwoMode} (hX : X.IsHermitian) {a : ℝ}
    (ha : endpointTraceMoment 1 X = a) (t : ℝ) :
    endpointTraceMoment 1 (radial a X t) = a := by
  rw [traceMoment_eigenvalues hX] at ha
  rw [traceMoment_radial hX]
  simp only [modeMoment, pow_one, Fintype.sum_prod_type, Fin.sum_univ_two, radialValue] at ha ⊢
  linear_combination t * ha

private theorem radial_variance {X : TwoMode} (hX : X.IsHermitian) {a : ℝ}
    (ha : endpointTraceMoment 1 X = a) (t : ℝ) :
    endpointTraceMoment 2 (radial a X t) - a ^ 2 =
      t ^ 2 * (endpointTraceMoment 2 X - a ^ 2) := by
  rw [traceMoment_eigenvalues hX] at ha
  rw [traceMoment_radial hX, traceMoment_eigenvalues hX]
  simp only [modeMoment, pow_one, Fintype.sum_prod_type, Fin.sum_univ_two, radialValue] at ha ⊢
  linear_combination (2 * a * t * (1 - t)) * ha

private theorem variance_pos {X : TwoMode} (hX : X.IsHermitian) {a : ℝ}
    (ha : endpointTraceMoment 1 X = a) (hns : X ≠ (a : ℂ) • (1 : TwoMode)) :
    0 < endpointTraceMoment 2 X - a ^ 2 := by
  have hvar : endpointTraceMoment 2 X - a ^ 2 =
      modeMoment 2 (fun i => hX.eigenvalues i - a) := by
    rw [traceMoment_eigenvalues hX] at ha ⊢
    simp only [modeMoment, pow_one, Fintype.sum_prod_type, Fin.sum_univ_two] at ha ⊢
    linear_combination (2 * a) * ha
  have hex : ∃ i : Mode, hX.eigenvalues i ≠ a := by
    by_contra! hall
    exact hns (scalar_of_eigenvalues_eq hX hall)
  obtain ⟨i, hi⟩ := hex
  rw [hvar, modeMoment]
  refine div_pos (Finset.sum_pos' (fun j _ => sq_nonneg (hX.eigenvalues j - a)) ?_) (by norm_num)
  exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (sq_nonneg _)
    (pow_ne_zero 2 (sub_ne_zero.mpr hi)).symm⟩

private theorem radialValue_hasDerivAt (a x t : ℝ) :
    HasDerivAt (radialValue a x) (x - a) t := by
  have he : radialValue a x = fun s => a + s * (x - a) := by
    funext s
    unfold radialValue
    ring
  rw [he]
  simpa only [one_mul] using ((hasDerivAt_id' t).mul_const (x - a)).const_add a

private theorem traceMoment_radial_hasDerivAt {X : TwoMode} (hX : X.IsHermitian)
    (k : ℕ) (a t : ℝ) :
    HasDerivAt (fun s => endpointTraceMoment (k + 1) (radial a X s))
      ((∑ i : Mode, ((k : ℝ) + 1) * radialValue a (hX.eigenvalues i) t ^ k *
        (hX.eigenvalues i - a)) / 4) t := by
  simp only [traceMoment_radial hX, modeMoment]
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
    (radialValue_hasDerivAt a (hX.eigenvalues i) t).fun_pow (k + 1)

/-- The radial derivative of a normalized trace moment at nonzero time. -/
private theorem traceMoment_radial_euler {X : TwoMode} (hX : X.IsHermitian)
    (k : ℕ) (a t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s => endpointTraceMoment (k + 1) (radial a X s))
      (((k : ℝ) + 1) * (endpointTraceMoment (k + 1) (radial a X t) -
        a * endpointTraceMoment k (radial a X t)) / t) t := by
  have h := traceMoment_radial_hasDerivAt hX k a t
  convert h using 1
  symm
  apply (eq_div_iff ht).2
  rw [mul_comm _ t, ← mul_div_assoc, Finset.mul_sum]
  have hterm (i : Mode) :
      t * (((k : ℝ) + 1) * radialValue a (hX.eigenvalues i) t ^ k *
        (hX.eigenvalues i - a)) =
      ((k : ℝ) + 1) * (radialValue a (hX.eigenvalues i) t ^ (k + 1) -
        a * radialValue a (hX.eigenvalues i) t ^ k) := by
    rw [pow_succ]
    have hx : t * (hX.eigenvalues i - a) = radialValue a (hX.eigenvalues i) t - a := by
      unfold radialValue
      ring
    linear_combination (((k : ℝ) + 1) * radialValue a (hX.eigenvalues i) t ^ k) * hx
  simp only [hterm, traceMoment_radial hX, modeMoment]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem momentRatio_hasDerivAt {u v : ℝ → ℝ} {a t x₂ y₃ : ℝ}
    (ht : t ≠ 0) (hu : u t ≠ 0)
    (hu' : HasDerivAt u (3 * (u t - a * x₂) / t) t)
    (hv' : HasDerivAt v (4 * (v t - a * y₃) / t) t) :
    HasDerivAt (fun s => (v s) ^ 3 / (u s) ^ 4)
      (-(12 * a * (v t) ^ 2 * (u t * y₃ - x₂ * v t)) / (t * (u t) ^ 5)) t := by
  convert (hv'.fun_pow 3).fun_div (hu'.fun_pow 4) (pow_ne_zero 4 hu) using 1
  norm_num
  field_simp [ht, hu]
  ring

/-- Strict contractivity for PSD inputs outside the nonnegative scalar ray. -/
theorem A1_quartic_contractivity_strict (X : TwoMode) (hX : X.PosSemidef)
    (hns : ¬ ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : TwoMode)) :
    (endpointTraceMoment 4 (A₁ X)) ^ 3 < (endpointTraceMoment 3 X) ^ 4 := by
  let a := endpointTraceMoment 1 X
  have hX₀ : X ≠ 0 := fun h => hns ⟨0, le_rfl, by simpa using h⟩
  have ha : 0 < a := traceMoment_pos_of_psd hX hX₀ 1
  have hvar := variance_pos hX.isHermitian (a := a) rfl
    (fun h => hns ⟨a, ha.le, h⟩)
  have hY := A₁_isHermitian X hX.isHermitian
  have hmeanY : endpointTraceMoment 1 (A₁ X) = a := by
    simp only [a, endpointTraceMoment, pow_one, A₁_trace]
  let u (t : ℝ) := endpointTraceMoment 3 (radial a X t)
  let v (t : ℝ) := endpointTraceMoment 4 (radial a (A₁ X) t)
  let D (t : ℝ) := u t * endpointTraceMoment 3 (radial a (A₁ X) t) -
    endpointTraceMoment 2 (radial a X t) * v t
  let ratio (t : ℝ) := (v t) ^ 3 / (u t) ^ 4
  let slope (t : ℝ) := -(12 * a * (v t) ^ 2 * D t) / (t * (u t) ^ 5)
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < u t := by
    refine traceMoment_pos_of_psd (radial_posSemidef ha.le hX ht) (fun hz => ?_) 3
    have hm := radial_mean hX.isHermitian (a := a) rfl t
    rw [hz] at hm
    exact ha.ne' (by simpa [endpointTraceMoment] using hm.symm)
  have hvpos (t : ℝ) : 0 < v t := by
    have hrad : (radial a (A₁ X) t).IsHermitian := by
      change (radial a (A₁ X) t)ᴴ = radial a (A₁ X) t
      simp only [radial, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hY.eq]
    refine traceMoment_pos_of_eigenvalues hrad (fun hz => ?_) 4 (fun i => ?_)
    · have hm := radial_mean hY hmeanY t
      rw [hz] at hm
      exact ha.ne' (by simpa [endpointTraceMoment] using hm.symm)
    · exact (Even.pow_nonneg (by decide : Even 4)) _
  have hD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < D t := by
    have hfloor := A1_quartic_floor (radial a X t)
      (radial_posSemidef ha.le hX ⟨ht.1.le, ht.2.le⟩)
    rw [A1_radial, radial_mean hX.isHermitian (a := a) rfl,
      radial_variance hX.isHermitian (a := a) rfl] at hfloor
    have hfloor_pos :
        0 < a ^ 2 * (t ^ 2 * (endpointTraceMoment 2 X - a ^ 2)) ^ 2 / 5 :=
      div_pos (mul_pos (pow_pos ha 2) (pow_pos (mul_pos (pow_pos ht.1 2) hvar) 2))
        (by norm_num)
    exact hfloor_pos.trans_le hfloor
  have hucont : Continuous u := continuous_iff_continuousAt.mpr
    (fun t => (traceMoment_radial_hasDerivAt hX.isHermitian 2 a t).continuousAt)
  have hvcont : Continuous v := continuous_iff_continuousAt.mpr
    (fun t => (traceMoment_radial_hasDerivAt hY 3 a t).continuousAt)
  have hcont : ContinuousOn ratio (Icc (0 : ℝ) 1) :=
    (hvcont.pow 3).continuousOn.div (hucont.pow 4).continuousOn
      (fun t ht => pow_ne_zero 4 (hpos t ht).ne')
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt ratio (slope t) t := by
    have hu' : HasDerivAt u (3 * (u t - a * endpointTraceMoment 2 (radial a X t)) / t) t := by
      simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num] using
        traceMoment_radial_euler hX.isHermitian 2 a t ht.1.ne'
    have hv' :
        HasDerivAt v (4 * (v t - a * endpointTraceMoment 3 (radial a (A₁ X) t)) / t) t := by
      simpa only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num] using
        traceMoment_radial_euler hY 3 a t ht.1.ne'
    exact momentRatio_hasDerivAt ht.1.ne' (hpos t ⟨ht.1.le, ht.2.le⟩).ne' hu' hv'
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope ratio slope
    (show (0 : ℝ) < 1 by norm_num) hcont hderiv
  have hslope : slope t < 0 :=
    div_neg_of_neg_of_pos
      (neg_lt_zero.mpr (mul_pos (mul_pos (mul_pos (by norm_num) ha)
        (pow_pos (hvpos t) 2)) (hD t ht)))
      (mul_pos ht.1 (pow_pos (hpos t ⟨ht.1.le, ht.2.le⟩) 5))
  have hratio : ratio 1 < ratio 0 := by
    rw [heq, sub_zero, div_one] at hslope
    exact sub_neg.mp hslope
  have hzero : ratio 0 = 1 := by
    simp only [ratio, u, v, radial_zero, traceMoment_scalar]
    field_simp [ha.ne'] <;> ring
  rw [hzero] at hratio
  have hden : 0 < (endpointTraceMoment 3 X) ^ 4 :=
    pow_pos (traceMoment_pos_of_psd hX hX₀ 3) 4
  simp only [ratio, u, v, radial_one] at hratio
  exact (div_lt_one hden).mp hratio

private theorem A1_quartic_scalar (c : ℝ) :
    (endpointTraceMoment 4 (A₁ ((c : ℂ) • (1 : TwoMode)))) ^ 3 =
      (endpointTraceMoment 3 ((c : ℂ) • (1 : TwoMode))) ^ 4 := by
  rw [map_smul, A₁_one, traceMoment_scalar, traceMoment_scalar]
  ring

/-- The signed two-mode endpoint is tracially contractive from 3 to 4 on PSD inputs. -/
theorem A1_quartic_contractivity (X : TwoMode) (hX : X.PosSemidef) :
    (endpointTraceMoment 4 (A₁ X)) ^ 3 ≤ (endpointTraceMoment 3 X) ^ 4 := by
  by_cases hs : ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : TwoMode)
  · obtain ⟨c, _, rfl⟩ := hs
    exact (A1_quartic_scalar c).le
  · exact (A1_quartic_contractivity_strict X hX hs).le

/-- Equality holds precisely on the nonnegative scalar multiples of the identity. -/
theorem A1_quartic_contractivity_eq_iff (X : TwoMode) (hX : X.PosSemidef) :
    (endpointTraceMoment 4 (A₁ X)) ^ 3 = (endpointTraceMoment 3 X) ^ 4 ↔
      ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : TwoMode) := by
  constructor
  · intro heq
    by_contra hs
    exact (A1_quartic_contractivity_strict X hX hs).ne heq
  · rintro ⟨c, _, rfl⟩
    exact A1_quartic_scalar c

#print axioms A1_quartic_contractivity_strict
#print axioms A1_quartic_contractivity
#print axioms A1_quartic_contractivity_eq_iff

end WuRankOneEndpointFloor
