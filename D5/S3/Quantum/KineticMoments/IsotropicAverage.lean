/- GID: D5/S3/Quantum/KineticMoments/IsotropicAverage
   generality: G
   mirror-B: D5/B/S3/Quantum/KineticMoments/IsotropicAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Determine isotropic even directional moments by a weighted recurrence. -/

/-
isotropic_average:
  proof_shape: content
  escape_witness: weighted_recurrence (integrated polynomial coefficient comparison)
  admission_basis: escape-witness
integrable_directional:
  proof_shape: bind-only
  escape_witness: none; consumer: OddMoment.multiplier_integral
  admission_basis: escape-witness (host isotropic_average; this is a consumed helper)
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

/- All statements are universal algebraic or integral identities; no finite certificate,
   enumeration, checker, or numerical reduction is delivered. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Polynomial.Expand

open scoped BigOperators RealInnerProductSpace
open MeasureTheory Polynomial

namespace D5.S3.Quantum.KineticMoments.IsotropicAverage

noncomputable def simultaneousRotation {N : ℕ} (R : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)))
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : (Fin N → EuclideanSpace ℝ (Fin 3)) := fun j => R (P j)

def IsIsotropic {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) : Prop :=
  ∀ R : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)),
    LinearMap.det R.toLinearEquiv.toLinearMap = 1 →
      MeasurePreserving (simultaneousRotation R) ν ν

private noncomputable def weightedMoment {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s i : ℕ) (q : (EuclideanSpace ℝ (Fin 3))) : ℝ :=
  ∫ P, ‖P j‖^(2*s) * ⟪q, P j⟫^(2*i) ∂ν

private theorem even_rotation_same_norm (f : (EuclideanSpace ℝ (Fin 3)) → ℝ)
    (hneg : ∀ x, f (-x) = f x)
    (hinv : ∀ (R : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3))),
      LinearMap.det R.toLinearEquiv.toLinearMap = 1 → ∀ x, f (R x) = f x)
    (x y : (EuclideanSpace ℝ (Fin 3))) (hxy : ‖x‖ = ‖y‖) : f x = f y := by
  by_cases h : x = y
  · rw [h]
  let R := (ℝ ∙ (x - y)).reflection
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hdim := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 2)
    (sub_ne_zero.mpr h)
  have hR : LinearMap.det R.toLinearEquiv.toLinearMap = 1 := by
    simpa [R, hdim] using (ℝ ∙ (x-y)).det_reflection
  have hRx : R x = -y := by
    have hneg : -R x = y := by
      change -(ℝ ∙ (x-y)).reflection x = y
      rw [← Submodule.reflection_orthogonal_apply]
      exact Submodule.reflection_sub hxy
    simpa using congrArg (fun z : (EuclideanSpace ℝ (Fin 3)) => -z) hneg
  have hi := hinv R hR x
  rw [hRx, hneg] at hi
  exact hi.symm

private theorem weightedMoment_neg {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s i : ℕ) (q : (EuclideanSpace ℝ (Fin 3))) :
    weightedMoment ν j s i (-q) = weightedMoment ν j s i q := by
  simp [weightedMoment, inner_neg_left, pow_mul]

private theorem weightedMoment_smul {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s i : ℕ) (c : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) :
    weightedMoment ν j s i (c • q) = c^(2*i) * weightedMoment ν j s i q := by
  simp only [weightedMoment, inner_smul_left, conj_trivial, mul_pow]
  simp_rw [show ∀ P : (Fin N → EuclideanSpace ℝ (Fin 3)),
    ‖P j‖^(2*s)*(c^(2*i)*⟪q, P j⟫^(2*i)) = c^(2*i)*(‖P j‖^(2*s)*⟪q, P j⟫^(2*i))
    from fun P => by ring]
  exact integral_const_mul _ _

private theorem weightedMoment_rotation {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (hν : IsIsotropic ν) (j : Fin N) (s i : ℕ) (q : (EuclideanSpace ℝ (Fin 3)))
    (R : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3))) (hR : LinearMap.det R.toLinearEquiv.toLinearMap = 1) :
    weightedMoment ν j s i (R q) = weightedMoment ν j s i q := by
  have he : MeasurableEmbedding (simultaneousRotation (N := N) R) :=
    (Homeomorph.piCongrRight (fun _ : Fin N => R.toHomeomorph)).measurableEmbedding
  have hi := (hν R hR).integral_comp he
    (fun P : (Fin N → EuclideanSpace ℝ (Fin 3)) => ‖P j‖^(2*s)*⟪R q, P j⟫^(2*i))
  simpa [weightedMoment, simultaneousRotation, R.inner_map_map, R.norm_map] using hi.symm

private theorem weightedMoment_radial {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (hν : IsIsotropic ν) (j : Fin N) (s i : ℕ) (q e : (EuclideanSpace ℝ (Fin 3))) (he : ‖e‖ = 1) :
    weightedMoment ν j s i q = ‖q‖^(2*i) * weightedMoment ν j s i e := by
  have hs := even_rotation_same_norm (weightedMoment ν j s i)
    (weightedMoment_neg ν j s i)
    (fun R hR x => weightedMoment_rotation ν hν j s i x R hR)
    q (‖q‖ • e) (by simp [norm_smul, he])
  rw [hs, weightedMoment_smul]

private theorem mixed_bound (p x y : (EuclideanSpace ℝ (Fin 3))) (s n r : ℕ) (hr : r ≤ n) :
    ‖‖p‖^(2*s) * ⟪x, p⟫^(n-r) * ⟪y, p⟫^r‖ ≤
      (‖x‖^(n-r) * ‖y‖^r) * ‖p‖^(2*s+n) := by
  calc
    _ = ‖p‖^(2*s) * ‖⟪x, p⟫‖^(n-r) * ‖⟪y, p⟫‖^r := by
      simp [norm_mul, norm_pow]
    _ ≤ ‖p‖^(2*s) * (‖x‖*‖p‖)^(n-r) * (‖y‖*‖p‖)^r := by
      gcongr
      · exact norm_inner_le_norm x p
      · exact norm_inner_le_norm y p
    _ = _ := by
      rw [show 2*s+n = 2*s+(n-r)+r by omega, pow_add, pow_add, mul_pow, mul_pow]
      ring

private theorem integrable_mixed {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s n r : ℕ) (hr : r ≤ n) (x y : (EuclideanSpace ℝ (Fin 3)))
    (hm : Integrable (fun P => ‖P j‖^(2*s+n)) ν) :
    Integrable (fun P => ‖P j‖^(2*s) * ⟪x, P j⟫^(n-r) * ⟪y, P j⟫^r) ν := by
  apply (hm.const_mul (‖x‖^(n-r)*‖y‖^r)).mono'
  · exact (by fun_prop : Continuous
      (fun P : (Fin N → EuclideanSpace ℝ (Fin 3)) => ‖P j‖^(2*s) * ⟪x, P j⟫^(n-r) * ⟪y, P j⟫^r)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun P => mixed_bound (P j) x y s n r hr)

private noncomputable def momentPolynomial {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s n : ℕ) (x y : (EuclideanSpace ℝ (Fin 3))) : ℝ[X] :=
  ∑ r ∈ Finset.range (n+1), Polynomial.monomial r
    ((n.choose r : ℝ) * ∫ P, ‖P j‖^(2*s) * ⟪x, P j⟫^(n-r) * ⟪y, P j⟫^r ∂ν)

private theorem momentPolynomial_eval {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s n : ℕ) (x y : (EuclideanSpace ℝ (Fin 3)))
    (hm : Integrable (fun P => ‖P j‖^(2*s+n)) ν) (t : ℝ) :
    (momentPolynomial ν j s n x y).eval t =
      ∫ P, ‖P j‖^(2*s) * ⟪x+t • y, P j⟫^n ∂ν := by
  have hI r (hr : r ∈ Finset.range (n+1)) :=
    integrable_mixed ν j s n r (by simpa using Finset.mem_range.mp hr) x y hm
  simp only [momentPolynomial, eval_finsetSum, eval_monomial]
  calc
    _ = ∑ r ∈ Finset.range (n+1),
        ∫ P, ((n.choose r : ℝ)*t^r) * (‖P j‖^(2*s)*⟪x, P j⟫^(n-r)*⟪y, P j⟫^r) ∂ν := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [integral_const_mul]
      ring
    _ = ∫ P, ∑ r ∈ Finset.range (n+1),
        ((n.choose r : ℝ)*t^r) * (‖P j‖^(2*s)*⟪x, P j⟫^(n-r)*⟪y, P j⟫^r) ∂ν := by
      rw [integral_finsetSum]
      intro r hr
      exact (hI r hr).const_mul _
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro P
      simp only [inner_add_left, inner_smul_left, conj_trivial]
      rw [add_comm ⟪x, P j⟫ (t*⟪y, P j⟫), add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp [mul_pow]
      ring

private theorem momentPolynomial_coeff {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (s n r : ℕ) (x y : (EuclideanSpace ℝ (Fin 3))) (hr : r ≤ n) :
    (momentPolynomial ν j s n x y).coeff r =
      (n.choose r : ℝ) * ∫ P, ‖P j‖^(2*s) * ⟪x, P j⟫^(n-r) * ⟪y, P j⟫^r ∂ν := by
  simp [momentPolynomial, Polynomial.coeff_monomial, Finset.sum_ite_eq', hr]

private theorem coeff_radial_polynomial (i : ℕ) :
    (((1 : ℝ[X]) + X^2)^i).coeff 2 = (i : ℝ) := by
  have he : ((1 : ℝ[X])+X^2)^i = Polynomial.expand ℝ 2 ((1+X)^i) := by
    simp
  rw [he, Polynomial.coeff_expand (by norm_num : 0 < 2)]
  simp [Polynomial.coeff_one_add_X_pow]

private theorem norm_sq_axis_add (l : Fin 3) (hl : l ≠ 0) (t : ℝ) :
    ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) + t • (EuclideanSpace.single l (1 : ℝ))‖^2 = 1+t^2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, EuclideanSpace.inner_single_left, hl, Ne.symm hl]

private theorem choose_double_two (i : ℕ) : (2*(i+1)).choose 2 = (i+1)*(2*i+1) := by
  rw [Nat.choose_two_right, show 2*(i+1)-1 = 2*i+1 by omega]
  rw [show 2*(i+1)*(2*i+1) = 2*((i+1)*(2*i+1)) by ring]
  omega

private theorem mixed_second_coefficient {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (hν : IsIsotropic ν) (j : Fin N) (s i : ℕ)
    (hm : Integrable (fun P => ‖P j‖^(2*s+2*(i+1))) ν)
    (l : Fin 3) (hl : l ≠ 0) :
    (2*i+1 : ℝ) * (∫ P, ‖P j‖^(2*s) * (P j 0)^(2*i) * (P j l)^2 ∂ν) =
      weightedMoment ν j s (i+1) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
  have hp : momentPolynomial ν j s (2*(i+1)) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ((EuclideanSpace.single l (1 : ℝ))) =
      Polynomial.C (weightedMoment ν j s (i+1) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))) *
        (1 + Polynomial.X^2)^(i+1) := by
    apply Polynomial.funext
    intro t
    rw [momentPolynomial_eval ν j s (2*(i+1)) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ((EuclideanSpace.single l (1 : ℝ))) hm t]
    change weightedMoment ν j s (i+1) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))+t • (EuclideanSpace.single l (1 : ℝ))) = _
    rw [weightedMoment_radial ν hν j s (i+1) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))+t • (EuclideanSpace.single l (1 : ℝ))) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) (by simp)]
    rw [pow_mul, norm_sq_axis_add l hl t]
    simp
    ring
  have hc := congrArg (fun p : ℝ[X] => p.coeff 2) hp
  rw [momentPolynomial_coeff ν j s (2*(i+1)) 2 ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ((EuclideanSpace.single l (1 : ℝ))) (by omega),
    Polynomial.coeff_C_mul, coeff_radial_polynomial, choose_double_two] at hc
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul, show 2*(i+1)-2 = 2*i by omega, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at hc
  have hi : (i : ℝ)+1 ≠ 0 := by positivity
  apply (mul_left_cancel₀ hi)
  nlinarith [hc]

private theorem weighted_recurrence {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (hν : IsIsotropic ν) (j : Fin N) (s i : ℕ)
    (hm : Integrable (fun P => ‖P j‖^(2*s+2*(i+1))) ν) :
    (2*i+1 : ℝ) * weightedMoment ν j (s+1) i ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) =
      (2*i+3 : ℝ) * weightedMoment ν j s (i+1) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
  have hI (l : Fin 3) : Integrable
      (fun P => ‖P j‖^(2*s) * (P j 0)^(2*i) * (P j l)^2) ν := by
    simpa [EuclideanSpace.inner_single_left, show 2*(i+1)-2 = 2*i by omega] using
      integrable_mixed ν j s (2*(i+1)) 2 (by omega) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ((EuclideanSpace.single l (1 : ℝ))) hm
  have he : weightedMoment ν j (s+1) i ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) =
      ∑ l : Fin 3, ∫ P, ‖P j‖^(2*s) * (P j 0)^(2*i) * (P j l)^2 ∂ν := by
    rw [← integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun l _ => hI l)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro P
    simp only [weightedMoment, EuclideanSpace.inner_single_left, map_one, one_mul]
    rw [show 2*(s+1) = 2*s+2 by omega, pow_add, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, Fin.sum_univ_succ, Fin.sum_univ_two]
  have hzero : (∫ P, ‖P j‖^(2*s) * (P j 0)^(2*i) * (P j 0)^2 ∂ν) =
      weightedMoment ν j s (i+1) ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro P
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul, weightedMoment]
    rw [show 2*(i+1)=2*i+2 by omega, pow_add]
    ring
  have h1 := mixed_second_coefficient ν hν j s i hm (1 : Fin 3) (by decide)
  have h2 := mixed_second_coefficient ν hν j s i hm (2 : Fin 3) (by decide)
  simp only [Fin.zero_eta, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at *
  rw [hzero]
  nlinarith [h1, h2]

private theorem weighted_isotropic_axis {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (hν : IsIsotropic ν) (j : Fin N) (i s : ℕ)
    (hm : Integrable (fun P => ‖P j‖^(2*(s+i))) ν) :
    (2*i+1 : ℝ) * weightedMoment ν j s i ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) =
      ∫ P, ‖P j‖^(2*(s+i)) ∂ν := by
  induction i generalizing s with
  | zero => simp [weightedMoment]
  | succ i ih =>
    have hm' : Integrable (fun P => ‖P j‖^(2*s+2*(i+1))) ν := by
      simpa [show 2*s+2*(i+1)=2*(s+(i+1)) by omega] using hm
    have hr := weighted_recurrence ν hν j s i hm'
    have hi := ih (s+1) (by simpa [show s+1+i=s+(i+1) by omega] using hm)
    convert hr.symm.trans hi using 1
    · push_cast; ring
    · congr 1
      funext P
      congr 1
      omega

theorem integrable_directional {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (j : Fin N) (i : ℕ) (q : (EuclideanSpace ℝ (Fin 3)))
    (hm : Integrable (fun P => ‖P j‖^(2*i)) ν) :
    Integrable (fun P => ⟪q, P j⟫^(2*i)) ν := by
  simpa using integrable_mixed ν j 0 (2*i) 0 (by omega) q 0 (by simpa using hm)

theorem isotropic_average {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (hν : IsIsotropic ν) (j : Fin N) (i : ℕ) (q : (EuclideanSpace ℝ (Fin 3)))
    (hm : Integrable (fun P => ‖P j‖^(2*i)) ν) :
    (∫ P, ⟪q, P j⟫^(2*i) ∂ν) =
      ‖q‖^(2*i) * (∫ P, ‖P j‖^(2*i) ∂ν) / (2*i+1 : ℝ) := by
  have hc := weighted_isotropic_axis ν hν j i 0 (by simpa using hm)
  have hrad := weightedMoment_radial ν hν j 0 i q ((EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) (by simp)
  simp only [weightedMoment, Nat.mul_zero, pow_zero, one_mul, zero_add] at hc hrad
  rw [hrad]
  have hi : (2*i+1 : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination ‖q‖^(2*i) * hc

end D5.S3.Quantum.KineticMoments.IsotropicAverage
