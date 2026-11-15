/- GID: D5/S3/Quantum/Analysis/PositiveMomentRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/PositiveMomentRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive continuous moment maps and one-coordinate rigidity. -/

/-
admission_basis: escape-witness
escape_witness: kadison_real
kadison_real: proof_shape: content; consumer: exists_starAlgHom_of_square,
through the private Jordan and power lemmas.
exists_starAlgHom_of_square: proof_shape: content; constructs the full
continuous star-algebra homomorphism from coordinate-square equality.
All private lemmas are consumed in these proofs.
Classical Kadison inequality and single-generator multiplicative-domain
rigidity. The finite positive variance argument does not assume commutation
of individual effects. Bernstein approximation passes this inequality to
arbitrary continuous real functions in an arbitrary ordered C-star algebra.
-/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Tactic.Ring

/-! # Positive moment rigidity

Kadison's self-adjoint inequality is obtained from finite positive variance
and Bernstein approximation. Equality at the interval coordinate determines
the entire continuous moment map.
-/

noncomputable section

open Filter
open scoped ComplexOrder Topology unitInterval Polynomial

namespace D5.S3.Quantum.Analysis.PositiveMomentRigidity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Inclusion of real continuous functions into complex continuous functions. -/
def complexify : C(I, ℝ) →ₐ[ℝ] C(I, ℂ) :=
  Complex.ofRealAm.compLeftContinuous ℝ Complex.continuous_ofReal

private theorem continuous_complexify : Continuous (complexify : C(I, ℝ) → C(I, ℂ)) :=
  (Complex.ofRealCLM.compLeftContinuous ℝ I).continuous

private theorem complexify_nonneg {g : C(I, ℝ)} (hg : 0 ≤ g) :
    0 ≤ complexify g := by
  intro x
  change (0 : ℂ) ≤ (g x : ℂ)
  exact Complex.nonneg_iff.mpr ⟨hg x, by simp⟩

private theorem image_selfadjoint (Z : C(I, ℂ) →ₚ[ℂ] A) (g : C(I, ℝ)) :
    IsSelfAdjoint (Z (complexify g)) := by
  have hp := (Z.map_nonneg (complexify_nonneg (show 0 ≤ g ⊔ 0 from le_sup_right))).isSelfAdjoint
  have hn := (Z.map_nonneg (complexify_nonneg (show 0 ≤ (-g) ⊔ 0 from le_sup_right))).isSelfAdjoint
  have he : g = (g ⊔ 0) - ((-g) ⊔ 0) := by
    ext x
    simp [max_zero_sub_max_neg_zero_eq_self]
  rw [he, map_sub, map_sub]
  exact hp.sub hn

private theorem finite_variance {κ : Type*} [Fintype κ] (E : κ → A) (a : κ → ℝ)
    (hE : ∀ i, 0 ≤ E i) (hunit : ∑ i, E i = 1) :
    (∑ i, a i • E i) * (∑ i, a i • E i) ≤ ∑ i, (a i) ^ 2 • E i := by
  classical
  let S := ∑ i, a i • E i
  have hS : IsSelfAdjoint S :=
    isSelfAdjoint_sum _ fun i _ => (IsSelfAdjoint.all (a i)).smul (hE i).isSelfAdjoint
  have identity : (∑ i, (a i • (1 : A) - S) * E i * (a i • (1 : A) - S)) =
      (∑ i, (a i) ^ 2 • E i) - S * S := by
    have term (i : κ) : (a i • (1 : A) - S) * E i * (a i • (1 : A) - S) =
        (a i) ^ 2 • E i - (a i • E i) * S - S * (a i • E i) + S * E i * S := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_sub, smul_smul, pow_two]
      abel
    simp_rw [term]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, hunit]
    change (∑ i, (a i) ^ 2 • E i) - S * S - S * S + S * 1 * S = _
    rw [mul_one]
    abel
  apply sub_nonneg.mp
  rw [← identity]
  exact Finset.sum_nonneg fun i _ =>
    (((IsSelfAdjoint.all (a i)).smul (IsSelfAdjoint.one A)).sub hS).conjugate_nonneg (hE i)

omit [StarOrderedRing A] in
private theorem image_bernstein (Z : C(I, ℂ) →ₚ[ℂ] A) (g : C(I, ℝ)) (n : ℕ) :
    Z (complexify (bernsteinApproximation n g)) =
      ∑ k : Fin (n + 1), g (bernstein.z k) • Z (complexify (bernstein n k)) := by
  have he : bernsteinApproximation n g =
      ∑ k : Fin (n + 1), g (bernstein.z k) • bernstein n k := by
    ext x
    simp [bernsteinApproximation.apply, mul_comm]
  rw [he, map_sum, map_sum]
  congr 1
  ext k
  rw [map_smul, Z.map_smul_of_tower]

/-- Self-adjoint Kadison inequality for every positive unital continuous
moment map, with no dimension, separability or complete-positivity premise. -/
theorem kadison_real (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1) (g : C(I, ℝ)) :
    Z (complexify g) * Z (complexify g) ≤ Z (complexify (g * g)) := by
  have finite (n : ℕ) :
      Z (complexify (bernsteinApproximation n g)) *
        Z (complexify (bernsteinApproximation n g)) ≤
      Z (complexify (bernsteinApproximation n (g * g))) := by
    let E : Fin (n + 1) → A := fun k => Z (complexify (bernstein n k))
    have hE : ∀ k, 0 ≤ E k := fun k =>
      Z.map_nonneg (complexify_nonneg (fun _ => bernstein_nonneg))
    have hsum : ∑ k, E k = 1 := by
      have hb : (∑ k : Fin (n + 1), bernstein n k) = 1 := by
        ext x
        simp [bernstein.probability]
      dsimp [E]
      rw [← map_sum, ← map_sum, hb, map_one, hunit]
    simpa only [image_bernstein, ContinuousMap.mul_apply, pow_two] using
      finite_variance E (fun k => g (bernstein.z k)) hE hsum
  have hg := (map_continuous Z).continuousAt.tendsto.comp
    (continuous_complexify.continuousAt.tendsto.comp (bernsteinApproximation_uniform g))
  have hgg := (map_continuous Z).continuousAt.tendsto.comp
    (continuous_complexify.continuousAt.tendsto.comp (bernsteinApproximation_uniform (g * g)))
  exact le_of_tendsto_of_tendsto' (hg.mul hg) hgg finite

private theorem zero_linear_term (B D : A)
    (hp : ∀ t : ℝ, 0 ≤ t • B + t ^ 2 • D) : B = 0 := by
  have lower (B D : A) (h : ∀ t : ℝ, 0 ≤ t • B + t ^ 2 • D) : 0 ≤ B := by
    have hpos (t : ℝ) (ht : 0 < t) : 0 ≤ B + t • D := by
      apply (smul_nonneg_iff_nonneg_of_pos_left ht).mp
      simpa only [smul_add, smul_smul, pow_two] using h t
    have ht : Tendsto (fun t : ℝ => B + t • D) (𝓝[>] 0) (𝓝 B) := by
      have hc : Continuous (fun t : ℝ => B + t • D) := by fun_prop
      simpa only [zero_smul, add_zero] using
        (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hpos t ht)
  have hneg : ∀ t : ℝ, 0 ≤ t • (-B) + t ^ 2 • D := by
    intro t
    simpa only [neg_smul, smul_neg, neg_sq] using hp (-t)
  exact le_antisymm (neg_nonneg.mp (lower (-B) D hneg)) (lower B D hp)

private theorem jordan (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1)
    (u : C(I, ℝ)) (hsquare : Z (complexify (u * u)) = Z (complexify u) * Z (complexify u))
    (h : C(I, ℝ)) :
    (2 : ℝ) • Z (complexify (u * h)) =
      Z (complexify u) * Z (complexify h) + Z (complexify h) * Z (complexify u) := by
  apply sub_eq_zero.mp
  apply zero_linear_term _ (Z (complexify (h * h)) - Z (complexify h) * Z (complexify h))
  intro t
  have hsrc : (u + t • h) * (u + t • h) =
      u * u + t • ((2 : ℝ) • (u * h)) + t ^ 2 • (h * h) := by
    ext x
    simp
    ring
  have he : Z (complexify ((u + t • h) * (u + t • h))) -
      Z (complexify (u + t • h)) * Z (complexify (u + t • h)) =
      t • ((2 : ℝ) • Z (complexify (u * h)) -
        (Z (complexify u) * Z (complexify h) + Z (complexify h) * Z (complexify u))) +
      t ^ 2 • (Z (complexify (h * h)) - Z (complexify h) * Z (complexify h)) := by
    rw [hsrc]
    simp only [map_add, map_smul, PositiveLinearMap.map_smul_of_tower, hsquare,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul,
      pow_two]
    abel
  rw [← he]
  exact sub_nonneg.mpr (kadison_real Z hunit (u + t • h))

private def realCoordinate : C(I, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual closed-interval coordinate, including both endpoints. -/
def coordinate : C(I, ℂ) := complexify realCoordinate

private theorem image_powers (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1)
    (hsquare : Z (coordinate * coordinate) = Z coordinate * Z coordinate) (n : ℕ) :
    Z (complexify (realCoordinate ^ n)) = Z coordinate ^ n := by
  induction n with
  | zero => simpa using hunit
  | succ n ih =>
    have hj := jordan Z hunit realCoordinate (by simpa [coordinate] using hsquare)
      (realCoordinate ^ n)
    rw [ih] at hj
    have hm : realCoordinate * realCoordinate ^ n = realCoordinate ^ (n + 1) :=
      (pow_succ' _ _).symm
    rw [hm] at hj
    apply (smul_right_injective A (show (2 : ℝ) ≠ 0 by norm_num))
    change (2 : ℝ) • Z (complexify (realCoordinate ^ (n + 1))) = _
    rw [hj]
    change Z coordinate * Z coordinate ^ n + Z coordinate ^ n * Z coordinate = _
    rw [← pow_succ', ← pow_succ]
    exact (two_smul ℝ (Z coordinate ^ (n + 1))).symm

private theorem image_polynomial (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1)
    (hsquare : Z (coordinate * coordinate) = Z coordinate * Z coordinate) (p : ℝ[X]) :
    Z (complexify (Polynomial.toContinuousMapOnAlgHom I p)) =
      Polynomial.aeval (Z coordinate) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    have he : Polynomial.toContinuousMapOnAlgHom I (Polynomial.monomial n a) =
        a • realCoordinate ^ n := by
      ext x
      simp [realCoordinate, Polynomial.eval_monomial]
    rw [he, map_smul, Z.map_smul_of_tower, image_powers Z hunit hsquare]
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [Algebra.smul_def]

private theorem polynomial_multiplicative (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1)
    (hsquare : Z (coordinate * coordinate) = Z coordinate * Z coordinate)
    (p q : ℝ[X]) :
    Z (complexify (Polynomial.toContinuousMapOnAlgHom I p *
      Polynomial.toContinuousMapOnAlgHom I q)) =
      Z (complexify (Polynomial.toContinuousMapOnAlgHom I p)) *
        Z (complexify (Polynomial.toContinuousMapOnAlgHom I q)) := by
  rw [← map_mul, image_polynomial Z hunit hsquare, map_mul,
    image_polynomial Z hunit hsquare, image_polynomial Z hunit hsquare]

private theorem real_multiplicative (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1)
    (hsquare : Z (coordinate * coordinate) = Z coordinate * Z coordinate)
    (f g : C(I, ℝ)) :
    Z (complexify (f * g)) = Z (complexify f) * Z (complexify g) := by
  have hc : Continuous (fun f : C(I, ℝ) => Z (complexify f)) :=
    (map_continuous Z).comp continuous_complexify
  have hp (p : ℝ[X]) : ∀ g : C(I, ℝ),
      Z (complexify (Polynomial.toContinuousMapOnAlgHom I p * g)) =
        Z (complexify (Polynomial.toContinuousMapOnAlgHom I p)) * Z (complexify g) := by
    intro g
    apply closure_minimal (s := (polynomialFunctions I : Set C(I, ℝ))) ?_
      (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) (continuous_const.mul hc))
      (continuousMap_mem_polynomialFunctions_closure 0 1 g)
    rintro _ ⟨q, -, rfl⟩
    exact polynomial_multiplicative Z hunit hsquare p q
  apply closure_minimal (s := (polynomialFunctions I : Set C(I, ℝ))) ?_
    (isClosed_eq (hc.comp (continuous_id.mul continuous_const)) (hc.mul continuous_const))
    (continuousMap_mem_polynomialFunctions_closure 0 1 f)
  rintro _ ⟨p, -, rfl⟩
  exact hp p g

private def realPart (f : C(I, ℂ)) : C(I, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
private def imagPart (f : C(I, ℂ)) : C(I, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩

private theorem split_complex (f : C(I, ℂ)) :
    f = complexify (realPart f) + Complex.I • complexify (imagPart f) := by
  ext x
  change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (f x)).symm

private theorem star_complexify (f : C(I, ℝ)) : star (complexify f) = complexify f := by
  ext x
  change star ((f x : ℝ) : ℂ) = (f x : ℂ)
  simp

/-- Equality for the square of the single interval coordinate forces the
ENTIRE positive unital map to be a genuine star-algebra homomorphism. -/
theorem exists_starAlgHom_of_square (Z : C(I, ℂ) →ₚ[ℂ] A) (hunit : Z 1 = 1)
    (hsquare : Z (coordinate * coordinate) = Z coordinate * Z coordinate) :
    ∃ Φ : C(I, ℂ) →⋆ₐ[ℂ] A, (∀ f, Φ f = Z f) ∧ Φ coordinate = Z coordinate := by
  have hm (f g : C(I, ℂ)) : Z (f * g) = Z f * Z g := by
    have hr (a b : C(I, ℝ)) :
        Z (complexify a * complexify b) = Z (complexify a) * Z (complexify b) := by
      rw [← map_mul, real_multiplicative Z hunit hsquare]
    rw [split_complex f, split_complex g]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, hr]
  have hs (f : C(I, ℂ)) : Z (star f) = star (Z f) := by
    rw [split_complex f]
    simp only [star_add, star_smul, star_complexify, map_add, map_smul,
      (image_selfadjoint Z (realPart f)).star_eq,
      (image_selfadjoint Z (imagPart f)).star_eq]
  refine ⟨{ toFun := Z
            map_one' := hunit
            map_mul' := hm
            map_zero' := map_zero Z
            map_add' := map_add Z
            commutes' := ?_
            map_star' := hs }, (fun _ => rfl), rfl⟩
  intro z
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hunit, Algebra.algebraMap_eq_smul_one]

end D5.S3.Quantum.Analysis.PositiveMomentRigidity
