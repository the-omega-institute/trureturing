/- GID: D5/S3/Quantum/Algebra/Knot/TwoStrandTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/TwoStrandTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All signed two-strand Artin powers have an exact path-trace formula. -/

import D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation

variable {L : Type*} [Fintype L] [DecidableEq L]
attribute [local instance] Classical.propDecidable
local instance (R : L → L → Prop) (n : ℕ) (s t : L) : DecidableEq (LegalPath R n s t) :=
  Classical.decEq _

/-- Signed powers of the sole two-strand generator in the existing Artin presentation. -/
def twoStrand (m : ℤ) : PositiveBraid :=
  ⟨⟨2, by omega⟩, (lastGenerator 1 (by omega)) ^ m⟩

private theorem spectral_mul {S : Type*} [Ring S] [Algebra ℂ S]
    (P : S) (hP : P * P = P) (a b c e : ℂ) :
    (a • (1 - P) + b • P) * (c • (1 - P) + e • P) =
      (a * c) • (1 - P) + (b * e) • P := by
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
    abel
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    hQQ, hPQ, hQP, hP, smul_zero, add_zero, zero_add, mul_comm c a, mul_comm e b]

private theorem spectral_zpow {S : Type*} [Ring S] [Algebra ℂ S]
    (P : S) (hP : P * P = P) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (u : Sˣ) (hu : (u : S) = a • (1 - P) + b • P)
    (hui : ((u⁻¹ : Sˣ) : S) = a⁻¹ • (1 - P) + b⁻¹ • P) (m : ℤ) :
    ((u ^ m : Sˣ) : S) = (a ^ m) • (1 - P) + (b ^ m) • P := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [zpow_add_one, Units.val_mul, ih, hu, spectral_mul P hP,
      zpow_add_one₀ ha, zpow_add_one₀ hb]
  | pred m ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hui, spectral_mul P hP,
      zpow_sub_one₀ ha, zpow_sub_one₀ hb]

private theorem twoStrand_writhe (m : ℤ) : writhe 2 (twoStrand m).2 = m := by
  change (exponentHom 2 ((lastGenerator 1 (by omega)) ^ m)).toAdd = m
  rw [map_zpow]
  simp [lastGenerator, exponentHom]

private theorem generator_spectral
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) :
    (representation R hR d hd δ hδ hPF A hA hparameter 2 s
        (lastGenerator 1 (by omega)) : C R 2 s) =
      A⁻¹ • (1 - lastProjection R d δ 1 (by omega) s) +
        (-A ^ 3) • lastProjection R d δ 1 (by omega) s ∧
    (representation R hR d hd δ hδ hPF A hA hparameter 2 s
        (lastGenerator 1 (by omega))⁻¹ : C R 2 s) =
      A • (1 - lastProjection R d δ 1 (by omega) s) +
        (-A ^ 3)⁻¹ • lastProjection R d δ 1 (by omega) s := by
  constructor
  · simp only [representation, lastGenerator, PresentedGroup.toGroup.of]
    change A⁻¹ • 1 + (A * (δ : ℂ)) • lastProjection R d δ 1 (by omega) s =
      A⁻¹ • (1 - lastProjection R d δ 1 (by omega) s) +
        (-A ^ 3) • lastProjection R d δ 1 (by omega) s
    funext t
    ext x y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hparameter]
    field_simp [hA]
    ring
  · rw [map_inv]
    simp only [representation, lastGenerator, PresentedGroup.toGroup.of]
    change A • 1 + (A⁻¹ * (δ : ℂ)) • lastProjection R d δ 1 (by omega) s =
      A • (1 - lastProjection R d δ 1 (by omega) s) +
        (-A ^ 3)⁻¹ • lastProjection R d δ 1 (by omega) s
    funext t
    ext x y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hparameter]
    field_simp [hA]
    ring

private theorem tau_sub (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (X Y : C R n s) :
    tau R d δ n s (X - Y) = tau R d δ n s X - tau R d δ n s Y := by
  simp only [tau, Pi.sub_apply, Matrix.trace_sub, mul_sub, Finset.sum_sub_distrib, sub_div]

/-- The exact two-eigenvalue formula, for every positive or negative crossing exponent. -/
theorem two_strand_trace
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) (m : ℤ) :
    normalizedTrace R hR d hd δ hδ hPF A hA hparameter s (twoStrand m) =
      (δ : ℂ) * (-A ^ 3) ^ m *
        (A⁻¹ ^ m * (1 - (δ : ℂ)⁻¹ ^ 2) + (-A ^ 3) ^ m * (δ : ℂ)⁻¹ ^ 2) := by
  let P : C R 2 s := lastProjection R d δ 1 (by omega) s
  let ρ := representation R hR d hd δ hδ hPF A hA hparameter 2 s
  have htrace := weighted_path_markov_trace R hR d hd δ hδ hPF
  have hP : P * P = P := ((htrace 1 s).2.2.2.2.2.2.2.2.2 (by omega)).2.2.2
  have hone : tau R d δ 2 s 1 = 1 := (htrace 2 s).2.2.2.2.2.2.2.2.1
  have hone1 : tau R d δ 1 s 1 = 1 := (htrace 1 s).2.2.2.2.2.2.2.2.1
  have htauP : tau R d δ 2 s P = (δ : ℂ)⁻¹ ^ 2 := by
    have hh := ((htrace 1 s).2.2.2.2.2.2.2.2.2 (by omega)).2.1 (1 : C R 1 s)
    have hi : iota R 1 s 1 = 1 := (iotaHom R 1 s).map_one
    simpa only [hi, one_mul, hone1, mul_one, P] using hh
  have hspectral := generator_spectral R hR d hd δ hδ hPF A hA hparameter s
  have hi : (((ρ (lastGenerator 1 (by omega)))⁻¹ : (C R 2 s)ˣ) : C R 2 s) =
      A⁻¹⁻¹ • (1 - P) + (-A ^ 3)⁻¹ • P := by
    simpa only [ρ, P, map_inv, inv_inv] using hspectral.2
  have hpowers := spectral_zpow P hP A⁻¹ (-A ^ 3) (inv_ne_zero hA)
    (neg_ne_zero.mpr (pow_ne_zero _ hA)) (ρ (lastGenerator 1 (by omega)))
    hspectral.1 hi m
  have hr : (ρ ((twoStrand m).2) : C R 2 s) =
      (A⁻¹ ^ m) • (1 - P) + ((-A ^ 3) ^ m) • P := by
    change (ρ ((lastGenerator 1 (by omega)) ^ m) : C R 2 s) = _
    rw [map_zpow]
    exact hpowers
  have hadd (X Y : C R 2 s) :
      tau R d δ 2 s (X + Y) = tau R d δ 2 s X + tau R d δ 2 s Y := by
    simp only [tau, Pi.add_apply, Matrix.trace_add, mul_add, Finset.sum_add_distrib, add_div]
  change (δ : ℂ) ^ (2 - 1) * (-A ^ 3) ^ writhe 2 (twoStrand m).2 *
    tau R d δ 2 s (ρ ((twoStrand m).2) : C R 2 s) = _
  rw [twoStrand_writhe, hr, hadd, tau_smul, tau_smul, tau_sub, hone, htauP]
  norm_num

#print axioms two_strand_trace
end D5.S3.Quantum.Algebra.Knot.TwoStrandTrace
