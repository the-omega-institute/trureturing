/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fractional zero-mode monomial weights, the exact point spectrum and the ground line. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement
import D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum
import Mathlib.Data.Finsupp.Weight

/-!
The ground line and monomial weights of the concrete third-cover complement.
Transport the native `PolynomialFockLZeroSpectrum.lZero_spectrum` along the
ordinary vacuum slice of the proved tensor splitting. The zero-mode shift is
that of `ThirdCoverVirasoro.coverMode`.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverGroundSpectrum

open MvPolynomial PolynomialFockSugawaraSupport PolynomialFockLZeroSpectrum
open ThirdCoverIntegerFactor ThirdCoverComplement
open ThirdCoverVirasoro (coverMode)
open scoped TensorProduct

/-- The total native cover frequency of a complement occupation vector. -/
def occupationEnergy (d : Complement →₀ ℕ) : ℕ :=
  d.sum fun k e => (k.val + 1) * e

private theorem energy_mapDomain (d : Complement →₀ ℕ) :
    energy (d.mapDomain (Subtype.val : Complement → ℕ)) = occupationEnergy d := by
  unfold energy occupationEnergy
  exact Finsupp.sum_mapDomain_index (fun k => mul_zero (k + 1))
    (fun k a b => mul_add (k + 1) a b)

@[simp] theorem occupationEnergy_eq_zero_iff (d : Complement →₀ ℕ) :
    occupationEnergy d = 0 ↔ d = 0 := by
  letI : Finsupp.NonTorsionWeight ℕ (fun k : Complement => k.val + 1) :=
    ⟨by
      intro r k h
      rw [nsmul_eq_mul] at h
      exact (Nat.mul_eq_zero.mp h).resolve_right (Nat.succ_ne_zero k.val)⟩
  have hw : Finsupp.weight (fun k : Complement => k.val + 1) d = occupationEnergy d := by
    simp only [Finsupp.weight_apply, occupationEnergy, Nat.nsmul_eq_mul]
    exact Finsupp.sum_congr fun k _ => Nat.mul_comm _ _
  rw [← hw]
  exact Finsupp.weight_eq_zero_iff_eq_zero (fun k : Complement => k.val + 1)

private theorem nativeLZero_monomial (d : ℕ →₀ ℕ) (a : ℂ) :
    L 0 (monomial d a) = (energy d : ℂ) • monomial d a := by
  let u : EnergyFiber (energy d) := ⟨d, rfl⟩
  have h : monomial d (1 : ℂ) ∈ lZeroEigenspace (energy d) := by
    rw [(lZero_spectrum (energy d)).1]
    exact Submodule.subset_span ⟨u, rfl⟩
  change (L 0 - (energy d : ℂ) • (LinearMap.id : Module.End ℂ Fock))
    (monomial d (1 : ℂ)) = 0 at h
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
  have hm : monomial d a = a • monomial d (1 : ℂ) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, h, smul_comm a (energy d : ℂ)]

private theorem nativeLZero_one : L 0 (1 : Fock) = 0 := by
  simpa [energy] using nativeLZero_monomial (0 : ℕ →₀ ℕ) (1 : ℂ)

/-- On the ordinary vacuum slice, the covered zero mode acts on the complement alone. -/
private theorem coverMode_zero_rename (Q : ComplementFock) :
    coverMode 0 (rename (Subtype.val : Complement → ℕ) Q) =
      rename Subtype.val (fractionalVirasoro 0 Q) := by
  have h := DFunLike.congr_fun (split_coverMode sqrtThree_sq 0) ((1 : Fock) ⊗ₜ[ℂ] Q)
  rw [LinearEquiv.conj_apply_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, nativeLZero_one, TensorProduct.zero_tmul, zero_add] at h
  have hj := congrArg (join sqrtThree (ne_zero_of_sq_eq_three sqrtThree_sq)) h
  change join sqrtThree _ (split sqrtThree _ (coverMode 0
      (join sqrtThree _ ((1 : Fock) ⊗ₜ[ℂ] Q)))) =
    join sqrtThree _ ((1 : Fock) ⊗ₜ[ℂ] fractionalVirasoro 0 Q) at hj
  rw [split, AlgEquiv.apply_symm_apply] at hj
  simpa only [join_tmul, map_one, one_mul] using hj

/-- The actual fractional Virasoro zero mode acts diagonally on every monomial. -/
theorem fractionalVirasoro_zero_monomial (d : Complement →₀ ℕ) (a : ℂ) :
    fractionalVirasoro 0 (monomial d a) =
      ((1 / 9 : ℂ) + (occupationEnergy d : ℂ) / 3) • monomial d a := by
  apply rename_injective _ Subtype.val_injective
  rw [← coverMode_zero_rename, map_smul, rename_monomial]
  simp only [coverMode, mul_zero, one_div, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, nativeLZero_monomial, energy_mapDomain,
    smul_smul, ← add_smul]
  have hscalar : (3 : ℂ)⁻¹ * (occupationEnergy d : ℂ) + 9⁻¹ =
      9⁻¹ + (occupationEnergy d : ℂ) / 3 := by ring
  simp only [ite_true, hscalar]

/-- Each coefficient is multiplied by the eigenvalue of its occupation vector. -/
theorem fractionalVirasoro_zero_coeff (Q : ComplementFock) (d : Complement →₀ ℕ) :
    (fractionalVirasoro 0 Q).coeff d =
      ((1 / 9 : ℂ) + (occupationEnergy d : ℂ) / 3) * Q.coeff d := by
  classical
  conv_lhs => rw [Q.as_sum]
  simp only [map_sum, coeff_sum, fractionalVirasoro_zero_monomial, coeff_smul, smul_eq_mul,
    coeff_monomial, mul_ite, mul_zero, Finset.sum_ite_eq']
  by_cases hd : d ∈ Q.support
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd, notMem_support_iff.mp hd, mul_zero]

private theorem eigenvalue_eq_of_coeff_ne_zero {Q : ComplementFock} {a : ℂ}
    (hQ : fractionalVirasoro 0 Q = a • Q) {d : Complement →₀ ℕ} (hd : Q.coeff d ≠ 0) :
    (1 / 9 : ℂ) + (occupationEnergy d : ℂ) / 3 = a := by
  have h := congrArg (fun P : ComplementFock => P.coeff d) hQ
  change (fractionalVirasoro 0 Q).coeff d = (a • Q).coeff d at h
  rw [fractionalVirasoro_zero_coeff, coeff_smul, smul_eq_mul] at h
  exact mul_right_cancel₀ hd h

/-- The lowest-weight eigenspace is the line generated by the vacuum polynomial. -/
theorem fractionalVirasoro_zero_ground_eigenspace :
    LinearMap.ker (fractionalVirasoro 0 - (1 / 9 : ℂ) •
      (LinearMap.id : Module.End ℂ ComplementFock)) =
      Submodule.span ℂ ({(1 : ComplementFock)} : Set ComplementFock) := by
  apply le_antisymm
  · intro Q hQ
    have heig : fractionalVirasoro 0 Q = (1 / 9 : ℂ) • Q := by
      simpa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] using hQ
    have hm : Q = monomial 0 (Q.coeff 0) := by
      apply eq_monomial_of_support_subset_singleton
      intro d hd
      have hvalue := eigenvalue_eq_of_coeff_ne_zero heig (mem_support_iff.mp hd)
      have hcast : (occupationEnergy d : ℂ) = 0 := by
        linear_combination 3 * hvalue
      have henergy : occupationEnergy d = 0 := by exact_mod_cast hcast
      exact Set.mem_singleton_iff.mpr ((occupationEnergy_eq_zero_iff d).mp henergy)
    refine Submodule.mem_span_singleton.mpr ⟨Q.coeff 0, ?_⟩
    simpa only [monomial_zero', C_eq_smul_one] using hm.symm
  · apply Submodule.span_le.mpr
    intro Q hQ
    rw [Set.mem_singleton_iff] at hQ
    subst Q
    have hvac : fractionalVirasoro 0 (1 : ComplementFock) = (1 / 9 : ℂ) • 1 := by
      simpa using fractionalVirasoro_vacuum 0 le_rfl
    simpa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using hvac

/-- The point spectrum is exactly the nonnegative integer shifts by thirds of `1 / 9`. -/
theorem fractionalVirasoro_zero_eigenvalue (a : ℂ) :
    (∃ Q : ComplementFock, Q ≠ 0 ∧ fractionalVirasoro 0 Q = a • Q) ↔
      ∃ n : ℕ, a = (1 / 9 : ℂ) + (n : ℂ) / 3 := by
  classical
  constructor
  · rintro ⟨Q, hQ, heig⟩
    obtain ⟨d, hd⟩ : ∃ d : Complement →₀ ℕ, Q.coeff d ≠ 0 := by
      by_contra! h
      apply hQ
      apply MvPolynomial.ext
      intro d
      simpa using h d
    exact ⟨occupationEnergy d, (eigenvalue_eq_of_coeff_ne_zero heig hd).symm⟩
  · rintro ⟨n, rfl⟩
    let d : Complement →₀ ℕ := Finsupp.single ⟨0, by decide⟩ n
    refine ⟨monomial d 1, ?_, ?_⟩
    · exact fun h => one_ne_zero (monomial_eq_zero.mp h)
    · have hd : occupationEnergy d = n := by
        simp [d, occupationEnergy, Finsupp.sum_single_index]
      rw [fractionalVirasoro_zero_monomial, hd]

theorem fractionalVirasoro_zero_eigenvalue_lower_bound {Q : ComplementFock} {a : ℂ}
    (hQ : Q ≠ 0) (heig : fractionalVirasoro 0 Q = a • Q) : (1 / 9 : ℝ) ≤ a.re := by
  obtain ⟨n, rfl⟩ := (fractionalVirasoro_zero_eigenvalue a).mp ⟨Q, hQ, heig⟩
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.natCast_re]
  exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg n) (by norm_num))

/-- The real eigenvalues attain their minimum at the vacuum. -/
theorem fractionalVirasoro_zero_minimum :
    IsLeast {x : ℝ | ∃ Q : ComplementFock, Q ≠ 0 ∧ fractionalVirasoro 0 Q = (x : ℂ) • Q}
      (1 / 9) := by
  refine ⟨⟨1, one_ne_zero, ?_⟩, ?_⟩
  · simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, if_pos rfl] using
      (show fractionalVirasoro 0 (1 : ComplementFock) = (1 / 9 : ℂ) • 1 by
        simpa using fractionalVirasoro_vacuum 0 le_rfl)
  · rintro x ⟨Q, hQ, heig⟩
    simpa only [Complex.ofReal_re] using fractionalVirasoro_zero_eigenvalue_lower_bound hQ heig

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverGroundSpectrum
