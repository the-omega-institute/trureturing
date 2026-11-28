/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualConformalEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualConformalEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The inverse-twisted restricted dual has the actual conformal energy spectrum. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualBorcherds
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualPairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeVirasoro
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces
import Mathlib.LinearAlgebra.Dual.Lemmas
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The conformal zero mode and its eigenspaces on the actual P48q restricted dual. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualConformalEnergy

open scoped BigOperators Classical DirectSum
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualConformalState (omega)
open LatticeActualConformalWard (omega_product)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (nativeField)
open P48qFiniteEnergyEigenspaces (totalLZero_eigenspace_finiteDimensional)
open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qNativeDualCoefficients (bpzTerm)
open P48qNativeDualLinearField (dualField)
open P48qNativeRestrictedDualField (ActualGrade GradeDual RestrictedDual gradedPairing
  gradedPairing_apply_grade gradedPairing_dualField_coeff gradedPairing_ext)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero totalLZero_eigenvalues totalLZero_vacuum_spectrum totalWeight)

open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private source_conformal_products_checked from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeVirasoro

noncomputable section

local notation "Ω" => omega lattice (actualInverse lattice)
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "C" => HVertexOperator.coeff
local notation "Lᵈ" => HVertexOperator.coeff (dualField Ω) (-6)

/-- The weight and quasiprimary identities for the actual source conformal vector. -/
theorem sourceOmega_weight_and_quasiprimary :
    L₀ Ω = (2 : ℂ) • Ω ∧ L₁ Ω = 0 := by
  obtain ⟨_, hWeight, hQuasiprimary, _, _⟩ :=
    source_conformal_products_checked lattice rfl (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
  rw [omega_product, show (1 : ℤ) - 1 = 0 by decide] at hWeight
  rw [omega_product, show (2 : ℤ) - 1 = 1 by decide] at hQuasiprimary
  exact ⟨hWeight, hQuasiprimary⟩

private theorem sourceOmega_LOne_pow (j : ℕ) (hj : j ≠ 0) : (L₁ ^ j) Ω = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  rw [pow_succ, Module.End.mul_apply, sourceOmega_weight_and_quasiprimary.2, map_zero]

/-- On the cubic cover, the conformal BPZ coefficient at k transposes the
native coefficient at -k - 12. -/
theorem gradedPairing_dualField_omega_coeff (k : ℤ) (f : RestrictedDual) (v : State) :
    gradedPairing (C (dualField Ω) k f) v =
      gradedPairing f (C (nativeField Ω) (-k - 12) v) := by
  have hWeight : L₀ Ω = ((2 : ℕ) : ℂ) • Ω := by
    simpa only [Nat.cast_ofNat] using sourceOmega_weight_and_quasiprimary.1
  have hSum :
      (∑ j ∈ Finset.range (2 + 1), (j.factorial : ℂ)⁻¹ • bpzTerm Ω 2 k j v) =
        bpzTerm Ω 2 k 0 v := by
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    · intro j _ hj
      simp only [bpzTerm, sourceOmega_LOne_pow j hj, map_zero, Pi.zero_apply,
        LinearMap.zero_apply, smul_zero]
    · intro h
      exact (h (by decide)).elim
  have hSign : (-1 : ℂ) ^ (2 : ℕ) = 1 := by norm_num
  have hIndex : -k - 6 * ((2 : ℕ) : ℤ) + 3 * ((0 : ℕ) : ℤ) = -k - 12 := by omega
  rw [gradedPairing_dualField_coeff Ω 2 hWeight, hSum, hSign, one_smul,
    bpzTerm, pow_zero, Module.End.one_apply, hIndex]

/-- The conformal coefficient at x⁻⁶ transposes the actual twisted energy. -/
theorem gradedPairing_dual_conformal_zero (f : RestrictedDual) (v : State) :
    gradedPairing (Lᵈ f) v = gradedPairing f (totalLZero v) := by
  simpa only [show -(-6 : ℤ) - 12 = -6 by decide,
    native_conformal_coeff_neg_six_eq_totalLZero] using
    gradedPairing_dualField_omega_coeff (-6) f v

/-- The weight diagonal on the sum of the actual grade duals. -/
def dualLZero : Module.End ℂ RestrictedDual :=
  DirectSum.lmap fun w : ℝ => (w : ℂ) • (LinearMap.id : Module.End ℂ (GradeDual w))

@[simp] theorem dualLZero_apply (f : RestrictedDual) (w : ℝ) :
    dualLZero f w = (w : ℂ) • f w := by
  simp only [dualLZero, DirectSum.lmap_apply, LinearMap.smul_apply, LinearMap.id_apply]

/-- The actual inverse-twisted conformal coefficient at x⁻⁶ = z⁻² is the
weight diagonal on the restricted dual. -/
theorem dual_conformal_coeff_neg_six_eq_dualLZero : Lᵈ = dualLZero := by
  apply LinearMap.ext
  intro f
  apply gradedPairing_ext
  intro w v
  have hv : totalLZero (v : State) = (w : ℂ) • (v : State) :=
    Module.End.mem_eigenspace_iff.mp v.property
  calc
    gradedPairing (Lᵈ f) (v : State) = gradedPairing f (totalLZero (v : State)) :=
      gradedPairing_dual_conformal_zero f (v : State)
    _ = (w : ℂ) • f w v := by
      rw [hv, map_smul, gradedPairing_apply_grade f w v]
    _ = gradedPairing (dualLZero f) (v : State) := by
      rw [gradedPairing_apply_grade (dualLZero f) w v, dualLZero_apply, LinearMap.smul_apply]

theorem dual_conformal_lof (w : ℝ) (f : GradeDual w) :
    Lᵈ (DirectSum.lof ℂ ℝ GradeDual w f) = (w : ℂ) • DirectSum.lof ℂ ℝ GradeDual w f := by
  simp only [dual_conformal_coeff_neg_six_eq_dualLZero, dualLZero, DirectSum.lmap_lof,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul]

private theorem eigenvalue_eq_of_component_ne_zero {a : ℂ} {f : RestrictedDual} {w : ℝ}
    (hf : Lᵈ f = a • f) (hw : f w ≠ 0) : (w : ℂ) = a := by
  have h : (Lᵈ f) w = (a • f) w := congrArg (fun g : RestrictedDual => g w) hf
  rw [dual_conformal_coeff_neg_six_eq_dualLZero, dualLZero_apply, DirectSum.smul_apply] at h
  exact smul_left_injective ℂ hw h

/-- Inclusion of the grade dual identifies it with the entire corresponding
eigenspace of the actual dual conformal coefficient. -/
def dualConformalEigenspaceEquiv (w : ℝ) :
    GradeDual w ≃ₗ[ℂ] Module.End.eigenspace Lᵈ (w : ℂ) := by
  let includeGrade : GradeDual w →ₗ[ℂ] Module.End.eigenspace Lᵈ (w : ℂ) :=
    (DirectSum.lof ℂ ℝ GradeDual w).codRestrict _ fun f =>
      Module.End.mem_eigenspace_iff.mpr (dual_conformal_lof w f)
  refine LinearEquiv.ofBijective includeGrade ⟨?_, ?_⟩
  · intro f g h
    have hComponent := congrArg
      (fun x : Module.End.eigenspace Lᵈ (w : ℂ) => (x : RestrictedDual) w) h
    simpa only [includeGrade, LinearMap.codRestrict_apply, DirectSum.lof_apply] using hComponent
  · intro f
    refine ⟨(f : RestrictedDual) w, Subtype.ext ?_⟩
    change DirectSum.lof ℂ ℝ GradeDual w ((f : RestrictedDual) w) = (f : RestrictedDual)
    apply DFinsupp.ext
    intro u
    by_cases hu : u = w
    · subst u
      rw [DirectSum.lof_apply]
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hu]
      symm
      by_contra hNonzero
      have hf : Lᵈ (f : RestrictedDual) = (w : ℂ) • (f : RestrictedDual) :=
        Module.End.mem_eigenspace_iff.mp f.property
      exact hu (Complex.ofReal_injective (eigenvalue_eq_of_component_ne_zero hf hNonzero))

/-- The actual state energy and dual conformal zero mode have the same
algebraic point spectrum, with eigenvalues taken over ℂ. -/
theorem dual_conformal_has_eigenvector_iff (a : ℂ) :
    (∃ f : RestrictedDual, f ≠ 0 ∧ Lᵈ f = a • f) ↔
      ∃ v : State, v ≠ 0 ∧ totalLZero v = a • v := by
  constructor
  · rintro ⟨f, hf, he⟩
    have hComponent : ∃ w : ℝ, f w ≠ 0 := by
      by_contra! h
      apply hf
      apply DFinsupp.ext
      intro w
      rw [DFinsupp.zero_apply, h w]
    obtain ⟨w, hw⟩ := hComponent
    have ha : (w : ℂ) = a := eigenvalue_eq_of_component_ne_zero he hw
    have hGrade : ∃ v : ActualGrade w, v ≠ 0 := by
      by_contra! h
      apply hw
      apply LinearMap.ext
      intro v
      rw [h v, map_zero, LinearMap.zero_apply]
    obtain ⟨v, hv⟩ := hGrade
    refine ⟨(v : State), fun hz => hv (Subtype.ext hz), ?_⟩
    rw [← ha]
    exact Module.End.mem_eigenspace_iff.mp v.property
  · rintro ⟨v, hv, he⟩
    obtain ⟨p, d, ha⟩ := (totalLZero_eigenvalues a).mp ⟨v, hv, he⟩
    let w := totalWeight p d
    have hw : a = (w : ℂ) := ha
    have hvGrade : v ∈ totalLZero.eigenspace (w : ℂ) := by
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [hw] using he
    let x : ActualGrade w := ⟨v, hvGrade⟩
    have hx : x ≠ 0 := by
      intro hz
      apply hv
      simpa only [Submodule.coe_zero] using congrArg (fun y : ActualGrade w => (y : State)) hz
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
    have hg0 : g ≠ 0 := by
      intro hz
      exact hg (by rw [hz, LinearMap.zero_apply])
    refine ⟨DirectSum.lof ℂ ℝ GradeDual w g, ?_, ?_⟩
    · intro hz
      apply hg0
      have h := congrArg (fun f : RestrictedDual => f w) hz
      simpa only [DirectSum.lof_apply, DFinsupp.zero_apply] using h
    · rw [hw]
      exact dual_conformal_lof w g

/-- The exact dual point spectrum is 16/9 + n/3 for n in ℕ. -/
theorem dual_conformal_exact_eigenvalues (a : ℂ) :
    (∃ f : RestrictedDual, f ≠ 0 ∧ Lᵈ f = a • f) ↔
      ∃ n : ℕ, a = 16 / 9 + (n : ℂ) / 3 :=
  (dual_conformal_has_eigenvector_iff a).trans (totalLZero_exact_eigenvalues a)

theorem dual_conformal_eigenspace_finiteDimensional (w : ℝ) :
    FiniteDimensional ℂ (Module.End.eigenspace Lᵈ (w : ℂ)) := by
  letI : FiniteDimensional ℂ (ActualGrade w) := totalLZero_eigenspace_finiteDimensional (w : ℂ)
  exact (dualConformalEigenspaceEquiv w).finiteDimensional

theorem dual_conformal_eigenspace_finrank (w : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace Lᵈ (w : ℂ)) =
      Module.finrank ℂ (ActualGrade w) :=
  (dualConformalEigenspaceEquiv w).finrank_eq.symm.trans
    (Subspace.dual_finrank_eq (K := ℂ) (V := ActualGrade w))

theorem dual_conformal_ground_finrank :
    Module.finrank ℂ (Module.End.eigenspace Lᵈ (16 / 9 : ℂ)) = 1 := by
  have h := dual_conformal_eigenspace_finrank (16 / 9)
  have hCast : ((16 / 9 : ℝ) : ℂ) = (16 / 9 : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  change Module.finrank ℂ (Module.End.eigenspace Lᵈ ((16 / 9 : ℝ) : ℂ)) =
    Module.finrank ℂ (totalLZero.eigenspace ((16 / 9 : ℝ) : ℂ)) at h
  rw [hCast] at h
  exact h.trans totalLZero_vacuum_spectrum.2.2

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualConformalEnergy
