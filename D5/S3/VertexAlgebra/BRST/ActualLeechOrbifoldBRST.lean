/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual bosonic-string BRST and its nonzero-energy contraction. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! BRST on the actual Leech orbifold, the hyperbolic lattice field and the
native bc ghost Fock space. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldCriticalMatter (Matter matter)
open D5.S3.Quantum.Fermionic

abbrev ComplexState := VirasoroBRST.State Matter

abbrev Q : Module.End ℂ ComplexState := VirasoroBRST.Q matter
abbrev E : Module.End ℂ ComplexState := VirasoroBRST.Ltotal matter 0
abbrev b0 : Module.End ℂ ComplexState := VirasoroBRST.ghostB matter 0

/-- The string differential on the original tensor factors is nilpotent. -/
theorem Q_squared : Q ^ 2 = 0 := by
  have h := VirasoroBRST.square_anomaly matter
  change Q ^ 2 = ((26 - (26 : ℂ)) / 26) • VirasoroBRST.ghostSquareAnomaly matter at h
  simpa only [sub_self, zero_div, zero_smul] using h

private theorem Q_commutes_energy : Q * E = E * Q := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (VirasoroBRST.Q_Ltotal matter 0) x
  simp only [show matter.centralCharge = (26 : ℂ) from rfl, sub_self, zero_div,
    zero_mul, zero_smul, LinearMap.zero_apply] at h
  exact sub_eq_zero.mp h

private theorem b0_square : b0 * b0 = 0 := by
  let b := BcGhostFock.b 0
  have twice : (2 : ℂ) • (b * b) = 0 := by
    rw [two_smul]
    exact BcGhostFock.ghost_b_car 0 0
  have hb : b * b = 0 := (smul_eq_zero.mp twice).resolve_left (by norm_num)
  let lift := Module.End.lTensorAlgHom ℂ CountableOccupationFock.Fock Matter
  change lift b * lift b = 0
  simpa only [map_mul, map_zero] using congrArg lift hb

private theorem b0_commutes_energy : b0 * E = E * b0 := by
  have ward : Q * b0 + b0 * Q = E := VirasoroBRST.Q_ward_b matter 0
  rw [← ward]
  calc
    b0 * (Q * b0 + b0 * Q) = b0 * Q * b0 + (b0 * b0) * Q := by noncomm_ring
    _ = b0 * Q * b0 + Q * (b0 * b0) := by rw [b0_square, zero_mul, mul_zero]
    _ = (Q * b0 + b0 * Q) * b0 := by noncomm_ring

/-- The actual total-energy eigenspace on the full string-state carrier. -/
abbrev EnergySpace (μ : ℂ) := E.eigenspace μ

private theorem preserves_energy {A : Module.End ℂ ComplexState} (commutes : A * E = E * A)
    (μ : ℂ) {x : ComplexState} (hx : x ∈ EnergySpace μ) :
    A x ∈ EnergySpace μ := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h := LinearMap.congr_fun commutes x
  change A (E x) = E (A x) at h
  rw [← h, Module.End.mem_eigenspace_iff.mp hx, map_smul]

/-- Restrict the string differential to the actual total-energy eigenspace. -/
def differential (μ : ℂ) : Module.End ℂ (EnergySpace μ) :=
  Q.restrict (fun _ hx => preserves_energy Q_commutes_energy μ hx)

/-- Restrict the zero ghost mode and rescale by inverse total energy. -/
def homotopy (μ : ℂ) : Module.End ℂ (EnergySpace μ) :=
  μ⁻¹ • b0.restrict (fun _ hx => preserves_energy b0_commutes_energy μ hx)

/-- Every energy eigenspace is a BRST complex. -/
theorem differential_squared (μ : ℂ) : differential μ ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q (Q x.val) = 0
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun Q_squared x.val

/-- In nonzero total energy, the actual zero ghost mode contracts the BRST complex. -/
theorem contraction (μ : ℂ) (hμ : μ ≠ 0) :
    differential μ * homotopy μ + homotopy μ * differential μ = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q (μ⁻¹ • b0 x.val) + μ⁻¹ • b0 (Q x.val) = x.val
  have ward : Q (b0 x.val) + b0 (Q x.val) = E x.val :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter 0) x.val
  rw [map_smul, ← smul_add, ward, Module.End.mem_eigenspace_iff.mp x.property,
    smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Every closed state of nonzero total energy has the specified BRST primitive. -/
theorem exact_of_closed (μ : ℂ) (hμ : μ ≠ 0) (x : ComplexState)
    (hx : E x = μ • x) (closed : Q x = 0) :
    Q (μ⁻¹ • b0 x) = x := by
  let y : EnergySpace μ := ⟨x, Module.End.mem_eigenspace_iff.mpr hx⟩
  have h := congrArg Subtype.val (LinearMap.congr_fun (contraction μ hμ) y)
  change Q (μ⁻¹ • b0 x) + μ⁻¹ • b0 (Q x) = x at h
  simpa only [closed, map_zero, smul_zero, add_zero] using h

#print axioms Q_squared
#print axioms differential_squared
#print axioms contraction
#print axioms exact_of_closed

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
