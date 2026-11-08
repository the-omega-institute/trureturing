import D5.S3.Quantum.SpinFactor.OriginalUnitSupport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original-carrier reconstruction of the support-obstruction source.
These bridges do not supply a lawful enrolled readout, whole-family variation,
sensitivity or observational-dependence evidence. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.SpinFactor.OriginalUnitSupport

open _root_.D5.S3.Quantum.SpinFactor.OriginalUnitSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure RawInputs where
  E : Type u
  [normed : NormedAddCommGroup E]
  [space : NormedSpace ℝ E]
  S : E →ₗ[ℝ] E →ₗ[ℝ] E
  D : E → E → E
  P : Set (E →ₗ[ℝ] ℝ)
  positive : P2 S D P
  balance : PB S D P
  comm : ∀ x y, S x y = S y x
  unit : E
  unitLaw : ∀ x, S unit x = x
  squareNorm : ∀ x, ‖S x x‖ = ‖x‖ ^ 2
  separates : ∀ x, (∀ α ∈ P, α x = 0) → x = 0

attribute [instance] RawInputs.normed RawInputs.space

structure RawState (p : RawInputs.{u}) where
  mu : ℝ
  b : p.E
  alpha : p.E →ₗ[ℝ] ℝ
  member : alpha ∈ p.P
  normalized : alpha p.unit = 1
  contractive : ∀ x, |alpha x| ≤ ‖x‖
  Z : ℝ
  nonzero : Z ≠ 0
  reads : alpha (p.D (mu • p.unit) b) = Z
  norms : |Z| = ‖p.D (mu • p.unit) b‖

abbrev rawSignature : Signature where
  Params := RawInputs.{u}
  State := RawState
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rawActual : Realization rawSignature.{u} :=
  realize rawSignature
    (fun role p z => if role then z.alpha (p.S z.b (p.D (z.mu • p.unit) z.b))
      else z.alpha z.b)
    (fun e => nomatch e)

abbrev rawArena : Arena where
  signature := rawSignature.{u}
  Law R := ∀ (p : RawInputs.{u}) (z : RawState p),
    R.readout true p z = 0 ∧ R.readout false p z = 0

abbrev rawSourceScope : Prop := type_of% (@support_unit_obstruction.{u})

theorem raw_source_bridge : rawSourceScope.{u} ↔ rawArena.{u}.Law rawActual := by
  constructor
  · intro h p z
    exact h p.S p.D p.P p.positive p.balance p.comm p.unit p.unitLaw
      p.squareNorm p.separates z.mu z.b z.alpha z.member z.normalized
      z.contractive z.Z z.nonzero z.reads z.norms
  · intro h E normed space S D P hP hPB hc unit hu hsq hsep mu b alpha
      hmember hnormalized hcontractive Z hnonzero hreads hnorms
    exact h ⟨E, S, D, P, hP, hPB, hc, unit, hu, hsq, hsep⟩
      ⟨mu, b, alpha, hmember, hnormalized, hcontractive, Z, hnonzero, hreads, hnorms⟩

theorem raw_actual_positive : rawArena.{u}.Law rawActual :=
  raw_source_bridge.mp (@support_unit_obstruction.{u})

end Reg.D5.S3.Quantum.SpinFactor.OriginalUnitSupport

namespace Reg.D5.S3.Quantum.SpinFactor.OriginalUnitSupport

open _root_.D5.S3.Quantum.SpinFactor.OriginalUnitSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure BoundaryInputs where
  base : RawInputs.{u}
  cone : Set base.E
  exactCone : ∀ x, x ∈ cone ↔ ∀ α ∈ base.P, 0 ≤ α x

structure BoundaryState (p : BoundaryInputs.{u}) where
  mu : ℝ
  b : p.base.E
  beta : p.base.E →ₗ[ℝ] ℝ
  positive : ∀ x ∈ p.cone, 0 ≤ beta x
  normalized : beta p.base.unit = 1
  contractive : ∀ x, |beta x| ≤ ‖x‖
  Z : ℝ
  nonzero : Z ≠ 0
  reads : beta (p.base.D (mu • p.base.unit) b) = Z
  norms : |Z| = ‖p.base.D (mu • p.base.unit) b‖
  t : ℝ

abbrev boundarySignature : Signature where
  Params := BoundaryInputs.{u}
  State := BoundaryState
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def boundaryActual : Realization boundarySignature.{u} :=
  realize boundarySignature (fun role p z =>
    if role then z.mu else ‖z.b - z.t • p.base.unit‖) (fun e => nomatch e)

abbrev boundaryArena : Arena where
  signature := boundarySignature.{u}
  Law R := ∀ (p : BoundaryInputs.{u}) (z : BoundaryState p),
    R.readout true p z ≠ 0 ∧ |z.t| < R.readout false p z

abbrev boundarySourceScope : Prop := type_of% (@positive_support_unit_boundary.{u})

theorem boundary_source_bridge : boundarySourceScope.{u} ↔
    boundaryArena.{u}.Law boundaryActual := by
  constructor
  · intro h p z
    have hh := h p.base.S p.base.D p.base.P p.base.positive p.base.balance
      p.base.comm p.base.unit p.base.unitLaw p.base.squareNorm p.base.separates
      p.cone p.exactCone z.mu z.b z.beta z.positive z.normalized z.contractive
      z.Z z.nonzero z.reads z.norms
    exact ⟨hh.1, hh.2 z.t⟩
  · intro h E normed space S D P hP hPB hc unit hu hsq hsep C hexact
      mu b beta hpositive hnormalized hcontractive Z hnonzero hreads hnorms
    let p : BoundaryInputs := ⟨⟨E, S, D, P, hP, hPB, hc, unit, hu, hsq, hsep⟩, C, hexact⟩
    have ht (t : ℝ) := h p
      ⟨mu, b, beta, hpositive, hnormalized, hcontractive, Z, hnonzero, hreads, hnorms, t⟩
    exact ⟨(ht 0).1, fun t => (ht t).2⟩

theorem boundary_actual_positive : boundaryArena.{u}.Law boundaryActual :=
  boundary_source_bridge.mp (@positive_support_unit_boundary.{u})

end Reg.D5.S3.Quantum.SpinFactor.OriginalUnitSupport
