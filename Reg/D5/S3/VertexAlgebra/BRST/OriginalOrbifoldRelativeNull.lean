import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull

/-! Observe the range of the native restricted BRST differential in its exactness law. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldCriticalMatter (hyperbolicData)
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldRelativeMassShell
  (relativeMassShell differential hyperbolic_chargeEnergy)
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldRelativeNull
  (differential_exact differential_on_basis shellBasis top bottom middle ShellIndex
    coordinateDifferential coordinateDifferential_exact)
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality (Charge)
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy (chargeEnergy)

namespace Reg.D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Charge hyperbolicData)
    (fun a => Module.End ℂ (relativeMassShell a))
    (fun a => Submodule ℂ (relativeMassShell a))

def actual : Realization signature :=
  realize signature (fun _ _ d => LinearMap.range d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Charge hyperbolicData) (_ha : chargeEnergy hyperbolicData a = 0)
    (_hne : a ≠ 0),
    R.readout () a (differential a) = LinearMap.ker (differential a)

private def witnessCharge : Charge hyperbolicData := ![1, 0]

private theorem witness_null : chargeEnergy hyperbolicData witnessCharge = 0 := by
  rw [hyperbolic_chargeEnergy]
  exact mul_zero (1 : ℤ)

private theorem witness_nonzero : witnessCharge ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Fin 2)
  change (1 : ℤ) = 0 at hzero
  exact one_ne_zero hzero

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have heq : ⊥ = LinearMap.ker (differential witnessCharge) :=
    law witnessCharge witness_null witness_nonzero
  have hclosed : shellBasis witnessCharge witness_null top ∈
      LinearMap.ker (differential witnessCharge) :=
    LinearMap.mem_ker.mpr (differential_on_basis witnessCharge witness_null).2.2.2
  rw [← heq, Submodule.mem_bot] at hclosed
  exact (shellBasis witnessCharge witness_null).ne_zero top hclosed

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witnessCharge, 0, LinearMap.id, ?_⟩
  intro heq
  change LinearMap.range (0 : Module.End ℂ (relativeMassShell witnessCharge)) =
    LinearMap.range (LinearMap.id : Module.End ℂ (relativeMassShell witnessCharge)) at heq
  have hmem : shellBasis witnessCharge witness_null top ∈
      LinearMap.range (LinearMap.id : Module.End ℂ (relativeMassShell witnessCharge)) :=
    ⟨shellBasis witnessCharge witness_null top, rfl⟩
  rw [← heq, LinearMap.range_zero, Submodule.mem_bot] at hmem
  exact (shellBasis witnessCharge witness_null).ne_zero top hmem

def family : Registration arena (type_of% (@differential_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨differential_exact, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@differential_exact) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.VertexAlgebra.OriginalOrbifoldRelativeNull.differential_exact
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => LinearMap.range d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace Coordinate

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2 → ℤ)
    (fun _ => Module.End ℂ (ShellIndex → ℂ))
    (fun _ => Submodule ℂ (ShellIndex → ℂ))

def actual : Realization signature :=
  realize signature (fun _ _ d => LinearMap.range d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Fin 2 → ℤ) (_ha : a 0 * a 1 = 0) (_hne : a ≠ 0),
    R.readout () a (coordinateDifferential a) = LinearMap.ker (coordinateDifferential a)

private def witnessCharge : Fin 2 → ℤ := ![1, 0]

private theorem witness_nonzero : witnessCharge ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h (0 : Fin 2) : (1 : ℤ) = 0)

private def topVector : ShellIndex → ℂ := Pi.single top 1

private theorem topVector_ne_zero : topVector ≠ 0 := by
  intro h
  have ht := congrFun h top
  simpa [topVector] using ht

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have heq : ⊥ = LinearMap.ker (coordinateDifferential witnessCharge) :=
    law witnessCharge (mul_zero (1 : ℤ)) witness_nonzero
  have hclosed : topVector ∈ LinearMap.ker (coordinateDifferential witnessCharge) := by
    apply LinearMap.mem_ker.mpr
    funext k
    rcases k with (_ | (i | _)) <;>
      simp [coordinateDifferential, topVector, Pi.single_apply, bottom, middle, top]
  rw [← heq, Submodule.mem_bot] at hclosed
  exact topVector_ne_zero hclosed

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨witnessCharge, 0, LinearMap.id, ?_⟩
  intro heq
  change LinearMap.range (0 : Module.End ℂ (ShellIndex → ℂ)) =
    LinearMap.range (LinearMap.id : Module.End ℂ (ShellIndex → ℂ)) at heq
  have hmem : topVector ∈ LinearMap.range (LinearMap.id : Module.End ℂ (ShellIndex → ℂ)) :=
    ⟨topVector, rfl⟩
  rw [← heq, LinearMap.range_zero, Submodule.mem_bot] at hmem
  exact topVector_ne_zero hmem

def family : Registration arena (type_of% (@coordinateDifferential_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coordinateDifferential_exact, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coordinateDifferential_exact) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.VertexAlgebra.OriginalOrbifoldRelativeNull.coordinateDifferential_exact
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull.Coordinate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => LinearMap.range d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Coordinate

end Reg.D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
