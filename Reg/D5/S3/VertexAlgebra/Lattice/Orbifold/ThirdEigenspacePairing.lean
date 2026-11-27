import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the complex Gram form. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle (zeta zeta_primitive)

noncomputable section

private abbrev Cartan := Fin 48 → ℂ

private theorem root_primitive : IsPrimitiveRoot (zeta : ℂ) 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr zeta_primitive

namespace Invariance

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Cartan (fun _ => Cartan) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ y x => p48qForm (p48qAction x) (p48qAction y)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x y : Cartan, R.readout () y x = p48qForm x y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have at_zero := h 0 0
  change (1 : ℂ) = p48qForm 0 0 at at_zero
  simp at at_zero

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  let x : Cartan := fun _ => 1
  have hx : x ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨y, hy⟩ : ∃ y : Cartan, p48qForm x y ≠ 0 := by
    by_contra! h
    exact hx (p48qForm_nondegenerate.1 x h)
  refine ⟨y, x, 0, ?_⟩
  change p48qForm (p48qAction x) (p48qAction y) ≠ p48qForm (p48qAction 0) (p48qAction y)
  simpa only [p48qForm_invariant, map_zero, LinearMap.zero_apply] using hy

def family : Registration arena (type_of% p48qForm_invariant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨p48qForm_invariant, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    p48qForm_invariant (Realization signature) Cartan Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing.p48qForm_invariant.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing.Invariance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Invariance

namespace DualBasis

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Cartan) (fun _ => Cartan →ₗ[ℂ] ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x => p48qForm x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (i j : Fin 16),
    R.readout () () (p48qBasis hζ i) (p48qOppositeBasis hζ j) = if i = j then 1 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have diagonal := h root_primitive 0 0
  change (0 : ℂ) = (if (0 : Fin 16) = 0 then 1 else 0) at diagonal
  simp at diagonal

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), p48qBasis root_primitive 0, 0, ?_⟩
  intro h
  have at_dual := DFunLike.congr_fun h (p48qOppositeBasis root_primitive 0 : Cartan)
  change p48qForm (p48qBasis root_primitive 0) (p48qOppositeBasis root_primitive 0) =
    p48qForm 0 (p48qOppositeBasis root_primitive 0) at at_dual
  simp [p48q_pair_bases] at at_dual

def family : Registration arena (type_of% @p48q_pair_bases) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@p48q_pair_bases, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@p48q_pair_bases) (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing.p48q_pair_bases.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing.DualBasis.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DualBasis

end

end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
