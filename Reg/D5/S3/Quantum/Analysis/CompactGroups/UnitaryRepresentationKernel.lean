import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
import Reg.Support.DependentFamily

/-! Source-bound audit of the theorem that every neighbourhood of the identity of a compact group
contains the kernel of a continuous finite-dimensional unitary representation. -/

namespace Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel

open _root_.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- The two-element group `ℤ/2`, written multiplicatively, in universe `u`. -/
abbrev Two := ULift.{u} (Multiplicative (ZMod 2))

/-- The discrete topology on the two-element group. -/
abbrev twoTop : TopologicalSpace Two.{u} := ⊥

/-- The two-element group with the discrete topology is discrete. -/
theorem twoDiscrete : @DiscreteTopology Two.{u} twoTop :=
  @DiscreteTopology.mk Two.{u} twoTop rfl

/-- The two-element group with the discrete topology is a topological group. -/
theorem twoTopGroup : @IsTopologicalGroup Two.{u} twoTop _ :=
  letI := twoTop.{u}
  haveI := twoDiscrete.{u}
  { continuous_mul := continuous_of_discreteTopology
    continuous_inv := continuous_of_discreteTopology }

/-- The two-element group with the discrete topology is compact. -/
theorem twoCompact : @CompactSpace Two.{u} twoTop :=
  letI := twoTop.{u}
  Finite.compactSpace

/-- The unitary `1 × 1` matrix `-1`. -/
def negOne : Matrix.unitaryGroup (Fin 1) ℂ :=
  ⟨-1, by simp [Matrix.mem_unitaryGroup_iff]⟩

/-- The matrix `-1` is not the identity. -/
theorem negOne_ne_one : negOne ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.unitaryGroup (Fin 1) ℂ => (A : Matrix (Fin 1) (Fin 1) ℂ) 0 0) h
  norm_num [negOne] at this

/-- The circle group `U(1)` lifted to universe `u`, with its tautological representation. -/
abbrev Circle := ULift.{u} (Matrix.unitaryGroup (Fin 1) ℂ)

/-- The tautological representation of `U(1)` on `ℂ`. -/
def taut : Circle.{u} →ₜ* Matrix.unitaryGroup (Fin 1) ℂ :=
  { (MulEquiv.ulift : Circle.{u} ≃* _).toMonoidHom with
    continuous_toFun := continuous_uliftDown }

/-! ## `exists_unitaryRep_ker_subset`: the value of the representation at a group element -/
namespace Kernel

/-- The value `ρ g` of a continuous unitary representation at a group element. -/
abbrev signature : Signature where
  Params := Σ G : Type u, Σ _ : Group G, Σ _ : TopologicalSpace G, Σ n : ℕ,
    G →ₜ* Matrix.unitaryGroup (Fin n) ℂ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix.unitaryGroup (Fin p.2.2.2.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p g => letI := p.2.1; letI := p.2.2.1; p.2.2.2.2 g) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the complete group, instance, neighbourhood and conclusion telescope of
`exists_unitaryRep_ker_subset`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {G : Type u} [iG : Group G] [tG : TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {U : Set G}, U ∈ 𝓝 (1 : G) →
    ∃ (n : ℕ) (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ),
      ∀ g, r.readout () ⟨G, iG, tG, n, ρ⟩ g = 1 → g ∈ U

/-- If every representation were read as the identity, every element of the two-element
discrete group would lie in the neighbourhood `{1}`. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let _ := twoTop.{u}
  have := twoDiscrete.{u}
  have := twoTopGroup.{u}
  have := twoCompact.{u}
  obtain ⟨n, ρ, hρ⟩ := h (G := Two.{u}) (U := {1}) ((isOpen_discrete _).mem_nhds rfl)
  have hne : (⟨Multiplicative.ofAdd 1⟩ : Two.{u}) ≠ 1 := by decide
  exact hne (hρ ⟨Multiplicative.ofAdd 1⟩ rfl)

/-- The tautological representation of `U(1)` separates `1` from `-1`. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Circle.{u}, inferInstance, inferInstance, 1, taut⟩, 1, ⟨negOne⟩, ?_⟩
  change taut.{u} 1 ≠ taut.{u} ⟨negOne⟩
  intro h
  exact negOne_ne_one h.symm

def source_registration :
    Registration arena.{u} (type_of% @exists_unitaryRep_ker_subset.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unitaryRep_ker_subset.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Kernel

def exists_unitaryRep_ker_subset_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_unitaryRep_ker_subset.{u}) (Realization Kernel.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel.exists_unitaryRep_ker_subset_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel.Kernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Kernel.arena.{u}⟩
  objectArena := .source ⟨Kernel.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Kernel.arena.{u} ⟨Kernel.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Kernel.signature.{u}
    (fun _ p g => letI := p.2.1; letI := p.2.2.1; p.2.2.2.2 g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
    definition := none
    coordinates := #[0, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "domain", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
