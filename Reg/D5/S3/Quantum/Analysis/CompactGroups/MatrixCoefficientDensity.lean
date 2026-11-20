import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity
import Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
import Reg.Support.DependentFamily

/-! Source-bound audit of the density of the complex span of the matrix coefficients of
continuous finite-dimensional unitary representations in the continuous functions on a compact
group. -/

namespace Reg.D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity

open _root_.D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
  (Two twoTop twoDiscrete twoTopGroup twoCompact Circle taut negOne)

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-! ## `dense_span_unitary_coefficients`: the matrix coefficient at a group element -/
namespace Coefficient

/-- A compact-group coefficient datum: a group with its topology, a continuous unitary
representation of dimension `n`, and a pair of matrix indices. -/
structure Parameters : Type (u + 1) where
  G : Type u
  [group : Group G]
  [topology : TopologicalSpace G]
  n : ℕ
  ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ
  i : Fin n
  j : Fin n

/-- The entry `(ρ g) i j` of the value of a continuous unitary representation at a group
element. -/
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p g => letI := p.group; letI := p.topology;
    (p.ρ g : Matrix (Fin p.n) (Fin p.n) ℂ) p.i p.j)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete group, instance and conclusion telescope of
`dense_span_unitary_coefficients`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {G : Type u} [iG : Group G] [tG : TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G],
    Dense (Submodule.span ℂ {f : C(G, ℂ) | ∃ (n : ℕ)
      (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n),
        ∀ g, f g = r.readout () (@Parameters.mk G iG tG n ρ i j) g} : Set C(G, ℂ))

/-- If every coefficient were read as `0`, the span would be the zero subspace, which is not
dense in the continuous functions on the two-element discrete group. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let _ := twoTop.{u}
  have := twoDiscrete.{u}
  have := twoTopGroup.{u}
  have := twoCompact.{u}
  have hd := h (G := Two.{u})
  have h0 : Dense ({0} : Set C(Two.{u}, ℂ)) := by
    refine hd.mono fun f hf => ?_
    have hbot := (Submodule.span_le (p := (⊥ : Submodule ℂ C(Two.{u}, ℂ)))).2 ?_ hf
    · exact (Submodule.mem_bot ℂ).1 hbot
    · rintro f ⟨n, ρ, i, j, hf⟩
      rw [SetLike.mem_coe, Submodule.mem_bot]
      ext g
      simpa [rejected, realize] using hf g
  have h1 : (1 : C(Two.{u}, ℂ)) ∈ ({0} : Set C(Two.{u}, ℂ)) := by
    rw [← closure_singleton, h0.closure_eq]
    exact Set.mem_univ _
  have h2 := congrArg (fun f : C(Two.{u}, ℂ) => f 1) (Set.mem_singleton_iff.1 h1)
  simp at h2

/-- The tautological representation of `U(1)` has coefficient `1` at the identity and `-1` at
the matrix `-1`. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨@Parameters.mk Circle.{u} _ _ 1 taut 0 0, 1, ⟨negOne⟩, ?_⟩
  change ((taut.{u} 1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0) ≠
    ((taut.{u} ⟨negOne⟩ : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
  rw [map_one]
  change ((1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0) ≠ ((-1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
  norm_num

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @dense_span_unitary_coefficients.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dense_span_unitary_coefficients.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Coefficient

def dense_span_unitary_coefficients_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dense_span_unitary_coefficients.{u}) (Realization Coefficient.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity.dense_span_unitary_coefficients_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity.Coefficient.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Coefficient.arena.{u}⟩
  objectArena := .source ⟨Coefficient.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Coefficient.arena.{u} ⟨Coefficient.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Coefficient.signature.{u}
    (fun _ p g => letI := p.group; letI := p.topology;
      (p.ρ g : Matrix (Fin p.n) (Fin p.n) ℂ) p.i p.j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity
    definition := none
    coordinates := #[0, 6, 7, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.CompactGroups.MatrixCoefficientDensity
