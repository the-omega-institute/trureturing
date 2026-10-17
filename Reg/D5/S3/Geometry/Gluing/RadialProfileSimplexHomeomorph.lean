import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph
import Reg.Support.DependentFamily

open D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph
noncomputable section
universe u

/-- The observed values are actual source profile values, not proof verdicts. -/
abbrev signature : Signature where
  Params := Fin 4
  State := _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ProfileRange
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ i u => sourceProfile i u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨23 / 48, by norm_num⟩) (fun e => nomatch e)

/-- The complete original theorem telescope; only the indicated profile observation varies. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {T : Type u} [TopologicalSpace T]
    (next : T × Fin 4 → T) (σ : T × Fin 4 → Equiv.Perm (Fin 4)),
    (∀ ρ i u, sourceProfile (ρ i) (permuteOpposite ρ i u) = R.readout () i u) ∧
    (∀ a b, seam next σ (taggedHomeomorph a) (taggedHomeomorph b) ↔ seam next σ a b) ∧
    (∀ a b, Relation.EqvGen (seam next σ) (taggedHomeomorph a) (taggedHomeomorph b) ↔
      Relation.EqvGen (seam next σ) a b)

private def endpoint : _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite 0 :=
  ⟨vertex 1, by norm_num [vertex, Pi.single_apply]⟩
private def center : _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite 0 :=
  ⟨⟨![0,1/3,1/3,1/3], by
    constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩, by norm_num⟩

private theorem endpoint_value : (sourceProfile 0 endpoint : ℝ) = 1 / 4 := by
  change 1 / (1 + (max (1 : ℝ) (max 0 0)) + max (2 * ((max (1 : ℝ) (max 0 0)) - (1 - (max (1 : ℝ) (max 0 0)) - (min (1 : ℝ) (min 0 0))))) (max (3 * ((1 - (max (1 : ℝ) (max 0 0)) - (min (1 : ℝ) (min 0 0))) - (min (1 : ℝ) (min 0 0)))) (4 * (min (1 : ℝ) (min 0 0))))) = 1/4
  norm_num
private theorem center_value : (sourceProfile 0 center : ℝ) = 3 / 8 := by
  change 1 / (1 + max (1/3 : ℝ) (max (1/3) (1/3)) +
    max (2 * (max (1/3 : ℝ) (max (1/3) (1/3)) -
      (1 - max (1/3 : ℝ) (max (1/3) (1/3)) - min (1/3 : ℝ) (min (1/3) (1/3)))))
      (max (3 * ((1 - max (1/3 : ℝ) (max (1/3) (1/3)) - min (1/3 : ℝ) (min (1/3) (1/3))) -
      min (1/3 : ℝ) (min (1/3) (1/3)))) (4 * min (1/3 : ℝ) (min (1/3) (1/3))))) = 3/8
  norm_num

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T := ULift.{u} Unit
  letI : TopologicalSpace T := ⊥
  have hv := (h (T := T) (fun x => x.1) (fun _ => Equiv.refl _)).1 (Equiv.refl _) 0 endpoint
  have hv' := congrArg (fun a : ProfileRange => (a : ℝ)) hv
  change (sourceProfile 0 endpoint : ℝ) = 23 / 48 at hv'
  rw [endpoint_value] at hv'
  norm_num at hv'

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_original_relation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨0, endpoint, center, ?_⟩
    intro h
    have hh := congrArg (fun a : ProfileRange => (a : ℝ)) h
    change (sourceProfile 0 endpoint : ℝ) = (sourceProfile 0 center : ℝ) at hh
    rw [endpoint_value, center_value] at hh
    norm_num at hh

/-- Typed source realization with an explicit selection of the source profile observation. -/
def source_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_original_relation.{u})
    (type_of% (realize signature (fun _ i u => sourceProfile i u) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.source_original_relation.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ i u => sourceProfile i u) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph,
    definition := none, coordinates := #[5],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


open private a_pos a_lt_half forwardRadius backwardRadius phi_vertex from
  D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph

abbrev genericSignature : Signature where
  Params := ∀ i, _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite i → ProfileRange
  State _ := Simplex
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def genericActual : Realization genericSignature :=
  realize genericSignature (fun _ α x => (phi α x).val)
    (fun e => nomatch e)
def genericRejected : Realization genericSignature :=
  realize genericSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev genericArena : Arena where
  signature := genericSignature
  Law R := ∀ (α : ∀ i, _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite i → ProfileRange) (hα : ∀ i, Continuous (α i)),
    (∀ i, radialHomeomorph α hα (vertex i) = vertex i) ∧
    (∀ i u r, radialHomeomorph α hα (ray i u r) = ray i u (forwardRadius (α i u) r)) ∧
    (∀ i u r, (radialHomeomorph α hα).symm (ray i u r) = ray i u (backwardRadius (α i u) r)) ∧
    (∀ x : Central, radialHomeomorph α hα x.val = x.val ∧
      (radialHomeomorph α hα).symm x.val = x.val) ∧
    (∀ x j, R.readout () α x j = 0 ↔ x.val j = 0) ∧
    (∀ x j, ((radialHomeomorph α hα).symm x).val j = 0 ↔ x.val j = 0) ∧
    (∀ (J : Set (Fin 4)) x, (∀ j ∈ J, (radialHomeomorph α hα x).val j = 0) ↔
      ∀ j ∈ J, x.val j = 0) ∧
    (∀ (β : ∀ i, _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite i → ProfileRange) (ρ : Equiv.Perm (Fin 4)),
      (∀ i u, β (ρ i) (permuteOpposite ρ i u) = α i u) →
      ∀ x, phi β (permute ρ x) = permute ρ (phi α x)) ∧
    (∀ (β : ∀ i, _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite i → ProfileRange) (ρ : Equiv.Perm (Fin 4)),
      (∀ i u, β (ρ i) (permuteOpposite ρ i u) = α i u) →
      ∀ x, psi β (permute ρ x) = permute ρ (psi α x)) ∧
    (∀ i u (r : Radius), (r : ℝ) ≤ 1 / 4 → ∀ j,
      |(phi α (ray i u r)).val j - (vertex i).val j| ≤ 23 / 12 * (r : ℝ) ∧
      |(psi α (ray i u r)).val j - (vertex i).val j| ≤ (r : ℝ)) ∧
    (∀ i u, radialHomeomorph α hα (ray i u ⟨1 / 4, by norm_num⟩) =
      ray i u ⟨α i u, ⟨(a_pos (α i u)).le, (a_lt_half (α i u)).le⟩⟩)

private def flatProfile : ∀ i, _root_.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.Opposite i → ProfileRange := fun _ _ => ⟨1/4, by norm_num⟩
private theorem flatContinuous (i : Fin 4) : Continuous (flatProfile i) := continuous_const

private theorem genericRejected_law : ¬ genericArena.Law genericRejected := by
  intro h
  have hz := (h flatProfile flatContinuous).2.2.2.2.1 (vertex 0) 0
  have hh := hz.mp rfl
  norm_num [vertex] at hh

def genericRegistration : Registration genericArena (genericArena.Law genericActual) where
  actual := genericActual
  bridge := Iff.rfl
  variation := ⟨radial_homeomorph_spec, genericRejected, genericRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨genericRejected, ?_, rfl, genericRejected_law⟩
      intro j h; exact (h (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨flatProfile, vertex 0, vertex 1, ?_⟩
    intro h
    have hh := congrFun h 0
    change (phi flatProfile (vertex 0)).val 0 = (phi flatProfile (vertex 1)).val 0 at hh
    rw [phi_vertex, phi_vertex] at hh
    norm_num [vertex, Pi.single_apply] at hh

def generic_source_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_homeomorph_spec)
    (type_of% (realize genericSignature
      (fun _ α x => (phi α x).val) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.radial_homeomorph_spec.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph.genericRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨genericArena⟩, objectArena := .source ⟨genericArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source genericArena ⟨genericRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize genericSignature
    (fun _ α x => (phi α x).val) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms genericRegistration

#print axioms registration
end
end Reg.D5.S3.Geometry.Gluing.RadialProfileSimplexHomeomorph
