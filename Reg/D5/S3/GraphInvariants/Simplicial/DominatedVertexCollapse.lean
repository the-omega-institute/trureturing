import LeanInformationAuditInterface.Contract.Registration
import D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse
import Reg.Support.DependentFamily

namespace Reg.D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse

open _root_.D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

/-- The ambient type and both vertices are source parameters. -/
abbrev Params := Σ ι : Type u, Σ _v : ι, ι

abbrev signature : Signature :=
  { Params := Params
    State := fun p => PreAbstractSimplicialComplex p.1
    Role := Unit
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ p => PreAbstractSimplicialComplex p.1
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ p K => @deletion p.1 K {p.2.1})
    (fun e => nomatch e)

/-- The single-vertex complex used to test an incorrect deletion endpoint. -/
def oneVertex {ι : Type u} (w : ι) : PreAbstractSimplicialComplex ι where
  faces := {{w}}
  isRelLowerSet_faces := by
    rintro A rfl
    refine ⟨Finset.singleton_nonempty w, fun B hB hne => ?_⟩
    exact (Finset.subset_singleton_iff.mp hB).resolve_left hne.ne_empty

def rejected : Realization signature :=
  realize signature (fun _ p _ => oneVertex p.2.2) (fun e => nomatch e)

/-- Only the actual vertex-deletion endpoint is replaced; all premises are retained. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [inst : DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (_hfin : K.faces.Finite)
    (v w : ι) (_hvw : v ≠ w)
    (_hdom : ∀ A : Finset ι, A ∈ K → v ∈ A → insert w A ∈ K),
      @CollapsesTo ι K (R.readout () ⟨ι, v, w⟩ K)

def statement : Prop := ∀ {ι : Type u} [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (_hfin : K.faces.Finite)
    (v w : ι) (_hvw : v ≠ w)
    (_hdom : ∀ A : Finset ι, A ∈ K → v ∈ A → insert w A ∈ K),
    CollapsesTo K (deletion K {v})

/-- Every endpoint of a collapse is a subcomplex of its starting complex. -/
theorem collapse_le {ι : Type u}
    {K L : PreAbstractSimplicialComplex ι} (h : CollapsesTo K L) : L ≤ K := by
  induction h with
  | refl => exact le_rfl
  | @tail L M h hstep ih =>
    obtain ⟨σ, τ, _, rfl⟩ := hstep
    exact fun _ hA => ih hA.1

theorem rejected_law : ¬ arena.Law (rejected : Realization signature.{u}) := by
  intro h
  let ι := ULift.{u} Bool
  let v : ι := ⟨false⟩
  let w : ι := ⟨true⟩
  have hc := @h ι inferInstance ⊥ Set.finite_empty v w
    (by decide) (fun _ hA _ => hA.elim)
  have hp : ({w} : Finset ι) ∈ (⊥ : PreAbstractSimplicialComplex ι) :=
    collapse_le hc (show ({w} : Finset ι) ∈ oneVertex w from rfl)
  exact hp

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let ι := ULift.{u} Bool
  let v : ι := ⟨false⟩
  let w : ι := ⟨true⟩
  refine ⟨⟨ι, v, w⟩, ⊥, oneVertex w, ?_⟩
  intro heq
  change @deletion ι ⊥ {v} =
    @deletion ι (oneVertex w) {v} at heq
  have hw : ({w} : Finset ι) ∈ @deletion ι (oneVertex w) {v} :=
    ⟨rfl, by
      intro hs
      have he : v = w := Finset.mem_singleton.mp (Finset.singleton_subset_iff.mp hs)
      cases congrArg ULift.down he⟩
  have hp : ({w} : Finset ι) ∈ @deletion ι ⊥ {v} := heq ▸ hw
  exact hp.1

def registration : Registration arena.{u} statement where
  actual := actual
  bridge := by
    constructor
    · intro h ι inst K hfin v w hvw hdom
      exact @h ι inst K hfin v w hvw hdom
    · intro h ι inst K hfin v w hvw hdom
      exact @h ι inst K hfin v w hvw hdom
  variation := ⟨(by
    intro ι inst K hfin v w hvw hdom
    exact @collapsesTo_deletion_of_vertex_domination ι inst K hfin v w hvw hdom),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@collapsesTo_deletion_of_vertex_domination.{u})
    (type_of% (realize signature.{u}
      (fun _ p K => @deletion p.1 K {p.2.1}) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse
      "collapsesTo_deletion_of_vertex_domination") "__information_unit",
  realizationName := `Reg.D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p K => @deletion p.1 K {p.2.1}) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse,
    definition := none,
    coordinates := #[0, 4, 5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.GraphInvariants.Simplicial.DominatedVertexCollapse
