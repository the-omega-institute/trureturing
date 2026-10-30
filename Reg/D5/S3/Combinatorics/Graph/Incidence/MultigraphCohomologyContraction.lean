import D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open _root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphContraction
open _root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction
noncomputable section
open Classical
universe u v

abbrev survivorSignature : Signature where
  Params := Σ E : Type v, E
  State p := Surviving p.2 → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Surviving p.2 → ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def survivorActual : Realization survivorSignature :=
  realize survivorSignature (fun _ _ x y => x = y) (fun a => nomatch a)
def survivorRejected : Realization survivorSignature :=
  realize survivorSignature (fun _ _ _ _ => False) (fun a => nomatch a)

theorem survivorDependence : ObservationalDependence survivorSignature.{v} survivorActual := by
  intro i
  let E := ULift.{v} (Fin 2)
  let e : E := ⟨0⟩
  let f : Surviving e := ⟨⟨1⟩, by simp [e]⟩
  refine ⟨⟨E, e⟩, 0, fun _ => 1, ?_⟩
  intro he
  have hx : (fun _ : Surviving e => (1 : ℚ)) = 0 := congrFun he 0 ▸ rfl
  have hf := congrFun hx f
  norm_num at hf

abbrev edgeSignature : Signature where
  Params := Type v
  State E := E → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := (E → ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def edgeActual : Realization edgeSignature :=
  realize edgeSignature (fun _ _ x y => x = y) (fun a => nomatch a)
def edgeRejected : Realization edgeSignature :=
  realize edgeSignature (fun _ _ _ _ => False) (fun a => nomatch a)

theorem edgeDependence : ObservationalDependence edgeSignature.{v} edgeActual := by
  intro i
  let E := ULift.{v} Unit
  refine ⟨E, 0, fun _ => 1, ?_⟩
  intro he
  have hx : (fun _ : E => (1 : ℚ)) = 0 := congrFun he 0 ▸ rfl
  have hf := congrFun hx ⟨()⟩
  norm_num at hf

abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarActual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun a => nomatch a)
def scalarRejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun a => nomatch a)

theorem scalarDependence : ObservationalDependence scalarSignature scalarActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hx : (1 : ℚ) = 0 := congrFun he 0 ▸ rfl
  norm_num at hx

abbrev graphSignature : Signature where
  Params := Σ V : Type u, Σ E : Type v, DirectedMultigraph V E
  State p := Cohomology p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cohomology p.2.2 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def graphActual : Realization graphSignature :=
  realize graphSignature (fun _ _ x y => x = y) (fun a => nomatch a)
def graphRejected : Realization graphSignature :=
  realize graphSignature (fun _ _ _ _ => False) (fun a => nomatch a)

theorem graphDependence : ObservationalDependence graphSignature.{u,v} graphActual := by
  intro i
  let V := ULift.{u} Unit
  let E := ULift.{v} Unit
  let G : DirectedMultigraph V E := ⟨fun _ => ⟨()⟩, fun _ => ⟨()⟩⟩
  let q := (coboundary G).range.mkQ
  refine ⟨⟨V, E, G⟩, q 0, q (fun _ => 1), ?_⟩
  intro he
  have hx : q (fun _ => 1) = q 0 := congrFun he (q 0) ▸ rfl
  have hm := (Submodule.Quotient.eq (coboundary G).range).mp hx
  obtain ⟨k, hk⟩ := hm
  have hf := congrFun hk (⟨()⟩ : E)
  change k ⟨()⟩ - k ⟨()⟩ = (1 : ℚ) - 0 at hf
  linarith

private def testGraph : DirectedMultigraph (ULift.{u} Bool) (ULift.{v} Unit) :=
  ⟨fun _ => ⟨false⟩, fun _ => ⟨true⟩⟩
private theorem testNonloop : testGraph.{u,v}.source ⟨()⟩ ≠ testGraph.target ⟨()⟩ := by
  intro he
  have := congrArg ULift.down he
  cases this

@[reducible] def evacuate_coboundaryArena : Arena where
  signature := survivorSignature.{v}
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (k : V → ℚ),
    R.readout () ⟨E, e⟩ (evacuate G e (coboundary G k))
      (coboundary (contract G e h) (fun w => k w.val))

theorem evacuate_coboundaryPositive : evacuate_coboundaryArena.Law survivorActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_coboundary.{u,v}
theorem evacuate_coboundaryNegative : ¬ evacuate_coboundaryArena.Law survivorRejected := by
  intro h
  exact h testGraph ⟨()⟩ testNonloop 0

def evacuate_coboundaryEvidence : Registration evacuate_coboundaryArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_coboundary.{u,v})) where
  actual := survivorActual
  bridge := Iff.rfl
  variation := ⟨evacuate_coboundaryPositive, survivorRejected, evacuate_coboundaryNegative⟩
  sensitivity := ⟨fun i => ⟨survivorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, evacuate_coboundaryNegative⟩,
    fun i => nomatch i⟩
  dependence := survivorDependence

noncomputable def evacuate_coboundaryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_coboundary.{u,v})
    (type_of% (realize survivorSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_coboundary
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_coboundaryArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_coboundaryEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨evacuate_coboundaryArena⟩, objectArena := .source ⟨evacuate_coboundaryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source evacuate_coboundaryArena ⟨evacuate_coboundaryEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize survivorSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[1, 5], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms evacuate_coboundaryRegistration

@[reducible] def extend_coboundaryArena : Arena where
  signature := edgeSignature.{v}
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (k : ContractedVertex G e → ℚ),
    R.readout () E (extend e (coboundary (contract G e h) k))
      (coboundary G (k ∘ vertexMap G e h))

theorem extend_coboundaryPositive : extend_coboundaryArena.Law edgeActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_coboundary.{u,v}
theorem extend_coboundaryNegative : ¬ extend_coboundaryArena.Law edgeRejected := by
  intro h
  exact h testGraph ⟨()⟩ testNonloop 0

def extend_coboundaryEvidence : Registration extend_coboundaryArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_coboundary.{u,v})) where
  actual := edgeActual
  bridge := Iff.rfl
  variation := ⟨extend_coboundaryPositive, edgeRejected, extend_coboundaryNegative⟩
  sensitivity := ⟨fun i => ⟨edgeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, extend_coboundaryNegative⟩,
    fun i => nomatch i⟩
  dependence := edgeDependence

noncomputable def extend_coboundaryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_coboundary.{u,v})
    (type_of% (realize edgeSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_coboundary
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_coboundaryArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_coboundaryEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨extend_coboundaryArena⟩, objectArena := .source ⟨extend_coboundaryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source extend_coboundaryArena ⟨extend_coboundaryEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize edgeSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms extend_coboundaryRegistration

@[reducible] def evacuate_extendArena : Arena where
  signature := survivorSignature.{v}
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (G : DirectedMultigraph V E) (e : E) (b : Surviving e → ℚ),
    R.readout () ⟨E, e⟩ (evacuate G e (extend e b)) b

theorem evacuate_extendPositive : evacuate_extendArena.Law survivorActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_extend.{u,v}
theorem evacuate_extendNegative : ¬ evacuate_extendArena.Law survivorRejected := by
  intro h
  exact h testGraph ⟨()⟩ 0

def evacuate_extendEvidence : Registration evacuate_extendArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_extend.{u,v})) where
  actual := survivorActual
  bridge := Iff.rfl
  variation := ⟨evacuate_extendPositive, survivorRejected, evacuate_extendNegative⟩
  sensitivity := ⟨fun i => ⟨survivorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, evacuate_extendNegative⟩,
    fun i => nomatch i⟩
  dependence := survivorDependence

noncomputable def evacuate_extendRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_extend.{u,v})
    (type_of% (realize survivorSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_extend
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_extendArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.evacuate_extendEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨evacuate_extendArena⟩, objectArena := .source ⟨evacuate_extendArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source evacuate_extendArena ⟨evacuate_extendEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize survivorSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[1, 5], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms evacuate_extendRegistration

@[reducible] def extend_evacuate_subArena : Arena where
  signature := edgeSignature.{v}
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (a : E → ℚ),
    R.readout () E (extend e (evacuate G e a) - a)
      (coboundary G (fun w => -a e * (if w = G.target e then 1 else 0)))

theorem extend_evacuate_subPositive : extend_evacuate_subArena.Law edgeActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_evacuate_sub.{u,v}
theorem extend_evacuate_subNegative : ¬ extend_evacuate_subArena.Law edgeRejected := by
  intro h
  exact h testGraph ⟨()⟩ testNonloop 0

def extend_evacuate_subEvidence : Registration extend_evacuate_subArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_evacuate_sub.{u,v})) where
  actual := edgeActual
  bridge := Iff.rfl
  variation := ⟨extend_evacuate_subPositive, edgeRejected, extend_evacuate_subNegative⟩
  sensitivity := ⟨fun i => ⟨edgeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, extend_evacuate_subNegative⟩,
    fun i => nomatch i⟩
  dependence := edgeDependence

noncomputable def extend_evacuate_subRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_evacuate_sub.{u,v})
    (type_of% (realize edgeSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_evacuate_sub
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_evacuate_subArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.extend_evacuate_subEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨extend_evacuate_subArena⟩, objectArena := .source ⟨extend_evacuate_subArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source extend_evacuate_subArena ⟨extend_evacuate_subEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize edgeSignature.{v} (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms extend_evacuate_subRegistration

@[reducible] def cohomologyEquiv_representativesArena : Arena where
  signature := graphSignature.{u,v}
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e),
    (∀ a : E → ℚ, cohomologyEquiv G e h ((coboundary G).range.mkQ a) =
      (coboundary (contract G e h)).range.mkQ (evacuate G e a)) ∧
    (∀ b : Surviving e → ℚ, R.readout () ⟨V, E, G⟩
      ((cohomologyEquiv G e h).symm ((coboundary (contract G e h)).range.mkQ b))
      ((coboundary G).range.mkQ (extend e b)))

theorem cohomologyEquiv_representativesPositive : cohomologyEquiv_representativesArena.Law graphActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomologyEquiv_representatives.{u,v}
theorem cohomologyEquiv_representativesNegative : ¬ cohomologyEquiv_representativesArena.Law graphRejected := by
  intro h
  exact (h testGraph ⟨()⟩ testNonloop).2 0

def cohomologyEquiv_representativesEvidence : Registration cohomologyEquiv_representativesArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomologyEquiv_representatives.{u,v})) where
  actual := graphActual
  bridge := Iff.rfl
  variation := ⟨cohomologyEquiv_representativesPositive, graphRejected, cohomologyEquiv_representativesNegative⟩
  sensitivity := ⟨fun i => ⟨graphRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cohomologyEquiv_representativesNegative⟩,
    fun i => nomatch i⟩
  dependence := graphDependence

noncomputable def cohomologyEquiv_representativesRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomologyEquiv_representatives.{u,v})
    (type_of% (realize graphSignature.{u,v} (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomologyEquiv_representatives
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomologyEquiv_representativesArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomologyEquiv_representativesEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cohomologyEquiv_representativesArena⟩, objectArena := .source ⟨cohomologyEquiv_representativesArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cohomologyEquiv_representativesArena ⟨cohomologyEquiv_representativesEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize graphSignature.{u,v} (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[0, 1, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms cohomologyEquiv_representativesRegistration

@[reducible] def coboundary_annihilates_cyclesArena : Arena where
  signature := scalarSignature
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [Fintype E]
    (G : DirectedMultigraph V E) (k : V → ℚ) (z : CycleSpace G),
    R.readout () () (∑ f : E, coboundary G k f * z.val f) 0

theorem coboundary_annihilates_cyclesPositive : coboundary_annihilates_cyclesArena.Law scalarActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.coboundary_annihilates_cycles.{u,v}
theorem coboundary_annihilates_cyclesNegative : ¬ coboundary_annihilates_cyclesArena.Law scalarRejected := by
  intro h
  exact h testGraph 0 0

def coboundary_annihilates_cyclesEvidence : Registration coboundary_annihilates_cyclesArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.coboundary_annihilates_cycles.{u,v})) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨coboundary_annihilates_cyclesPositive, scalarRejected, coboundary_annihilates_cyclesNegative⟩
  sensitivity := ⟨fun i => ⟨scalarRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, coboundary_annihilates_cyclesNegative⟩,
    fun i => nomatch i⟩
  dependence := scalarDependence

noncomputable def coboundary_annihilates_cyclesRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.coboundary_annihilates_cycles.{u,v})
    (type_of% (realize scalarSignature (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.coboundary_annihilates_cycles
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.coboundary_annihilates_cyclesArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.coboundary_annihilates_cyclesEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨coboundary_annihilates_cyclesArena⟩, objectArena := .source ⟨coboundary_annihilates_cyclesArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source coboundary_annihilates_cyclesArena ⟨coboundary_annihilates_cyclesEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms coboundary_annihilates_cyclesRegistration

@[reducible] def cohomology_pairing_naturalityArena : Arena where
  signature := scalarSignature
  Law R := ∀ {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E] [Fintype E]
    (G : DirectedMultigraph V E) (e : E) (h : G.source e ≠ G.target e),
    (∀ (a : E → ℚ) (z : CycleSpace G), R.readout () ()
      (cohomologyPairing G ((coboundary G).range.mkQ a) z) (∑ f : E, a f * z.val f)) ∧
    (∀ (a : Cohomology G) (z : CycleSpace (contract G e h)),
      cohomologyPairing (contract G e h) (cohomologyEquiv G e h a) z =
        cohomologyPairing G a ((cycleEquiv G e h).symm z)) ∧
    (∀ (b : Cohomology (contract G e h)) (z : CycleSpace G),
      cohomologyPairing G ((cohomologyEquiv G e h).symm b) z =
        cohomologyPairing (contract G e h) b (cycleEquiv G e h z))

theorem cohomology_pairing_naturalityPositive : cohomology_pairing_naturalityArena.Law scalarActual :=
  @_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomology_pairing_naturality.{u,v}
theorem cohomology_pairing_naturalityNegative : ¬ cohomology_pairing_naturalityArena.Law scalarRejected := by
  intro h
  exact (h testGraph ⟨()⟩ testNonloop).1 0 0

def cohomology_pairing_naturalityEvidence : Registration cohomology_pairing_naturalityArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomology_pairing_naturality.{u,v})) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨cohomology_pairing_naturalityPositive, scalarRejected, cohomology_pairing_naturalityNegative⟩
  sensitivity := ⟨fun i => ⟨scalarRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cohomology_pairing_naturalityNegative⟩,
    fun i => nomatch i⟩
  dependence := scalarDependence

noncomputable def cohomology_pairing_naturalityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomology_pairing_naturality.{u,v})
    (type_of% (realize scalarSignature (fun _ _ x y => x = y) (fun a => nomatch a))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomology_pairing_naturality
    "Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction/Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomology_pairing_naturalityArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction.cohomology_pairing_naturalityEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨cohomology_pairing_naturalityArena⟩, objectArena := .source ⟨cohomology_pairing_naturalityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cohomology_pairing_naturalityArena ⟨cohomology_pairing_naturalityEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms cohomology_pairing_naturalityRegistration

end
end Reg.D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction
