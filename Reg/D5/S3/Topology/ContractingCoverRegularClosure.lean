import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.ContractingCoverRegularClosure

/-! Source-bound regular-interior observations retain both metric and index universes. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Topology.ContractingCoverRegularClosure

open _root_.D5.S3.Topology.ContractingCoverRegularClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

universe u v

structure Inputs where
  X : Type u
  metric : MetricSpace X

attribute [instance] Inputs.metric

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := Set P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => closure (interior s)) (fun e => nomatch e)

def erased : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs.{u}) {I : Type v} {K : Set P.X},
    IsCompact K → (interior K).Nonempty →
    ∀ {q : NNReal}, q < 1 → ∀ f : I → P.X → P.X,
    (∀ i, LipschitzWith q (f i)) → (∀ i, IsOpenMap (f i)) →
    (⋃ i, f i '' K) = K → R.readout () P K = K

abbrev sourceScope := type_of% (@closure_interior_eq_of_contracting_cover.{u,v})

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h P I K hK hne q hq f hlip hopen hcover
    exact @h P.X I P.metric K hK hne q hq f hlip hopen hcover
  · intro h X I metric K hK hne q hq f hlip hopen hcover
    exact @h ⟨X, metric⟩ I K hK hne q hq f hlip hopen hcover

theorem actual_positive : arena.{u,v}.Law actual :=
  source_bridge.mp (@closure_interior_eq_of_contracting_cover.{u,v})

theorem erased_fails : ¬ arena.{u,v}.Law erased := by
  intro h
  have he := @h ⟨PUnit.{u+1}, inferInstance⟩ PUnit.{v+1} univ
    isCompact_univ (by simp) 0 (by norm_num) (fun _ x => x)
    (by
      intro i
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [Subsingleton.elim x y])
    (fun _ => (Homeomorph.refl _).isOpenMap) (by ext x; simp)
  change (∅ : Set PUnit.{u+1}) = univ at he
  exact Set.empty_ne_univ he

def family : Registration arena.{u,v} sourceScope.{u,v} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨PUnit.{u+1}, inferInstance⟩, ∅, univ, ?_⟩
    change closure (interior (∅ : Set PUnit.{u+1})) ≠ closure (interior univ)
    simpa using (Set.empty_ne_univ : (∅ : Set PUnit.{u+1}) ≠ univ)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, u, 0, 0}
      (@closure_interior_eq_of_contracting_cover.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Topology.ContractingCoverRegularClosure.closure_interior_eq_of_contracting_cover.__information_unit
  realizationName := `Reg.D5.S3.Topology.ContractingCoverRegularClosure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => closure (interior s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.ContractingCoverRegularClosure
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.ContractingCoverRegularClosure
