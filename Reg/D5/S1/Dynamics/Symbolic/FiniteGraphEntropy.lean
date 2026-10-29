import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Reg.Support.DependentFamily

/-! Observe graph languages in the original carrier and instance telescope. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
open SymbolicDynamics Set Function Filter
open scoped Topology

namespace Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy

noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State V := V → V → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Set (ℕ → V)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ edge => edgeLanguage edge) (fun e => nomatch e)

def compactRejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => {w | ∃ i j, w i ≠ w j}) (fun e => nomatch e)

def shiftRejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

/-- Only the first source occurrence varies; every original binder and the
    entire compactness-and-closedness conclusion remain in the law. -/
def compactArena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [Fintype V] [TopologicalSpace V] [DiscreteTopology V]
    (edge : V → V → Prop),
    IsCompact (r.readout () V edge) ∧ IsClosed (edgeLanguage edge)

private theorem compact_rejected_law : ¬ compactArena.{u}.Law compactRejected := by
  intro h
  let point : ℕ → ULift.{u} Bool := fun _ => ULift.up false
  let pulse : ℕ → ℕ → ULift.{u} Bool := fun n k => ULift.up (decide (k = n))
  have ht : Tendsto pulse atTop (𝓝 point) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop k] with n hn
    simp [pulse, point, ne_of_lt hn]
  have hp : ∀ n, pulse n ∈ {w : ℕ → ULift.{u} Bool | ∃ i j, w i ≠ w j} := by
    intro n
    refine ⟨n, n + 1, ?_⟩
    simp [pulse]
  have hc : IsClosed {w : ℕ → ULift.{u} Bool | ∃ i j, w i ≠ w j} :=
    (@h (ULift.{u} Bool) inferInstance inferInstance inferInstance (fun _ _ => True)).1.isClosed
  obtain ⟨i, j, hij⟩ := hc.mem_of_tendsto ht (Eventually.of_forall hp)
  exact hij rfl

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ _ => True), (fun _ _ => False), ?_⟩
  intro heq
  have hmem : (fun _ : ℕ => (ULift.up () : ULift.{u} Unit)) ∈
      edgeLanguage (fun _ _ : ULift.{u} Unit => False) := by
    rw [← show edgeLanguage (fun _ _ : ULift.{u} Unit => True) =
      edgeLanguage (fun _ _ : ULift.{u} Unit => False) from heq]
    exact ⟨fun _ => ULift.up (), (fun _ => trivial), (fun _ => rfl)⟩
  obtain ⟨path, hpath, _⟩ := hmem
  exact hpath 0

def compactFamily : Registration compactArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed,
    compactRejected, compact_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨compactRejected, ?_, rfl, compact_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_isCompact_isClosed.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.compactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨compactArena.{u}⟩
  objectArena := .source ⟨compactArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compactArena.{u} ⟨compactFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ edge => edgeLanguage edge) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def shiftArena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [Fintype V] [TopologicalSpace V] [DiscreteTopology V]
    (edge : V → V → Prop),
    MapsTo (FullShift.shift (1 : ℕ)) (r.readout () V edge) (edgeLanguage edge)

private theorem shift_rejected_law : ¬ shiftArena.{u}.Law shiftRejected := by
  intro h
  have hmem := @h (ULift.{u} Unit) inferInstance inferInstance inferInstance
    (fun _ _ => False) (fun _ => ULift.up ()) (Set.mem_univ _)
  obtain ⟨path, hpath, _⟩ := hmem
  exact hpath 0

def shiftFamily : Registration shiftArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant,
    shiftRejected, shift_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shiftRejected, ?_, rfl, shift_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.edgeLanguage_shift_invariant.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.shiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena.{u}⟩
  objectArena := .source ⟨shiftArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena.{u} ⟨shiftFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ edge => edgeLanguage edge) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compactFamily
#print axioms registration_1
#print axioms shiftFamily
#print axioms registration_2

end
end Reg.D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
