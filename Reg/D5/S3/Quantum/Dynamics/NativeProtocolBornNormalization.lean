import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization

/-! Whole-family readout of the original physical tree and position cut. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
local notation "NativeTree" => _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree

structure Event (L : Type) where
  tree : NativeTree L
  event : Path tree → Bool
  positions : Finset (Fin 16)

abbrev signature : Signature where
  Params := Type
  State := Event
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => eventMass x.tree (historyEvent x.event)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Bool) (I : Finset (Fin 16)),
    (∑ p, ∑ z, mass T p z) = 1 ∧
    (0 ≤ r.readout () L ⟨T,e,I⟩ ∧ r.readout () L ⟨T,e,I⟩ ≤ 1) ∧
    (eventCut T I e).PosSemidef ∧
    (eventCut T I e).trace = (r.readout () L ⟨T,e,I⟩ : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h Unit (.leaf ()) (fun _ => false) ∅).2.1.2
  change (2 : ℝ) ≤ 1 at hp
  norm_num at hp

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨Unit,⟨.leaf (),fun _ => false,∅⟩,⟨.leaf (),fun _ => true,∅⟩,?_⟩
  change eventMass ((.leaf ()) : NativeTree Unit) (historyEvent (fun _ => false)) ≠
    eventMass ((.leaf ()) : NativeTree Unit) (historyEvent (fun _ => true))
  simp [eventMass, historyEvent, mass, operator, omega0]
  apply ne_of_lt
  exact_mod_cast (Finset.card_pos.mpr (Finset.univ_nonempty :
    (Finset.univ : Finset (Path ((.leaf ()) : NativeTree Unit))).Nonempty))

def family : Registration arena (type_of% (@original_complete_born_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e I => original_complete_born_law T e I,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_complete_born_law) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization.original_complete_born_law.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => eventMass x.tree (historyEvent x.event)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

abbrev cutArena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Bool) (I : Finset (Fin 16)),
    (eventCut T I e).trace = (r.readout () L ⟨T,e,I⟩ : ℂ) ∧
    (eventCut T I e).det = (Coeff.realPhysical (cutDetCoordinates T I e) : ℂ) ∧
    (conjugateEventCut T I e).det = (Coeff.realConjugate (cutDetCoordinates T I e) : ℂ) ∧
    ∀ i j : CutBasis I, conjugateEventCut T I e i j =
      ∑ p, ∑ z : CutRest I, if e p then
        (-1 : ℂ)^(restExponent I z + rowExponent I j) *
        Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) ((splitAt I).symm (i,z)) *
        star (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) ((splitAt I).symm (j,z)))
      else 0

private theorem cut_rejected_law : ¬ cutArena.Law rejected := by
  intro h
  let T : NativeTree Unit := .leaf ()
  have ht := (original_complete_born_law T (fun _ => false) ∅).2.2.2
  have hb := (h Unit T (fun _ => false) ∅).1
  change (eventCut T ∅ (fun _ => false)).trace = (2 : ℂ) at hb
  rw [ht] at hb
  simp [eventMass, historyEvent] at hb

def cutFamily : Registration cutArena (type_of% (@original_event_cut_integer_coordinates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e I => original_event_cut_integer_coordinates T e I,
    rejected,cut_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,cut_rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def cutRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_cut_integer_coordinates) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization.original_event_cut_integer_coordinates.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization.cutFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cutArena⟩
  objectArena := .source ⟨cutArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cutArena ⟨cutFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => eventMass x.tree (historyEvent x.event)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cutFamily
#print axioms cutRegistration

abbrev resourceArena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (event : Path T → Bool) (I : Finset (Fin 16)),
    let Xi := eventCut T I event
    let p := r.readout () L ⟨T,event,I⟩
    let K := Coeff.kappa^(2*maxCalls T*Fintype.card (CutBasis I))
    let rho := ((p⁻¹ : ℝ) : ℂ) • Xi
    Xi.trace = (p : ℂ) ∧
    |Coeff.realConjugate (cutDetCoordinates T I event)| ≤ K ∧
    (0 < p → (Coeff.kappa^(2*maxCalls T))⁻¹ ≤ p ∧
      (Xi.rank = Fintype.card (CutBasis I) →
        K⁻¹ ≤ Xi.det.re ∧
        ∃ hXi : Xi.IsHermitian, ∃ hRho : rho.IsHermitian,
          K⁻¹ ≤ iInf hXi.eigenvalues ∧ K⁻¹/p ≤ iInf hRho.eigenvalues))

private theorem resource_rejected_law : ¬ resourceArena.Law rejected := by
  intro h
  let T : NativeTree Unit := .leaf ()
  have ht := (original_complete_born_law T (fun _ => false) ∅).2.2.2
  have hb := (h Unit T (fun _ => false) ∅).1
  change (eventCut T ∅ (fun _ => false)).trace = (2 : ℂ) at hb
  rw [ht] at hb
  simp [eventMass, historyEvent] at hb

def resourceFamily : Registration resourceArena (type_of% (@original_event_cut_resource_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e I => original_event_cut_resource_bounds T e I,
    rejected,resource_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,resource_rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def resourceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_cut_resource_bounds) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization.original_event_cut_resource_bounds.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization.resourceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨resourceArena⟩
  objectArena := .source ⟨resourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resourceArena ⟨resourceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => eventMass x.tree (historyEvent x.event)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms resourceFamily
#print axioms resourceRegistration

end Reg.D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
