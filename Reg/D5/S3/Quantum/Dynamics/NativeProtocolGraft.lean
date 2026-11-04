import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Dynamics.NativeProtocolGraft

/-! Whole-family registration of the original native protocol input. -/

noncomputable section
open scoped BigOperators Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
local notation "NativeTree" => _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree

/-- The complete dependent original input, including the actual feedback table
and the actual original-record event. It is not a scalar proxy for a protocol. -/
structure NativeInput where
  tree : NativeTree Cut
  continuation : Path tree → Fin 2 → NativeTree Stop
  program : ℕ
  event : (ℕ × Path tree × Option (Fin 2) × Stop) → Basis → Bool

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => NativeInput) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x =>
    projectedMass x.tree x.continuation x.program x.event) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (T : NativeTree Cut) (C : Path T → Fin 2 → NativeTree Stop)
    (program : ℕ) (event : (ℕ × Path T × Option (Fin 2) × Stop) → Basis → Bool) ,
    r.readout () () ⟨T,C,program,event⟩ =
      (∑ p, ∑ q : Path (extension T C p), ∑ z,
        if event (program,p,readTag (label T p) (C p) q,label (extension T C p) q) z then
          Complex.normSq (((operator (extension T C p) q * operator T p).mulVec omega0) z)
        else 0) ∧
    maxCalls (graft T (extension T C)) =
      Finset.univ.sup (fun p => calls T p + maxCalls (extension T C p)) ∧
    (∀ p, CutLaw (label T p) (C p)) ∧
    (∀ (p : Path T) (q : Path (extension T C p)),
      operator (graft T (extension T C)) (attach T (extension T C) p q) =
        operator (extension T C p) q * operator T p ∧
      archive (graft T (extension T C)) (attach T (extension T C) p q) =
        archive T p ++ archive (extension T C p) q ∧
      calls (graft T (extension T C)) (attach T (extension T C) p q) =
        calls T p + calls (extension T C p) q ∧
      label (graft T (extension T C)) (attach T (extension T C) p q) =
        label (extension T C p) q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let T : NativeTree Cut := .leaf .active
  let C : Path T → Fin 2 → NativeTree Stop := fun _ _ => .leaf ⟨.normal,0⟩
  have hb := (h T C 0 (fun _ _ => false)).1
  change (1 : ℝ) = _ at hb
  simp at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let T : NativeTree Cut := .leaf (.absorbed ⟨.normal,0⟩)
  let C : Path T → Fin 2 → NativeTree Stop := fun _ _ => .leaf ⟨.normal,0⟩
  let x : NativeInput := ⟨T,C,0,fun _ _ => false⟩
  let y : NativeInput := ⟨T,C,0,fun _ _ => true⟩
  refine ⟨(),x,y,?_⟩
  change projectedMass T C 0 (fun _ _ => false) ≠
    projectedMass T C 0 (fun _ _ => true)
  simp [projectedMass, eventMass, mass, graft, extension, extensionAt,
    T, C, label, operator, omega0]
  apply ne_of_lt
  exact_mod_cast (Finset.card_pos.mpr (Finset.univ_nonempty :
    (Finset.univ : Finset (Path ((.leaf ⟨.normal,0⟩) : NativeTree Stop))).Nonempty))

def family : Registration arena (type_of% (@original_native_projection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_native_projection,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- The full source family has typed evidence. Source occurrence selection
remains unspecified; this does not assert accepted source reconstruction. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_native_projection) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_native_projection.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x =>
    projectedMass x.tree x.continuation x.program x.event) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Arithmetic

structure Event (L : Type) where
  tree : NativeTree L
  event : Path tree → Basis → Bool

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
  realize signature (fun _ _ x => eventMass x.tree x.event) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => emptyTarget) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Basis → Bool),
    IsIntegral ℤ (r.readout () L ⟨T,e⟩) ∧
      r.readout () L ⟨T,e⟩ ≠ emptyTarget ∧
      r.readout () L ⟨T,e⟩ ≠ referenceTarget

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h Unit (.leaf ()) (fun _ _ => false)).2.1 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨Unit,⟨.leaf (),fun _ _ => false⟩,⟨.leaf (),fun _ _ => true⟩,?_⟩
  change eventMass ((.leaf ()) : NativeTree Unit) (fun _ _ => false) ≠
    eventMass ((.leaf ()) : NativeTree Unit) (fun _ _ => true)
  simp [eventMass, mass, operator, omega0]
  apply ne_of_lt
  exact_mod_cast (Finset.card_pos.mpr (Finset.univ_nonempty :
    (Finset.univ : Finset (Path ((.leaf ()) : NativeTree Unit))).Nonempty))

def family : Registration arena (type_of% (@original_event_arithmetic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e => original_event_arithmetic T e,rejected,rejected_law⟩
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
    (@original_event_arithmetic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_event_arithmetic.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Arithmetic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => eventMass x.tree x.event)
    (fun e => nomatch e))
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
end Arithmetic

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
