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

namespace Coordinates
abbrev signature := Arithmetic.signature
abbrev actual := Arithmetic.actual

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Basis → Bool),
    r.readout () L ⟨T,e⟩ = Coeff.realPhysical (Coeff.coordinates T e) ∧
    Coeff.realConjugate (Coeff.coordinates T e) =
      (∑ p, ∑ z, if e p z then (-1 : ℝ)^Coeff.exponent z *
        Complex.normSq (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) z)
        else 0) ∧
    |Coeff.realConjugate (Coeff.coordinates T e)| ≤ Coeff.kappa^(2*maxCalls T)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h Unit (.leaf ()) (fun _ _ => false)).1
  change (1 : ℝ) = Coeff.realPhysical (Coeff.coordinates _ _) at hh
  simp [Coeff.coordinates] at hh

def family : Registration arena (type_of% (@original_event_coordinates_and_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e => original_event_coordinates_and_bound T e,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := Arithmetic.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_coordinates_and_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_event_coordinates_and_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Coordinates.family
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
end Coordinates

namespace Resources
abbrev signature := Arithmetic.signature
abbrev actual := Arithmetic.actual
abbrev rejected := Arithmetic.rejected

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : Type) (T : NativeTree L) (e : Path T → Basis → Bool),
    (0 < r.readout () L ⟨T,e⟩ →
      (Coeff.kappa^(2*maxCalls T))⁻¹ ≤ r.readout () L ⟨T,e⟩) ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(13+5*Real.sqrt 5)/22)) ≤
      |r.readout () L ⟨T,e⟩-emptyTarget| ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(19+9*Real.sqrt 5)/22)) ≤
      |r.readout () L ⟨T,e⟩-referenceTarget|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h Unit (.leaf ()) (fun _ _ => false)).2.1
  change 1/(11*(Coeff.kappa^(2*maxCalls ((.leaf ()) : NativeTree Unit))+
    (13+5*Real.sqrt 5)/22)) ≤ |emptyTarget-emptyTarget| at hh
  rw [sub_self, abs_zero] at hh
  have hp : 0 < 1/(11*(Coeff.kappa^(2*maxCalls ((.leaf ()) : NativeTree Unit))+
      (13+5*Real.sqrt 5)/22)) := by
    dsimp [Coeff.kappa, phi]
    positivity
  linarith

def family : Registration arena (type_of% (@original_event_resource_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ T e => original_event_resource_bounds T e,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,?_,rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := Arithmetic.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_event_resource_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_event_resource_bounds.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Resources.family
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
end Resources

#print axioms Coordinates.family
#print axioms Resources.family


namespace EmptyPetz
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Actual
local instance : NormedAddCommGroup Qubit := Matrix.instL2OpNormedAddCommGroup
local instance : NormedSpace ℂ Qubit := Matrix.instL2OpNormedSpace
local instance : NormedRing Qubit := Matrix.instL2OpNormedRing
local instance : NormedAlgebra ℂ Qubit := Matrix.instL2OpNormedAlgebra

abbrev Input := Fin 2 → NativeTree Stop
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Input) (fun _ => ℝ × ℕ)

/-- Both observed operands occur in the original continuation discrepancy:
the actual raw event and its complete syntactic maximum resource. -/
def actual : Realization signature :=
  realize signature (fun _ _ C =>
    (eventMass (extensionAt .active C) (fun _ z => z 2),
      maxCalls (extensionAt .active C))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ C =>
    (emptyTarget,maxCalls (extensionAt .active C))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    reduced ((operator sourceTree ()).mulVec omega0) = chi ∧
    calls sourceTree () = 3 ∧ chi.PosDef ∧ chi.trace = 1 ∧ chi.det = t^4 ∧
    cfc Real.sqrt chi = chiRoot ∧
    (∀ v : Basis → ℂ,
      (∑ j : Fin 2, reduced ((projector (readBit 2) j).mulVec v)) =
        delta (reduced v)) ∧
    reduced omega0 = p0 ∧
    (∀ j : Fin 2, (projector (readBit 2) j).mulVec omega0 =
      if j = 0 then omega0 else 0) ∧
    petz (reduced omega0) 1 1 = ((emptyTarget : ℝ) : ℂ) ∧
    (∀ C : Fin 2 → NativeTree Stop,
      let T := extensionAt .active C
      (r.readout () () C).1 ≠ (petz (reduced omega0) 1 1).re ∧
      1/(11*(Coeff.kappa^(2*(r.readout () () C).2)+(13+5*Real.sqrt 5)/22)) ≤
        |(r.readout () () C).1 - (petz (reduced omega0) 1 1).re|)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h with ⟨_,_,_,_,_,_,_,_,_,hp,hall⟩
  have hx := (hall (fun _ => .leaf ⟨.normal,0⟩)).1
  change emptyTarget ≠ (petz (reduced omega0) 1 1).re at hx
  rw [hp, Complex.ofReal_re] at hx
  exact hx rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let x : Input := fun _ => .leaf ⟨.normal,0⟩
  let y : Input := fun _ => .call 0 .inverse (.leaf ⟨.normal,0⟩)
  refine ⟨(),x,y,?_⟩
  intro heq
  have hh := congrArg Prod.snd heq
  change maxCalls (extensionAt .active x) = maxCalls (extensionAt .active y) at hh
  have hx : maxCalls (extensionAt .active x) = 0 := by
    simp [maxCalls, extensionAt, x, calls]
  have hy : maxCalls (extensionAt .active y) = 9 := by
    simp only [maxCalls, extensionAt, y, calls, callCost, add_zero]
    exact Finset.sup_const Finset.univ_nonempty 9
  rw [hx,hy] at hh
  norm_num at hh

def family : Registration arena (type_of% (@original_empty_petz_consumer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_empty_petz_consumer,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- Whole-family evidence retains the exact original input and both readout
operands. Selected source reconstruction remains unresolved under issue 26627. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_empty_petz_consumer) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_empty_petz_consumer.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.EmptyPetz.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end EmptyPetz

end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
