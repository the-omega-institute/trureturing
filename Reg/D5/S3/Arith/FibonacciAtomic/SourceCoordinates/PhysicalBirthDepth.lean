import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth

/-! The whole physical telescope with depth and absolute-query roles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth
  (Role signature actual actualReadout erased erasedReadout)
open GenealogicalFiberTransport (Source decompose)
open ActualTreeReadoutAcquisition (Address readout)
open ActualImageAddressCertificate (height)

def depthMaximum (d : Source → Address → Nat) (T : Source) (L m : Nat) : Prop :=
  (∀ u : Address, u.length = L → d T u ≤ m) ∧
    ∃ u : Address, u.length = L ∧ d T u = m

def beats (d : Source → Address → Nat) (a b : Source) (L : Nat) : Prop :=
  ∃ u : Address, u.length = L ∧ ∀ v : Address, v.length = L → d b v < d a u

def rootBeats (d : Source → Address → Nat) (U : Source) (p : Address) (L : Nat) : Prop :=
  ∃ u : Address, u.length = L ∧ ∀ v : Address, v.length = L →
    d U (p ++ true :: v) < d U (p ++ false :: u)

def coneLaw (dpth : Source → Address → Nat)
    (pr : Source → Address →Address → List Address) (n : Nat) (z : Nat → Bool) (p : Address) (T : Physical) : Prop :=
  let q := rank n T
  T.descriptor.born ≤ n ∧ q + p.length ≤ n ∧ height T.source = q - 1 ∧
  (q ≤ 1 ↔ ∃ d c, T = .leaf d c) ∧
  (∀ u : Address, dpth T.source u ≤ q - 1) ∧
  (∀ (L : Nat), q - 1 ≤ L → depthMaximum dpth T.source L (q - 1)) ∧
  (∀ u : Address, q - 1 ≤ u.length →
    PaidWalk (orbit z n).1.source p u (pr T.source p u) (dpth T.source u) ∧
      (pr T.source p u).length = dpth T.source u + 1 ∧
      Observer.NativeSerialMachine.Run PhysicalTapeDepth.controller (.walk p u 0) 0 (orbit z n).1.source
        (PhysicalTapeDepth.eventTrace (orbit z n).1.source (pr T.source p u))
        (dpth T.source u)) ∧
  (∀ u v : Address, q - 1 ≤ u.length → dpth T.source (u ++ v) = dpth T.source u) ∧
  (∀ (L : Nat), n - 1 ≤ L → q - 1 ≤ L - p.length) ∧
  (∀ u : Address, dpth (orbit z n).1.source (p ++ u) = p.length + dpth T.source u) ∧
  (∀ u v : Address, 2 ≤ n → u.length = (2 * n - 1) - p.length →
    v.length = p.length →
    dpth (orbit z n).1.source (p ++ u) = p.length + dpth T.source u ∧
    p.length + dpth T.source u = p.length + dpth T.source (u ++ v)) ∧
  (∀ (U : Source) (L : Nat), q - 1 ≤ L → height U ≤ L →
    (∀ u : Address, u.length = L →
      dpth (orbit z n).1.source (p ++ u) = p.length + dpth U u) →
      (decompose T.source).1 = (decompose U).1) ∧
  (∀ (d : Descriptor) (e : Birth) (a b : Physical), T = .branch d e a b →
    2 ≤ q ∧ e.time = d.born + (if d.initial then 2 else 1) ∧ e.time ≤ n ∧
    0 < e.index ∧ e.bit = z e.index ∧ a.descriptor.born = e.time ∧
    b.descriptor.born = e.time ∧ a.descriptor.initial = !e.bit ∧
    b.descriptor.initial = e.bit ∧
    (if e.bit then rank n a else rank n b) = q - 1 ∧
    (if e.bit then rank n b else rank n a) = q - 2 ∧
    (if e.bit then height a.source else height b.source) = q - 2 ∧
    (if e.bit then height b.source else height a.source) = q - 3 ∧
    (∀ (L : Nat), q - 2 ≤ L →
      depthMaximum dpth (if e.bit then a.source else b.source) L (q - 2) ∧
      depthMaximum dpth (if e.bit then b.source else a.source) L (q - 3) ∧
      (3 ≤ q → (e.bit = true ↔ beats dpth a.source b.source L))) ∧
    (3 ≤ q → q - 2 ≤ (2 * n - 1) - p.length - 1 ∧
      p.length + 1 + ((2 * n - 1) - p.length - 1) = 2 * n - 1 ∧
      (e.bit = true ↔ rootbeats dpth dpth (orbit z n).1.source p ((2 * n - 1) - p.length - 1))) ∧
    (q = 3 → (if e.bit then height a.source else height b.source) = 1 ∧
      (if e.bit then height b.source else height a.source) = 0) ∧
    (q = 2 → a.source = .of (!e.bit) ∧ b.source = .of e.bit ∧
      (∀ u : Address, u ≠ [] → dpth T.source u = 1) ∧
      ∀ u : Address, dpth T.source u = dpth (.mul b.source a.source) u))


def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (n : Nat) (z : Nat → Bool),
    (orbit z n).1.descriptor = ⟨0, true⟩ ∧ rank n (orbit z n).1 = n ∧
    ∀ (p : Address) (T : Physical), Physical.at p (orbit z n).1 = some T →
      coneLaw (fun t u => R.readout .depths () (t, [], u))
        (fun t p u => R.readout .queries () (t, p, u)) n z p T

abbrev sourceScope := type_of% (@observable_orientations)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erasure_fails (i : Role) : ¬ arena.Law (erased i) := by
  intro h
  cases i with
  | depths =>
      let z : Nat → Bool := fun _ => true
      have hT := (h 2 z).2.2 [] (orbit z 2).1 rfl
      have hx := hT.2.2.2.2.2.1 1 (by decide)
      obtain ⟨u, _, hu⟩ := hx.2
      change (0 : Nat) = 1 at hu
      omega
  | queries =>
      let z : Nat → Bool := fun _ => true
      have hT := (h 0 z).2.2 [] (orbit z 0).1 rfl
      have hx := (hT.2.2.2.2.2.2.1 [] (by decide)).2.1
      change (0 : Nat) = 1 at hx
      omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨observable_orientations, erased .depths, erasure_fails .depths⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased i, ?_, rfl, erasure_fails i⟩
      intro j hj
      funext p s
      cases i <;> cases j <;> simp [erased, erasedReadout, actual,
        actualReadout, DependentFamily.realize] at hj ⊢
    · intro e; exact nomatch e
  dependence := _root_.Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth.family.dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@observable_orientations) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth.observable_orientations.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature actualReadout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalBirthDepth
