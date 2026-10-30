import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth

/-! Complete direction geometry as a dependent depth and literal-query family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth
open _root_.D5.S3.ConceptDynamics.InformationEscape
open GenealogicalFiberTransport (Source decompose)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (height)

inductive Role where
  | depths | queries
  deriving DecidableEq, Inhabited

instance : Fintype Role := ⟨{.depths, .queries}, by
  intro i
  cases i <;> simp⟩

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Source × Address × Address
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun i _ => match i with
    | .depths => Nat
    | .queries => List Address
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ (i : Role) (_ : Unit), signature.State () → signature.Output i ()
  | .depths, _, s => depth s.1 s.2.2
  | .queries, _, s => probes s.1 s.2.1 s.2.2

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature actualReadout (fun e => nomatch e)

def geometry (d : Source → Address → Nat) (pr : Source → Address → Address → List Address) : Prop :=
  ∀ T : Source,
    (∀ (U : Source) (p u : Address),
      (∀ w, readout (p ++ w) U = readout w T) → height T ≤ u.length →
      PaidWalk U p u (pr T p u) (d T u) ∧
        Observer.NativeSerialMachine.Run controller (.walk p u 0) 0 U
          (eventTrace U (pr T p u)) (d T u)) ∧
    (∀ p u : Address, (pr T p u).length = d T u + 1) ∧
    (∀ u : Address, d T u ≤ height T) ∧
    (∀ u v : Address, height T ≤ u.length → d T (u ++ v) = d T u) ∧
    (∀ L : Nat, height T ≤ L → ∃ u : Address, u.length = L ∧ d T u = height T) ∧
    (∀ (U : Source) (p : Address), subtree p U = some T →
      p.length + height T ≤ height U ∧
      ∀ u : Address, d U (p ++ u) = p.length + d T u) ∧
    (∀ (U : Source) (L : Nat), height T ≤ L → height U ≤ L →
      (∀ u : Address, u.length = L → d T u = d U u) →
      (decompose T).1 = (decompose U).1)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := geometry (fun T u => R.readout .depths () (T, [], u))
    (fun T p u => R.readout .queries () (T, p, u))

abbrev sourceScope := type_of% (@tape_geometry)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erasedReadout (i : Role) : ∀ (j : Role) (p : Unit),
    signature.State p → signature.Output j p
  | .depths, _, s => if i = .depths then 0 else depth s.1 s.2.2
  | .queries, _, s => if i = .queries then [] else probes s.1 s.2.1 s.2.2

def erased (i : Role) : DependentFamily.Realization signature :=
  DependentFamily.realize signature (erasedReadout i) (fun e => nomatch e)

theorem erasure_fails (i : Role) : ¬ arena.Law (erased i) := by
  intro h
  cases i with
  | depths =>
      have hx := (h (.mul (.of true) (.of true))).2.2.2.2.1 1 (by decide)
      obtain ⟨u, _, hu⟩ := hx
      change 0 = 1 at hu
      omega
  | queries =>
      have hx := (h (.of true)).2.1 [] []
      change 0 = 1 at hx
      omega

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨tape_geometry, erased .depths, erasure_fails .depths⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased i, ?_, rfl, erasure_fails i⟩
      intro j hj
      funext p s
      cases i <;> cases j <;> simp [erased, erasedReadout, actual,
        actualReadout, DependentFamily.realize] at hj ⊢
    · intro e; exact nomatch e
  dependence := by
    intro i
    change Role at i
    cases i with
    | depths =>
        refine ⟨(), (.of true, [], [false]), (.mul (.of true) (.of true), [], [false]), ?_⟩
        change (0 : Nat) ≠ 1
        decide
    | queries =>
        refine ⟨(), (.of true, [], []), (.of true, [true], []), ?_⟩
        change ([[false]] : List Address) ≠ [[true, false]]
        decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@tape_geometry) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth.tape_geometry.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth.family
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

end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PhysicalTapeDepth
