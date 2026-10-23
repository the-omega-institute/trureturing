import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder OriginalNarrowCost
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes FirstWindowBoundaryCompatibility FirstWindowBoundaryFourLabels GlobalPresetObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace FourLabelAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun m => List (Fin m → Bool)) (fun _ => Nat)
def actual : Realization signature := realize signature
  (fun _ _ bs => bs.length) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 3) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4),
    (∀ d : Pair, (∀ z, z ≠ d →
      (multiplicity m H z : ZMod 2) ≠ (multiplicity m H d : ZMod 2)) ↔ pivot m H = d) ∧
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piFour m H) ∧
    (piFour m H →
    ∃ (g : Pair → Pair) (S : Finset ℕ) (a : BaseAssignment),
      Function.Bijective g ∧ g (pivot m H) = 0 ∧ (g 0).1 = 0 ∧
      (∀ z ∈ internalImage m H, (g z).2 = 0) ∧
      S = (Finset.Ico 2 m).filter (fun h => (g (membership m H (h : ℕ))).1 = 1) ∧
      a = ⟨0, (g 0).2, 0, g (membership m H (1 : ℕ)), g (membership m H (m : ℕ))⟩ ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      (a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0) ∧
      (∀ j, baseCode m S a j = g (membership m H j)) ∧
      R.readout () m (baseWords m S a) = 2 ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (g (membership m H j)).1, some (g (membership m H j)).2] ∧
        (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).flatMap
          (fun b => List.ofFn b.1)).length = 2 * m)
private theorem positive : arena.{u}.Law actual := original_first_window_four_label_compatibility
private def sampleSupport (v : ZMod 2) : Finset ℕ := if v = 0 then {1, 2} else {2, 5}
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let f : Option (LiveRecord 8) → ULift.{u} (ZMod 2) := fun q =>
    match q with
    | none => ULift.up 0
    | some q => ULift.up (supportRow (sampleSupport q.value) (-q.phase).val)
  have inside : ∀ v h, h ∈ sampleSupport v → 1 ≤ h ∧ h ≤ 5 := by
    intro v h mem
    unfold sampleSupport at mem
    split_ifs at mem <;> simp only [Finset.mem_insert, Finset.mem_singleton] at mem
    all_goals rcases mem with rfl | rfl <;> omega
  have target : ∀ (v : ZMod 2) (j : Phase 5) (s : ℕ), s < 8 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ sampleSupport v then ULift.up 1 else ULift.up 0 := by
    intro v j s hs
    simp only [f, neg_neg, supportRow]
    split_ifs <;> rfl
  obtain ⟨g, S, a, _, _, _, _, _, _, _, _, _, _, _, bad, _⟩ :=
    (law 5 (by omega) false sampleSupport inside
      (fun _ => (ULift.up (0 : ZMod 2) : ULift.{u} (ZMod 2))) (fun _ => ULift.up 1)
      (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target
      (by decide)).2.2 (by unfold piFour; decide)
  change (3 : ℕ) = 2 at bad
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.original_first_window_four_label_compatibility.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, [], [fun _ => false], ?_⟩
    change (0 : ℕ) ≠ 1
    omega

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.original_first_window_four_label_compatibility.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.original_first_window_four_label_compatibility
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.FourLabelAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.FourLabelAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end FourLabelAudit
namespace RegionImageAudit
@[reducible] def signature : Signature := Reg.Support.SingleDependentReadout.signature Nat (fun _ => ZMod 2 → Finset ℕ) (fun _ => Finset Pair)
def actual : Realization signature := realize signature (fun _ m H => fullImage m H) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (H : ZMod 2 → Finset ℕ)
    (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m),
    R.readout () m H = insert 0 (insert (membership m H (1 : ℕ))
      (insert (membership m H (m : ℕ)) (internalImage m H)))
private theorem positive : arena.Law actual := image_regions
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 5 (by omega) (fun _ => ∅) (by simp)
  change (∅ : Finset Pair) = _ at bad
  have member : (0 : Pair) ∈ (∅ : Finset Pair) := by rw [bad]; simp
  simpa using member

def evidence : Registration arena (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.image_regions)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, (fun _ => ∅), (fun _ => {1}), ?_⟩
    change fullImage 5 (fun _ => ∅) ≠ fullImage 5 (fun _ => {1})
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.image_regions) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.image_regions "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.RegionImageAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.RegionImageAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 2, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end RegionImageAudit

namespace PhaseSumAudit
@[reducible] def signature : Signature := Reg.Support.SingleDependentReadout.signature Nat (fun _ => Finset ℕ) (fun _ => ZMod 2)
def actual : Realization signature := realize signature (fun _ m H => ∑ j : Phase m, supportRow H j.val) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (H : Finset ℕ)
    (inside : ∀ h ∈ H, h ≤ 2 * m - 2),
    R.readout () m H = (H.card : ZMod 2)
private theorem positive : arena.Law actual := phase_support_sum
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 5 {1} (by intro h hh; simp only [Finset.mem_singleton] at hh; omega)
  change (0 : ZMod 2) = 1 at bad
  exact zero_ne_one bad

def evidence : Registration arena (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.phase_support_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, ∅, {1}, ?_⟩
    change (∑ j : Phase 5, supportRow ∅ j.val) ≠ ∑ j : Phase 5, supportRow {1} j.val
    decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.phase_support_sum) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.phase_support_sum "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.PhaseSumAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels.PhaseSumAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels, definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 2, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end PhaseSumAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels
