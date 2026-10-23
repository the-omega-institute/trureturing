import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder OriginalNarrowCost
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes FirstWindowBoundaryCompatibility GlobalPresetObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace BaseInternalAudit
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
    (three : (fullImage m H).card = 3),
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piThree m H) ∧
    (∀ (two : (internalImage m H).card = 2) (base : (0 : Pair) ∈ internalImage m H),
    ∃ (X : Pair) (S : Finset ℕ) (a : BaseAssignment),
      X ≠ 0 ∧ internalImage m H = {0, X} ∧
      S = (Finset.Ico 2 m).filter (fun h => membership m H (h : ℕ) = X) ∧
      a = baseChoice m S.card (classIndex X (membership m H (1 : ℕ)))
        (classIndex X (membership m H (m : ℕ))) ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      R.readout () m (baseWords m S a) = 2 ∧
      (∀ p q, baseCode m S a p = baseCode m S a q → membership m H p = membership m H q) ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (baseCode m S a j).1, some (baseCode m S a j).2] ∧
        (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).flatMap
          (fun b => List.ofFn b.1)).length = 2 * m)
private theorem positive : arena.{u}.Law actual := original_first_window_three_label_compatibility
private def sampleSupport (v : ZMod 2) : Finset ℕ := if v = 0 then {2} else {1}
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let f : Option (LiveRecord 8) → ULift.{u} (ZMod 2) := fun q =>
    match q with
    | none => ULift.up 0
    | some q => ULift.up (supportRow (sampleSupport q.value) (-q.phase).val)
  have inside : ∀ v h, h ∈ sampleSupport v → 1 ≤ h ∧ h ≤ 5 := by
    intro v h mem
    unfold sampleSupport at mem
    split_ifs at mem <;> simp only [Finset.mem_singleton] at mem <;> omega
  have target : ∀ (v : ZMod 2) (j : Phase 5) (s : ℕ), s < 8 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ sampleSupport v then ULift.up 1 else ULift.up 0 := by
    intro v j s hs
    simp only [f, neg_neg, supportRow]
    split_ifs <;> rfl
  obtain ⟨X, S, a, _, _, _, _, _, _, _, bad, _⟩ := (law 5 (by omega) false sampleSupport inside
    (fun _ => (ULift.up (0 : ZMod 2) : ULift.{u} (ZMod 2))) (fun _ => ULift.up 1)
    (by intro v h; exact zero_ne_one (congrArg ULift.down h)) f target
    (by decide)).2 (by decide) (by decide)
  change (3 : ℕ) = 2 at bad
  omega

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.original_first_window_three_label_compatibility.{u})) where
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
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.original_first_window_three_label_compatibility.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.original_first_window_three_label_compatibility
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.BaseInternalAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.BaseInternalAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end BaseInternalAudit

namespace BaseScriptAudit
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat
    (fun m => ZMod 2 × NarrowWindowCost.Archive m) (fun _ => List (Option (ZMod 2)))
def actual : Realization signature := realize signature
  (fun _ _ q => endpointDifferences (some q.1) (q.2.map Prod.snd)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (a : BaseAssignment)
    (first : (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0)
    (second : a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0)
    (seam : a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2),
    R.readout () m (v, scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)) =
      [some (baseCode m S a j).1, some (baseCode m S a j).2]
private theorem positive : arena.Law actual := base_script_code
private theorem negative : ¬ arena.Law rejected := by
  intro law
  have bad := law 5 (by omega) ∅ (by simp) ⟨0, 0, 0, 0, 0⟩
    (by simp) (by simp) (Or.inl rfl) 0 0 0 (by omega)
  change ([] : List (Option (ZMod 2))) = [some _, some _] at bad
  have lengths := congrArg List.length bad
  simp only [List.length_nil, List.length_cons] at lengths
  omega

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.base_script_code)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨5, (0, []), (0, [(fun _ => false, some 0)]), ?_⟩
    change ([] : List (Option (ZMod 2))) ≠ [some 0]
    simp

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.base_script_code)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.base_script_code
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.BaseScriptAudit/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility.BaseScriptAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility,
    definition := none, coordinates := #[1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms evidence
#print axioms registration
end BaseScriptAudit

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility
