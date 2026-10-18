import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal BigOperators
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Family where
  S : Type
  O : Type
  d : S → Instruction (S ⊕ O)
abbrev signature : Signature where
  Params := Family
  State C := (C.S ⊕ C.O) × C.O
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ C z => tapeLaw (exits C.d z.1 z.2)) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0),
    0 < denominator d E ∧ denominator d E ≤ 4 ^ Fintype.card (U d E) ∧
    (∀ (s : U d E) (o : O), Clears (denominator d E)
      (Q.readout () ⟨S,O,d⟩ (.inl s.val,o)).toReal) ∧
    (∀ a ∈ E, ∀ o, Clears (denominator d E) (Q.readout () ⟨S,O,d⟩ (a,o)).toReal) ∧
    (∀ a ∈ E, ∑ o, Q.readout () ⟨S,O,d⟩ (a,o) = 1)

private theorem bad_invalid : ¬ arena.Law bad := by
  intro h
  let d : Empty → Instruction (Empty ⊕ Bool) := fun s => nomatch s
  have hn (a : Empty ⊕ Bool) : tapeLaw (never d a) = 0 := by
    have he : never d a = ∅ := by
      ext ω
      simp only [never,Set.mem_iInter,Set.mem_empty_iff_false,iff_false]
      intro hh
      obtain ⟨s,_⟩ := hh 0
      exact nomatch s
    rw [he,measure_empty]
  have hh := (h d univ (fun a _ => hn a)).2.2.2.2 (.inr true) (mem_univ _)
  simpa [bad,realize] using hh

def record : Registration arena (type_of% (@actual_exit_denominator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_exit_denominator,bad,bad_invalid⟩
  sensitivity := by
    letI : Subsingleton arena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    let d : Empty → Instruction (Empty ⊕ Bool) := fun s => nomatch s
    refine ⟨⟨Empty,Bool,d⟩,(.inr true,true),(.inr true,false),?_⟩
    simp only [actual,realize]
    rw [exits_exit,exits_exit]
    norm_num
    change (1 : ℝ≥0∞) ≠ 0
    exact one_ne_zero

def exitRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_exit_denominator) (type_of% (realize signature
      (fun _ C z => tapeLaw (exits C.d z.1 z.2)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator.actual_exit_denominator.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ C z => tapeLaw (exits C.d z.1 z.2)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def badHalf : Realization signature :=
  realize signature (fun _ _ _ => ENNReal.ofReal (1/2)) (fun e => nomatch e)
def chargedArena : Arena where
  signature := signature
  Law Q := ∀ {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    {p m a B : ℕ} (P : Program p a)
    (micro : Set (Snapshot p m a)) [Fintype micro]
    [MeasurableSpace micro] [MeasurableSingletonClass micro]
    (c : CompleteCodec P micro B) (d : micro → Instruction (micro ⊕ O))
    (E : Set (micro ⊕ O)) (hE : ∀ x ∈ E, tapeLaw (never d x) = 0),
    0 < denominator d E ∧ denominator d E ≤ 4 ^ (2 ^ B) ∧
    (∀ x ∈ E, ∀ o, Clears (denominator d E) (Q.readout () ⟨micro,O,d⟩ (x,o)).toReal)

private theorem half_invalid : ¬ chargedArena.Law badHalf := by
  intro h
  let P : Program 1 0 := ⟨fun _ => .finish,fun _ => none⟩
  let micro : Set (Snapshot 1 0 0) := ∅
  letI : IsEmpty micro := ⟨fun s => by simpa only [micro,Set.mem_empty_iff_false] using s.property⟩
  letI : Fintype micro := Fintype.ofIsEmpty
  letI : MeasurableSpace micro := ⊤
  letI : MeasurableSingletonClass micro := ⟨fun _ => trivial⟩
  let c : CompleteCodec P micro 0 := {
    encode := fun s => isEmptyElim s
    decode := fun _ => none
    roundtrip := fun s => isEmptyElim s }
  let d : micro → Instruction (micro ⊕ Bool) := fun s => isEmptyElim s
  have hn (x : micro ⊕ Bool) : tapeLaw (never d x) = 0 := by
    have he : never d x = ∅ := by
      ext ω
      simp only [never,Set.mem_iInter,Set.mem_empty_iff_false,iff_false]
      intro hh
      obtain ⟨s,_⟩ := hh 0
      exact isEmptyElim s
    rw [he,measure_empty]
  have hd : denominator d univ = 1 := by simp [denominator]
  have hh := (h P micro c d univ (fun x _ => hn x)).2.2 (.inr true) (mem_univ _) true
  change Clears (denominator d univ) (ENNReal.ofReal (1/2 : ℝ)).toReal at hh
  rw [hd] at hh
  obtain ⟨z,hz⟩ := hh
  norm_num [ENNReal.toReal_ofReal] at hz
  have hz1 : (z : ℝ) < 1 := by linarith
  have hzn : z < 1 := by exact_mod_cast hz1
  have hz0 : z = 0 := by omega
  rw [hz0] at hz
  norm_num at hz

def chargedRecord : Registration chargedArena (type_of% (@charged_exit_denominator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨charged_exit_denominator,badHalf,half_invalid⟩
  sensitivity := by
    letI : Subsingleton chargedArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨badHalf,?_,rfl,half_invalid⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := record.dependence

def chargedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_exit_denominator) (type_of% (realize signature
      (fun _ C z => tapeLaw (exits C.d z.1 z.2)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator.charged_exit_denominator.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator.chargedRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨chargedArena⟩, objectArena := .source ⟨chargedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source chargedArena ⟨chargedRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ C z => tapeLaw (exits C.d z.1 z.2)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator
