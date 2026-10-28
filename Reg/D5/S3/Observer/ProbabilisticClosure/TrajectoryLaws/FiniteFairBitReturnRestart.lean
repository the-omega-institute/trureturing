import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
local instance {A : Type} : MeasurableSpace (Option A) := ⊤
local instance {A : Type} : MeasurableSingletonClass (Option A) := ⟨fun _ => trivial⟩

structure Family where
  S : Type
  O : Type
  d : S → Instruction (S ⊕ O)
  a : S ⊕ O
abbrev signature : Signature where
  Params := Family
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := Option C.O × (ℕ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ C ω => restart C.d C.a ω) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ ω => (none,ω)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (a : S ⊕ O) (ha : tapeLaw (never d a) = 0),
    Measurable (fun ω => Q.readout () ⟨S,O,d,a⟩ ω) ∧
    tapeLaw.map (fun ω => Q.readout () ⟨S,O,d,a⟩ ω) =
      (tapeLaw.map (fun ω => (Q.readout () ⟨S,O,d,a⟩ ω).1)).prod tapeLaw ∧
    (∀ o, {ω | (Q.readout () ⟨S,O,d,a⟩ ω).1 = some o} = exits d a o) ∧
    (∀ (ω : ℕ → Bool) (n : ℕ) (o : O), ω ∈ hit d a n o →
      Q.readout () ⟨S,O,d,a⟩ ω =
        (some o,fun k => ω (k + requests (stopped d) a ω n)))

private theorem empty_return (a : Empty ⊕ Bool)
    (d : Empty → Instruction (Empty ⊕ Bool)) : tapeLaw (never d a) = 0 := by
  have he : never d a = ∅ := by
    ext ω
    simp only [never,mem_iInter,mem_empty_iff_false,iff_false]
    intro h
    obtain ⟨s,_⟩ := h 0
    exact nomatch s
  rw [he,measure_empty]

private theorem bad_invalid : ¬ arena.Law bad := by
  intro h
  let d : Empty → Instruction (Empty ⊕ Bool) := fun s => nomatch s
  have hh := (h d (.inr true) (empty_return _ d)).2.2.1 true
  have he : (∅ : Set (ℕ → Bool)) = univ := by
    simpa [bad,realize,exits_exit] using hh
  exact Set.empty_ne_univ he

def record : Registration arena (type_of% (@actual_return_restart)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_return_restart,bad,bad_invalid⟩
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
    have hr (ω : ℕ → Bool) : restart d (.inr true) ω = (some true,ω) := by
      have h := (actual_return_restart d (.inr true) (empty_return _ d)).2.2.2 ω 0 true
        ⟨rfl,by simp⟩
      simpa only [requests,Nat.add_zero] using h
    refine ⟨⟨Empty,Bool,d,.inr true⟩,(fun _ => false),(fun _ => true),?_⟩
    simp only [actual,realize,hr]
    intro h
    have hh := congrFun (congrArg Prod.snd h) 0
    cases hh

def returnRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_return_restart) (type_of% (realize signature
      (fun _ C ω => restart C.d C.a ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart.actual_return_restart.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ C ω => restart C.d C.a ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

structure PrefixFamily where
  S : Type
  O : Type
  d : S → Instruction (S ⊕ O)
  entrance : O → S ⊕ O
  s : O
abbrev prefixSignature : Signature where
  Params := PrefixFamily
  State C := List C.O × Set (ℕ → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance
def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ C p => tapeLaw
    {ω | ∃ σ ∈ p.2, services C.d C.entrance C.s ω p.1.length = some (p.1,σ)})
    (fun e => nomatch e)
def prefixBad : Realization prefixSignature :=
  realize prefixSignature (fun _ _ _ => 0) (fun e => nomatch e)
def prefixArena : Arena where
  signature := prefixSignature
  Law Q := ∀ {S O : Type} [Fintype S] [Fintype O]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (d : S → Instruction (S ⊕ O)) (entrance : O → S ⊕ O)
    (ha : ∀ s, tapeLaw (never d (entrance s)) = 0) (s : O) (w : List O)
    (E : Set (ℕ → Bool)) (hE : MeasurableSet E),
    Q.readout () ⟨S,O,d,entrance,s⟩ (w,E) = prefixMass d entrance s w * tapeLaw E
private theorem prefix_bad_invalid : ¬ prefixArena.Law prefixBad := by
  intro h
  let d : Empty → Instruction (Empty ⊕ Bool) := fun s => nomatch s
  have hh := h d Sum.inr (fun s => empty_return (.inr s) d) false [] univ MeasurableSet.univ
  simpa [prefixBad,realize,prefixMass] using hh
def prefixRecord : Registration prefixArena (type_of% (@repeated_service_prefix)) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨repeated_service_prefix,prefixBad,prefix_bad_invalid⟩
  sensitivity := by
    letI : Subsingleton prefixArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨prefixBad,?_,rfl,prefix_bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    let d : Empty → Instruction (Empty ⊕ Bool) := fun s => nomatch s
    refine ⟨⟨Empty,Bool,d,Sum.inr,false⟩,([],∅),([],univ),?_⟩
    simp [prefixActual,realize,services]
    change (0 : ℝ≥0∞) ≠ 1
    exact zero_ne_one

def prefixRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_service_prefix) (type_of% (realize prefixSignature
      (fun _ C p => tapeLaw {ω | ∃ σ ∈ p.2,
        services C.d C.entrance C.s ω p.1.length = some (p.1,σ)})
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart.repeated_service_prefix.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart.prefixRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨prefixArena⟩, objectArena := .source ⟨prefixArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source prefixArena ⟨prefixRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize prefixSignature (fun _ C p => tapeLaw
    {ω | ∃ σ ∈ p.2, services C.d C.entrance C.s ω p.1.length = some (p.1,σ)})
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitReturnRestart
