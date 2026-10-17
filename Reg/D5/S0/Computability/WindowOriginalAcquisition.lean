import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Computability.WindowOriginalAcquisition

namespace Reg.D5.S0.Computability.WindowOriginalAcquisition
open PhysicalWindowContinuation PhysicalWindowContinuation.CanonicalAcquisition
open PhysicalWindowContinuation.RegisterHandoff
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Config
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p n => CanonicalAcquisition.run
    (CanonicalAcquisition.initial (OriginalEncoder.localWord p.1 p.2) (OriginalEncoder.bit p.2 0)) n)
  (fun e => nomatch e)

def stopped : Realization signature := realize signature
  (fun _ p _ => CanonicalAcquisition.initial (OriginalEncoder.localWord p.1 p.2) (OriginalEncoder.bit p.2 0))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    Function.Injective (finiteCode (α := Symbol)) ∧
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧
    ∀ (h N : ℕ), 1 ≤ N → OriginalEncoder.L N ≤ h →
    let w := OriginalEncoder.localWord h N
    let e := OriginalEncoder.bit N 0
    ∃ T : ℕ, T ≤ A*(h+1)^2 ∧
      R.readout () ⟨h,N⟩ T = registerEnd w e ∧
      CanonicalAcquisition.program (registerEnd w e).control = .halt ∧
      RegisterRep (registerEnd w e) 0 (value1 (Original.finalColumns w e)) ∧
      RegisterRep (registerEnd w e) 1 (value2 (Original.finalColumns w e)) ∧
      RegisterRep (registerEnd w e) 2 h ∧
      RegisterRep (registerEnd w e) 3 N ∧
      Original.pair (Original.finalColumns w e) =
        NativeContinuation.JointLaw.composition (OriginalEncoder.W h N) ∧
      Original.pair (Original.finalColumns w e) = Original.columnSum w ∧
      Original.maximumColumn [] = 0 ∧
      (∀ b, Original.maximumColumn (w ++ [b]) ≤ 5*Original.maximumColumn w+2) ∧
      2*Original.maximumColumn w+1 ≤ 5^h ∧
      Original.maximumColumn w ≤ (5^h-1)/2 ∧
      N < Nat.fib (3*h+3) ∧
      (∀ n ≤ T, charged w e n ≤ B*(h+1)) ∧
      (∀ n ≤ T, ∀ t, 0 ≤ (CanonicalAcquisition.run (CanonicalAcquisition.initial w e) n).head t ∧
        (CanonicalAcquisition.run (CanonicalAcquisition.initial w e) n).head t ≤ 3*h+6) ∧
      (∀ n, (CanonicalAcquisition.run (CanonicalAcquisition.initial w e) n).cell sourceTrack=inputSource w e) ∧
      (registerEnd w e).cell workTrack=word (Original.finalColumns w e) ∧
      (∀ t : Track,(∀ j : Lane,t ≠ target j) → t ≠ sourceTrack → t ≠ workTrack →
        (registerEnd w e).cell t=fun _=>.blank) ∧
      (∀ t : Track,(registerEnd w e).head t=if t=sourceTrack then h else 0) ∧
      (∀ j : Lane,(normalized ((Original.finalColumns w e).map (select j))).length ≤
        (Original.finalColumns w e).length+1) ∧
      (∀ pre suf : List Window, pre++suf=w →
        ∃ q : ℕ, q ≤ T ∧ q ≤ 4+pre.length*(15*h+46) ∧
          CanonicalAcquisition.run (CanonicalAcquisition.initial w e) q =
            base (boundary (inputSource w e) pre.length
              (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) ∧
          Original.pair (columnsAfter [zeros] pre) =
            NativeContinuation.JointLaw.composition (pre.map Original.letter) ∧
          valueCount (columnsAfter [zeros] pre) = pre.length ∧
          (columnsAfter [zeros] pre).length ≤ 1+3*pre.length)

private theorem faithful : arena.Law actual := original_window_acquisition

private theorem unit_indices : _root_.D5.S0.Conventions.wdigits 1=[2] := by
  symm
  apply _root_.D5.S0.Conventions.wdigits_unique
  · simp [List.IsZeckendorfRep]
  · decide

private theorem stopped_fails : ¬ arena.Law stopped := by
  intro bad
  obtain ⟨_,A,B,hA,hB,hall⟩ := bad
  have hl : OriginalEncoder.L 1=0 := by
    simp [OriginalEncoder.L,
      _root_.D5.S1.Digit.GoldenBase4AutomataOracle.zeckendorfWordLength,unit_indices]
  obtain ⟨T,hT,he,rest⟩ := hall 0 1 (by decide) (by rw [hl])
  have hc := congrArg Config.control he
  simp [stopped,realize,CanonicalAcquisition.initial,registerEnd,port,startAt,base,
    PhysicalWindowContinuation.initial] at hc

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0,1⟩,0,1,?_⟩
  intro he
  have hc := congrArg Config.control he
  simp [actual,realize,CanonicalAcquisition.run,CanonicalAcquisition.initial,
    CanonicalAcquisition.step,CanonicalAcquisition.program,baseAction,
    PhysicalWindowContinuation.program,PhysicalWindowContinuation.initial,base] at hc

def family : Registration arena (type_of% original_window_acquisition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨faithful,stopped,stopped_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stopped,?_,?_,stopped_fails⟩
      · intro other ho
        cases role; cases other
        exact (ho rfl).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := actual_dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    original_window_acquisition
    (Realization signature) Type Unit := {
  unitName := `PhysicalWindowContinuation.CanonicalAcquisition.original_window_acquisition.__information_unit
  realizationName := `Reg.D5.S0.Computability.WindowOriginalAcquisition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial)
  readout := some (realize signature
    (fun _ p n => CanonicalAcquisition.run
    (CanonicalAcquisition.initial (OriginalEncoder.localWord p.1 p.2) (OriginalEncoder.bit p.2 0)) n)
    (fun e => nomatch e))
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial)
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial)
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.WindowOriginalAcquisition
    definition := none
    coordinates := #[2,3]
    readouts := #[{
      path := #["arg","arg","body","arg","body","arg","arg","body","body","body",
        "body","body","body","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S0.Computability.WindowOriginalAcquisition
