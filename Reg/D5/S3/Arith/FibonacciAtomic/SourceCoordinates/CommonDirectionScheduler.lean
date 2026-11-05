import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
import Reg.Support.DependentFamily

/-! # Full-family readouts for common-direction scheduling and binary execution -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
  (residueSource quantity replace terminalGcd costBound)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ H := (ZMod H × ZMod H) × List (ℕ × ℕ × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H v => schedule H (compiledReply H v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ((0, 0), [])) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ), 1 ≤ H → ∀ v : ℕ × ℕ,
    decode H (R.readout () H v).1 = residueSource H v ∧
    (R.readout () H v).1 =
      ((quantity (replace^[direction H] v) : ZMod H),
       (quantity (replace^[direction H + 1] v) : ZMod H)) ∧
    (R.readout () H v).2.length = (if H = 1 then 0 else 2 * costBound H) ∧
    ∀ t ∈ (R.readout () H v).2,
      (t.1 = direction H ∨ t.1 = direction H + 1) ∧ t.2.1 < H ∧
      (compile H t.1 t.2.1).count true = t.1 ∧
      (compile H t.1 t.2.1).count false ≤ graftBound H ∧
      t.2.2 = Nat.gcd (quantity (replace^[t.1] v) + t.2.1) H ∧
      t.2.2 = terminalGcd H (compile H t.1 t.2.1) v ∧
      ∀ current : ℕ × ℕ, residueSource H current = residueSource H v →
        ClosingCut H t.1 t.2.1 v current

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 2 (by decide) (0, 0)).2.2.1
  have hb : costBound 2 = 1 := by decide +kernel
  norm_num [rejected, realize, hb] at bad

def sourceRegistration : Registration arena
    (∀ (H : ℕ), 1 ≤ H → ∀ v : ℕ × ℕ,
    decode H (schedule H (compiledReply H v)).1 = residueSource H v ∧
    (schedule H (compiledReply H v)).1 =
      ((quantity (replace^[direction H] v) : ZMod H),
       (quantity (replace^[direction H + 1] v) : ZMod H)) ∧
    (schedule H (compiledReply H v)).2.length = (if H = 1 then 0 else 2 * costBound H) ∧
    ∀ t ∈ (schedule H (compiledReply H v)).2,
      (t.1 = direction H ∨ t.1 = direction H + 1) ∧ t.2.1 < H ∧
      (compile H t.1 t.2.1).count true = t.1 ∧
      (compile H t.1 t.2.1).count false ≤ graftBound H ∧
      t.2.2 = Nat.gcd (quantity (replace^[t.1] v) + t.2.1) H ∧
      t.2.2 = terminalGcd H (compile H t.1 t.2.1) v ∧
      ∀ current : ℕ × ℕ, residueSource H current = residueSource H v →
        ClosingCut H t.1 t.2.1 v current) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨effective_scheduler, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨2, (0, 0), (1, 0), ?_⟩
    change schedule 2 (compiledReply 2 (0, 0)) ≠ schedule 2 (compiledReply 2 (1, 0))
    intro h
    have hd := congrArg (fun s => decode 2 s.1) h
    rw [(effective_scheduler 2 (by decide) (0, 0)).1,
      (effective_scheduler 2 (by decide) (1, 0)).1] at hd
    have hx := congrArg Prod.fst hd
    norm_num [residueSource] at hx

def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@effective_scheduler) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler.informationUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H v => schedule H (compiledReply H v))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

abbrev binarySignature : Signature where
  Params := ℕ × (ℕ → ℕ) × ℕ
  State p := Joint p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := BinaryJoint p.1 × List (Binary × Binary)
  Anchor := Empty
  finiteAnchor := inferInstance

def binaryActual : Realization binarySignature :=
  realize binarySignature (fun _ p a => binaryRounds p.1
    (fun c => Nat.digits 2 (p.2.1 (Nat.ofDigits 2 c))) p.2.2 (encodeJoint p.1 a))
    (fun e => nomatch e)

def binaryRejected : Realization binarySignature :=
  realize binarySignature (fun _ _ _ => ([], [])) (fun e => nomatch e)

abbrev binaryArena : Arena where
  signature := binarySignature
  Law R := ∀ (H : ℕ) (answer : ℕ → ℕ) (j : ℕ) (a : Joint H),
    R.readout () (H, answer, j) a =
      (encodeJoint H (rounds H answer j a).1,
        (rounds H answer j a).2.map (fun t => (Nat.digits 2 t.1, Nat.digits 2 t.2))) ∧
    decodeJoint H (encodeJoint H a) = a ∧
    (encodeJoint H a).length = H.primeFactors.card ∧
    (∀ n d, d ∈ Nat.digits 2 n → d < 2)

private theorem binaryRejected_law : ¬ binaryArena.Law binaryRejected := by
  intro h
  have hb := (h 2 (fun _ => 0) 0 (fun _ => initialAxis)).1
  have hl := congrArg (fun s => s.1.length) hb
  change 0 = (encodeJoint 2 (fun _ => initialAxis)).length at hl
  have hcard : (2 : ℕ).primeFactors.card = 1 := by decide +kernel
  simp [encodeJoint, hcard] at hl

def binarySourceRegistration : Registration binaryArena
    (∀ (H : ℕ) (answer : ℕ → ℕ) (j : ℕ) (a : Joint H),
    binaryRounds H (fun c => Nat.digits 2 (answer (Nat.ofDigits 2 c))) j
      (encodeJoint H a) =
    (encodeJoint H (rounds H answer j a).1,
      (rounds H answer j a).2.map (fun t => (Nat.digits 2 t.1, Nat.digits 2 t.2))) ∧
    decodeJoint H (encodeJoint H a) = a ∧
    (encodeJoint H a).length = H.primeFactors.card ∧
    (∀ n d, d ∈ Nat.digits 2 n → d < 2)) where
  actual := binaryActual
  bridge := Iff.rfl
  variation := ⟨finite_binary_execution, binaryRejected, binaryRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨binaryRejected, ?_, rfl, binaryRejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(2, (fun _ => 0), 0), (fun _ => initialAxis),
      (fun _ => (⟨1, 0, 0⟩ : Axis)), ?_⟩
    intro h
    have hd := congrArg (fun s => decodeJoint 2 s.1) h
    change decodeJoint 2 (encodeJoint 2 (fun _ => initialAxis)) =
      decodeJoint 2 (encodeJoint 2 (fun _ => (⟨1, 0, 0⟩ : Axis))) at hd
    rw [(finite_binary_execution 2 (fun _ => 0) 0 _).2.1,
      (finite_binary_execution 2 (fun _ => 0) 0 _).2.1] at hd
    have hx := congrArg (fun a => (a ⟨2, Nat.prime_two.mem_primeFactors_self⟩).level) hd
    change 0 = 1 at hx
    omega

def binaryRegistration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@finite_binary_execution) (Realization binarySignature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler.binaryInformationUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler.binarySourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨binaryArena⟩
  objectArena := .source ⟨binaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source binaryArena ⟨binarySourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize binarySignature (fun _ p a => binaryRounds p.1
    (fun c => Nat.digits 2 (p.2.1 (Nat.ofDigits 2 c))) p.2.2 (encodeJoint p.1 a))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms sourceRegistration
#print axioms binarySourceRegistration
#print axioms registration
#print axioms binaryRegistration

end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
