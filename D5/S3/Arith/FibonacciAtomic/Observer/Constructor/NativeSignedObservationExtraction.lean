/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.entire_input_extraction; instance=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSignedObservationExtraction.endpoint
   digest: Exact signed mixed-epoch extraction with complete original row records. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

/-! Finite signed observations retain the whole original source and both complete rows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSignedObservationExtraction

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery (CutSet CutPrefixFree)
open ActualCutPartitionDecoder (HoleExterior literalRecord)
open NativeGroundSeparation (Term evaluate)
open NativeSymbolicRecutting (DeepAt symbolicRecord symbolic_recut_exact)
open NativePrefixIdentityReflection (MixedExpr eval)
open NativeSimultaneousPrefixSeparation (shift eval_shift)
open NativeDepthPatterns (Pattern Frontier fill depthEquiv)
open NativePayloadHistoryInstallation (Record)
open NativeFiveHoleFiber (NegativeRecord Negative GuardedEqual)

/-- Keep every variable name and every native ground leaf. -/
def mixed {X : Type} : Term X → MixedExpr X
  | .of (.inl b) => .ground (.of b)
  | .of (.inr x) => .residual 0 x
  | .mul l r => .pair (mixed l) (mixed r)

private theorem mixed_value {X : Type} (v : X → Source) (t : Term X) :
    eval v (mixed t) = evaluate v t := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r ihl ihr => exact congrArg₂ FreeMagma.mul ihl ihr

/-- Navigate the original skeleton, evolving an early ground leaf explicitly.
A proper descent into an unspecified frontier is rejected. -/
def endpoint {X : Type} (epoch : Nat) : Address → Term X → Option (MixedExpr X)
  | [], t => some (shift epoch (mixed t))
  | b :: p, .of (.inl c) => (subtree (b :: p) (substitution^[epoch] (.of c))).map .ground
  | _ :: _, .of (.inr _) => none
  | false :: p, .mul l _ => endpoint epoch p l
  | true :: p, .mul _ r => endpoint epoch p r

private theorem endpoint_exact {X : Type} (d : Nat) (a p : Address) (t : Term X)
    (deep : DeepAt d a t) (bound : a.length + p.length < d)
    (epoch : Nat) (v : X → Source) :
    (endpoint epoch p t).map (eval v) = subtree p (substitution^[epoch] (evaluate v t)) := by
  induction p generalizing a t with
  | nil => simp only [endpoint, Option.map_some, eval_shift, mixed_value, subtree]
  | cons b p ih =>
      cases t with
      | of c => cases c with
        | inl c =>
            change ((subtree (b :: p) (substitution^[epoch] (.of c))).map
              (fun g => MixedExpr.ground g)).map (eval v) =
                subtree (b :: p) (substitution^[epoch] (.of c))
            cases subtree (b :: p) (substitution^[epoch] (.of c)) <;> rfl
        | inr x => simp only [DeepAt] at deep; simp only [List.length_cons] at bound; omega
      | mul l r =>
          have bd : (a ++ [b]).length + p.length < d := by
            simp only [List.length_append, List.length_cons, List.length_nil] at *
            omega
          have pair := Function.Semiconj₂.iterate
            (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
              fun s t => substitution.map_mul s t) epoch (evaluate v l) (evaluate v r)
          change _ = subtree (b :: p) (substitution^[epoch] (.mul (evaluate v l) (evaluate v r)))
          rw [pair]
          cases b
          · exact ih (a ++ [false]) l deep.1 bd
          · exact ih (a ++ [true]) r deep.2 bd

/-- True selects equality; false selects disequality of the entire values. -/
abbrev Constraint (X : Type) := Bool × MixedExpr X × MixedExpr X

def ConstraintHolds {X : Type} (v : X → Source) (c : Constraint X) : Prop :=
  if c.1 then eval v c.2.1 = eval v c.2.2 else eval v c.2.1 ≠ eval v c.2.2

/-- None is an impossible guarded branch; some [] is the empty conjunction. -/
abbrev Program (X : Type) := Option (List (Constraint X))

def ProgramHolds {X : Type} (v : X → Source) (program : Program X) : Prop :=
  ∃ cs, program = some cs ∧ ∀ c ∈ cs, ConstraintHolds v c

def appendProgram {X : Type} (left right : Program X) : Program X :=
  match left, right with
  | some l, some r => some (l ++ r)
  | _, _ => none

private theorem append_exact {X : Type} (v : X → Source) (left right : Program X) :
    ProgramHolds v (appendProgram left right) ↔
      ProgramHolds v left ∧ ProgramHolds v right := by
  cases left <;> cases right <;>
    simp only [appendProgram, ProgramHolds, Option.some.injEq, reduceCtorEq,
      false_and, exists_false, exists_eq_right, and_false, List.forall_mem_append]

def compileList {X Y : Type} (compile : Y → Program X) : List Y → Program X
  | [] => some []
  | y :: ys => appendProgram (compile y) (compileList compile ys)

private theorem list_exact {X Y : Type} (compile : Y → Program X) (v : X → Source)
    (ys : List Y) : ProgramHolds v (compileList compile ys) ↔
      ∀ y ∈ ys, ProgramHolds v (compile y) := by
  induction ys with
  | nil => simp [compileList, ProgramHolds]
  | cons y ys ih => rw [compileList, append_exact, ih, List.forall_mem_cons]

/-- Both endpoints are computed before either comparison sign is accepted. -/
def comparison {X : Type} (t : Term X) (sign : Bool)
    (a : Nat) (p : Address) (b : Nat) (q : Address) : Program X :=
  match endpoint a p t, endpoint b q t with
  | some E, some F => some [(sign,E,F)]
  | _, _ => none

private theorem comparison_exact {X : Type} (d : Nat) (t : Term X)
    (deep : DeepAt d [] t) (v : X → Source) (sign : Bool)
    (a : Nat) (p : Address) (b : Nat) (q : Address)
    (hp : p.length < d) (hq : q.length < d) :
    ProgramHolds v (comparison t sign a p b q) ↔
      (subtree p (substitution^[a] (evaluate v t))).isSome ∧
      (subtree q (substitution^[b] (evaluate v t))).isSome ∧
      (if sign then subtree p (substitution^[a] (evaluate v t)) =
          subtree q (substitution^[b] (evaluate v t))
       else subtree p (substitution^[a] (evaluate v t)) ≠
          subtree q (substitution^[b] (evaluate v t))) := by
  rw [← endpoint_exact d [] p t deep (by simpa using hp) a v,
    ← endpoint_exact d [] q t deep (by simpa using hq) b v]
  cases hE : endpoint a p t <;> cases hF : endpoint b q t <;> cases sign <;>
    simp [comparison, hE, hF, ProgramHolds, ConstraintHolds]

def recordAddresses : Record → List Address
  | .literal _ p _ => [p]
  | .positive _ p _ q => [p,q]

def negativeAddresses (e : NegativeRecord) : List Address := [e.2.1,e.2.2.2]

/-- Literals are tested on one filling only after prefix locality is available. -/
def compileRecord {X : Type} (t : Term X) : Record → Program X
  | .literal a p y =>
      if readout p (substitution^[a] (evaluate (fun _ => .of true) t)) = y
      then some [] else none
  | .positive a p b q => comparison t true a p b q

def compileNegative {X : Type} (t : Term X) (e : NegativeRecord) : Program X :=
  comparison t false e.1 e.2.1 e.2.2.1 e.2.2.2

private theorem record_exact {X : Type} (d : Nat) (t : Term X)
    (deep : DeepAt d [] t) (v : X → Source) (r : Record)
    (bound : ∀ p ∈ recordAddresses r, p.length < d) :
    ProgramHolds v (compileRecord t r) ↔ r.Holds (evaluate v t) := by
  cases r with
  | literal a p y =>
      have same := NativeSymbolicRecutting.symbolic_history_constant d t deep [(a,p,y)]
        (by simpa [recordAddresses] using bound p (by simp [recordAddresses]))
        (fun _ => .of true) v
      simp only [NativeDepthPatterns.Consistent, List.forall_mem_singleton] at same
      change _ ↔ readout p (substitution^[a] (evaluate v t)) = y
      rw [← same]
      by_cases h : readout p (substitution^[a] (evaluate (fun _ => .of true) t)) = y <;>
        simp [compileRecord, h, ProgramHolds]
  | positive a p b q =>
      exact comparison_exact d t deep v true a p b q
        (bound p (by simp [recordAddresses])) (bound q (by simp [recordAddresses]))

private theorem negative_exact {X : Type} (d : Nat) (t : Term X)
    (deep : DeepAt d [] t) (v : X → Source) (e : NegativeRecord)
    (bound : ∀ p ∈ negativeAddresses e, p.length < d) :
    ProgramHolds v (compileNegative t e) ↔ Negative e (evaluate v t) :=
  comparison_exact d t deep v false e.1 e.2.1 e.2.2.1 e.2.2.2
    (bound _ (by simp [negativeAddresses])) (bound _ (by simp [negativeAddresses]))

abbrev Row := HoleExterior × Finset (Address × Address)

/-- All supplied records and both complete rows concern one original source. -/
def InputHolds (P Q : CutSet) (old target : Row) (H : List Record)
    (K : List NegativeRecord) (u : Source) : Prop :=
  literalRecord P u = old ∧ NativePayloadHistoryInstallation.Holds u H ∧
    (∀ e ∈ K, Negative e u) ∧ literalRecord Q u = target

/-- Rows retain their concrete exterior and every reached partition pair.
They have not yet been eliminated into a positive native image chart. -/
def ExtractedHolds {X : Type} (P Q : CutSet) (old target : Row) (H : List Record)
    (K : List NegativeRecord) (t : Term X) (v : X → Source) : Prop :=
  symbolicRecord P t v = old ∧ ProgramHolds v (compileList (compileRecord t) H) ∧
    ProgramHolds v (compileList (compileNegative t) K) ∧ symbolicRecord Q t v = target

def requests (P Q : CutSet) (H : List Record) (K : List NegativeRecord) : Finset Address :=
  P ∪ Q ∪ (H.flatMap recordAddresses).toFinset ∪ (K.flatMap negativeAddresses).toFinset

/-- Epoch magnitudes do not affect the required original prefix depth. -/
def requiredDepth (P Q : CutSet) (H : List Record) (K : List NegativeRecord) : Nat :=
  (requests P Q H K).sup List.length + 1

private theorem request_bound (P Q : CutSet) (H : List Record) (K : List NegativeRecord)
    (p : Address) (hp : p ∈ requests P Q H K) : p.length < requiredDepth P Q H K :=
  Nat.lt_succ_of_le (Finset.le_sup hp)

private theorem extracted_exact {X : Type} (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (old target : Row) (H : List Record) (K : List NegativeRecord)
    (t : Term X) (deep : DeepAt (requiredDepth P Q H K) [] t) (v : X → Source) :
    ExtractedHolds P Q old target H K t v ↔ InputHolds P Q old target H K (evaluate v t) := by
  let d := requiredDepth P Q H K
  have bp : ∀ p ∈ P, p.length < d := fun p hp =>
    request_bound P Q H K p (by simp [requests, hp])
  have bq : ∀ q ∈ Q, q.length < d := fun q hq =>
    request_bound P Q H K q (by simp [requests, hq])
  have bh : ∀ r ∈ H, ∀ p ∈ recordAddresses r, p.length < d := by
    intro r hr p hp
    apply request_bound P Q H K p
    simp only [requests, Finset.mem_union, List.mem_toFinset, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨r,hr,hp⟩)
  have bk : ∀ e ∈ K, ∀ p ∈ negativeAddresses e, p.length < d := by
    intro e he p hp
    apply request_bound P Q H K p
    simp only [requests, Finset.mem_union, List.mem_toFinset, List.mem_flatMap]
    exact Or.inr ⟨e,he,hp⟩
  have pe := (symbolic_recut_exact d P hP bp t deep v).2.2.2
  have qe := (symbolic_recut_exact d Q hQ bq t deep v).2.2.2
  simp only [ExtractedHolds, InputHolds, ← pe, ← qe, list_exact,
    NativePayloadHistoryInstallation.Holds]
  exact and_congr Iff.rfl (and_congr
    (forall_congr' fun r => forall_congr' fun hr => record_exact d t deep v r (bh r hr))
    (and_congr
      (forall_congr' fun e => forall_congr' fun he => negative_exact d t deep v e (bk e he))
      Iff.rfl))

/-- A finite, input-computed pattern family covers exactly the entire signed
fiber and reconstructs each original as itself, without any size bound. -/
theorem entire_input_extraction (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (old target : Row) (H : List Record) (K : List NegativeRecord)
    (u : Source) :
    InputHolds P Q old target H K u ↔
      ∃ p : Pattern (requiredDepth P Q H K), ∃ v : Frontier p → Source,
        fill p v = u ∧ ExtractedHolds P Q old target H K
          (NativeHistoryCells.patternTerm p id) v := by
  let d := requiredDepth P Q H K
  have exact_pattern (p : Pattern d) (v : Frontier p → Source) :
      ExtractedHolds P Q old target H K (NativeHistoryCells.patternTerm p id) v ↔
        InputHolds P Q old target H K (fill p v) := by
    have deep := NativeHistoryCells.pattern_deep d d p id [] (by simp)
    simpa only [NativeHistoryCells.pattern_evaluate, Function.comp_id] using
      extracted_exact P Q hP hQ old target H K _ deep v
  constructor
  · intro hu
    let x := depthEquiv d u
    have recover : fill x.1 x.2 = u := (depthEquiv d).left_inv u
    refine ⟨x.1,x.2,recover,(exact_pattern x.1 x.2).mpr ?_⟩
    rwa [recover]
  · rintro ⟨p,v,recover,hv⟩
    rw [← recover]
    exact (exact_pattern p v).mp hv

#print axioms entire_input_extraction

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSignedObservationExtraction
