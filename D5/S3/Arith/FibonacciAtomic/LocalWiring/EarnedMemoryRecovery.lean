/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/EarnedMemoryRecovery
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/EarnedMemoryRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four exact law-ready recovery routes and the finite code selected from earned bits. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition

/-! Actual mature-cut data recovery with completed finite memory and fixed live binding. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery

open AttainedPrefixAcquisition LocalTwoStepRecognizer KnownSeedCurrentFibers
open PhysicalBirthClock OrderedBirthPrefix PublicRowSeedReadiness LawfulSourceReadiness
open NativePastAcquisitionBarrier

/-- The exact finite code chosen by the shipped synthesis on the earned word. -/
inductive Code
  | binary (d : Nat) (coeff seed : Fin d → Bool)
  | moore (table : Sigma UnaryMooreSeparation.Table)
  | row (r : Nat) (coeff seed : Fin r → Bool)

def Code.eval : Code → OutputStream
  | .binary _ c seed | .row _ c seed => rowStream c seed
  | .moore t => t.2.machine.emit

def reify : Promise → List Bool → Option Code
  | .lawful (.binary d), word =>
    let xs := word.take (2 * d)
    (BoundedBinaryRecurrence.synthesize d xs).map fun c => .binary d c (seedFromPrefix xs)
  | .lawful (.moore K), word =>
    (UnaryMooreSeparation.synthesize K (word.take (2 * K - 1))).map Code.moore
  | .row r c, word => some (.row r c (seedFromPrefix word))

theorem reify_eval (P : Promise) (word : List Bool) :
    (reify P word).map Code.eval = generate P word := by
  cases P with
  | row r c => rfl
  | lawful C =>
    cases C with
    | binary d =>
      change ((BoundedBinaryRecurrence.synthesize d (word.take (2 * d))).map _).map Code.eval =
        (BoundedBinaryRecurrence.synthesize d (word.take (2 * d))).map _
      rw [Option.map_map]
      rfl
    | moore K =>
      change ((UnaryMooreSeparation.synthesize K (word.take (2 * K - 1))).map _).map Code.eval =
        (UnaryMooreSeparation.synthesize K (word.take (2 * K - 1))).map _
      rw [Option.map_map]
      rfl

/-- Replay starts from alpha and consumes only the supplied finite mark word. -/
def replayMarks (n : Nat) (marks : List Bool) : BirthRun :=
  physicalBirthClock (extendBits marks) n

/-- Rebuild every event field by running the clock, not by copying event metadata. -/
def replayBirthRecord (n : Nat) (events : List BirthEvent) : BirthRun :=
  replayMarks n (events.map BirthEvent.mark)

private theorem native_record_marks (z : BirthStream) (n : Nat) :
    (physicalBirthClock z n).births.map BirthEvent.mark = prefixBits z (clockSum n) := by
  have h := physical_birth_clock z n
  have hn := h.2.2.2.2.1
  apply List.ext_getElem
  · simpa [prefixBits] using hn
  · intro i hi _
    have hb : i < (physicalBirthClock z n).births.length := by simpa using hi
    have he := (h.1 i _ (List.getElem?_eq_getElem hb)).1
    simpa [prefixBits] using he.symm

private theorem replayMarks_exact (z : BirthStream) (n : Nat) :
    replayMarks n (prefixBits z (clockSum n)) = physicalBirthClock z n := by
  have h := physical_birth_clock z n
  have hc := h.2.2.2.1.trans h.2.2.2.2.1
  apply (h.2.2.2.2.2.2.2.2.2.2 _ ?_).symm
  intro j hj hJ
  have hi : j - 1 < clockSum n := by omega
  simp [extendBits, prefixBits, hi, consume, Nat.sub_add_cancel hj]

theorem replayBirthRecord_exact (z : BirthStream) (n : Nat) :
    replayBirthRecord n (physicalBirthClock z n).births = physicalBirthClock z n := by
  rw [replayBirthRecord, native_record_marks, replayMarks_exact]

/-- The finite data view, separate from the live binding and any audit journal. -/
structure Memory where
  word : List Bool
  code : Code
  cut : Nat
  cursor : Nat

/-- Readable owned backing for the selected data, with a separately held binding.
No write below creates, changes, or certifies that binding. -/
structure Backing (Binding : Type) where
  binding : Binding
  word : Option (List Bool)
  code : Option Code
  cut : Option Nat
  cursor : Option Nat

/-- Ordinary finite writes of the selected fields. -/
inductive StoreWrite
  | word (value : List Bool)
  | code (value : Code)
  | cut (value : Nat)
  | cursor (value : Nat)

/-- One local write cannot invent a root, grant or invocation right. -/
def applyWrite {Binding : Type} (b : Backing Binding) : StoreWrite → Backing Binding
  | .word w => {b with word := some w}
  | .code c => {b with code := some c}
  | .cut n => {b with cut := some n}
  | .cursor j => {b with cursor := some j}

def memoryWrites (m : Memory) : List StoreWrite :=
  [.word m.word, .code m.code, .cut m.cut, .cursor m.cursor]

/-- Interpretation of the actual finite write sequence on the specified backing. -/
def writeMemory {Binding : Type} (b : Backing Binding) (m : Memory) : Backing Binding :=
  (memoryWrites m).foldl applyWrite b

def Backing.read {Binding : Type} (b : Backing Binding) : Option Memory := do
  let word ← b.word
  let code ← b.code
  let cut ← b.cut
  let cursor ← b.cursor
  pure ⟨word, code, cut, cursor⟩

/-- Install only from the actual terminal register after acquisition; its finite code
is the canonical reification of the literal earned word, not a private machine. -/
def installStopped {Binding : Type} (P : Promise) (b : Backing Binding)
    (r : Record Register) : Option (Backing Binding) :=
  if r.stopped then
    match r.register.1 with
    | .stop word result => (reify P word).map fun code =>
        writeMemory b ⟨word, code, r.cut, result.nextIndex⟩
    | _ => none
  else none

/-- Genuine completed backing plus the external live root and rights at this cut.
No mathematical recovery function proves the supplied service predicate. -/
def HoldsAt {Binding : Type} (Live : Binding → OutputStream → Nat → Prop)
    (source : Binding) (s : OutputStream) (b : Backing Binding) (m : Memory) : Prop :=
  b.binding = source ∧ Live source s m.cut ∧ b.read = some m

/-- The common data recovered by all routes, with actual tasks kept distinct from
the observable transcript under the native service. -/
structure Bundle where
  memory : Memory
  incidence : List Address
  frontier : List Address
  births : List BirthEvent
  labelled : Labelled
  next : Address → Bool
  behavior : FutureBehavior

def direct (s : OutputStream) (m : Memory) : Bundle :=
  ⟨m, acquired .incidence m.cut s, acquired .frontier m.cut s,
    (physicalBirthClock (birthOf s) m.cut).births, physicalTree m.cut s,
    fun p => queryNext m.cut p s, future m.cut s⟩

inductive View
  | incidence (addresses : List Address)
  | frontier (addresses : List Address)
  | chronology (cut : Nat) (births : List BirthEvent)
  | earned (memory : Memory)

inductive ViewKind
  | incidence
  | frontier
  | chronology
  | earned

def project (b : Bundle) : ViewKind → View
  | .incidence => .incidence b.incidence
  | .frontier => .frontier b.frontier
  | .chronology => .chronology b.memory.cut b.births
  | .earned => .earned b.memory

/-- Recover directly from the completed memory, using the saved generator and counters
without any paid query. Inconsistent scalar counters do not certify a run. -/
def fromMemory (m : Memory) : Option Bundle :=
  if m.cursor = clockSum m.cut then some (direct m.code.eval m) else none

def fromMature (P : Promise) (p : Nat × List Bool) : Option Bundle := do
  let word := p.2.take P.target
  let code ← reify P word
  fromMemory ⟨word, code, p.1, clockSum p.1⟩

def recoverIncidence (P : Promise) (addresses : List Address) : Option Bundle :=
  ((shapeFromIncidence addresses).bind maturePrefix).bind (fromMature P)

def recoverFrontier (P : Promise) (addresses : List Address) : Option Bundle :=
  ((shapeFromFrontier addresses).bind maturePrefix).bind (fromMature P)

/-- Each attained view is decoded by its own concrete algorithm before projection. -/
def recover (P : Promise) : View → Option Bundle
  | .incidence xs => recoverIncidence P xs
  | .frontier xs => recoverFrontier P xs
  | .chronology n es =>
    recoverIncidence P (incidenceAddresses (shape (replayBirthRecord n es).tree))
  | .earned m => fromMemory m

def convert (P : Promise) (v : View) (kind : ViewKind) : Option View :=
  (recover P v).map fun b => project b kind

private theorem stable_mature (n e : Nat) (h : n ≤ e) : matureSize n ≤ matureSize e := by
  apply (show Monotone clockSum by
    apply monotone_nat_of_le_succ
    intro j
    simp [clockSum, List.range_succ])
  exact Nat.sub_le_sub_right h 1

private theorem prefix_of_mature (s : OutputStream) (n m : Nat) (h : m ≤ matureSize n) :
    (matureWord n s).take m = prefixBits (birthOf s) m := by
  simp only [matureWord, prefixBits, ← List.map_take, List.take_range, Nat.min_eq_left h]

private theorem inputIncidence (s : OutputStream) (n : Nat) (hn : 2 ≤ n) :
    (shapeFromIncidence (acquired .incidence n s)).bind maturePrefix =
      some (n, matureWord n s) := by
  have h := exact_ordered_birth_prefix (birthOf s) n hn
  unfold acquired physicalTree
  rw [h.2.2.2.1, Option.bind_some]
  exact h.2.2.2.2.2.2.2.2.1

private theorem inputFrontier (s : OutputStream) (n : Nat) (hn : 2 ≤ n) :
    (shapeFromFrontier (acquired .frontier n s)).bind maturePrefix =
      some (n, matureWord n s) := by
  have h := exact_ordered_birth_prefix (birthOf s) n hn
  unfold acquired physicalTree
  rw [h.2.2.2.2.1, Option.bind_some]
  exact h.2.2.2.2.2.2.2.2.1

private theorem written_read {Binding : Type} (b : Backing Binding) (m : Memory) :
    (writeMemory b m).read = some m ∧ (writeMemory b m).binding = b.binding := by
  cases m
  exact ⟨rfl,rfl⟩

private theorem completion_has_code (P : Promise) (hP : P.Valid) (s : OutputStream)
    (hs : P.Legal s) :
    ∃ code, reify P (acquire P s).earned = some code ∧ code.eval = s := by
  have h := attained_prefix_acquisition P hP s hs
  have hD := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hg := h.2.2.1
  rw [installEarned, hD.2] at hg
  change generate P (acquire P s).earned = some s at hg
  rw [← reify_eval] at hg
  cases hx : reify P (acquire P s).earned with
  | none => simp [hx] at hg
  | some code =>
    simp only [hx, Option.map_some, Option.some.injEq] at hg
    exact ⟨code,rfl,hg⟩

/-- On the attained domain incidence really returns the canonical completed bundle. -/
theorem recover_incidence_exact (P : Promise) (s : OutputStream) (n : Nat)
    (code : Code) (hn : 2 ≤ n) (hm : P.target ≤ matureSize n)
    (hc : reify P (prefixBits (birthOf s) P.target) = some code)
    (he : code.eval = s) :
    recoverIncidence P (acquired .incidence n s) =
      some (direct s ⟨prefixBits (birthOf s) P.target, code, n, clockSum n⟩) := by
  unfold recoverIncidence
  rw [inputIncidence s n hn, Option.bind_some]
  simp [fromMature, prefix_of_mature s n P.target hm, hc, fromMemory, he]

private theorem recover_frontier_exact (P : Promise) (s : OutputStream) (n : Nat)
    (code : Code) (hn : 2 ≤ n) (hm : P.target ≤ matureSize n)
    (hc : reify P (prefixBits (birthOf s) P.target) = some code) (he : code.eval = s) :
    recoverFrontier P (acquired .frontier n s) =
      some (direct s ⟨prefixBits (birthOf s) P.target, code, n, clockSum n⟩) := by
  unfold recoverFrontier
  rw [inputFrontier s n hn, Option.bind_some]
  simp [fromMature, prefix_of_mature s n P.target hm, hc, fromMemory, he]

private theorem recover_four_exact (P : Promise) (s : OutputStream) (n : Nat)
    (code : Code) (hn : 2 ≤ n) (hm : P.target ≤ matureSize n)
    (hc : reify P (prefixBits (birthOf s) P.target) = some code) (he : code.eval = s) :
    let b := direct s ⟨prefixBits (birthOf s) P.target, code, n, clockSum n⟩
    ∀ kind, recover P (project b kind) = some b := by
  intro b kind
  cases kind with
  | incidence => exact recover_incidence_exact P s n code hn hm hc he
  | frontier => exact recover_frontier_exact P s n code hn hm hc he
  | chronology =>
    change recoverIncidence P (incidenceAddresses (shape
      (replayBirthRecord n (physicalBirthClock (birthOf s) n).births).tree)) = some b
    rw [replayBirthRecord_exact]
    exact recover_incidence_exact P s n code hn hm hc he
  | earned => simp [b, direct, project, recover, fromMemory, he]

/-- Four genuinely different inputs yield one identical bundle on the completed,
synchronized, law-ready domain. The backing installed at acquisition is explicit;
later holdings and live rights are premises, not outcomes of the decoders. -/
theorem earned_memory_recovery (P : Promise) (hP : P.Valid) (s : OutputStream)
    (hs : P.Legal s) {Binding : Type} (Live : Binding → OutputStream → Nat → Prop)
    (initial : Backing Binding) (hLive : Live initial.binding s (deadline P.target)) :
    ∃ code, reify P (prefixBits (birthOf s) P.target) = some code ∧ code.eval = s ∧
    (∃ k stored,
      let plan := acquisitionPlan P P.target (deadline P.target)
      let r := run planObserver plan () s k
      installStopped P initial r = some stored ∧
      HoldsAt Live initial.binding s stored
        ⟨prefixBits (birthOf s) P.target, code, deadline P.target, clockSum (deadline P.target)⟩) ∧
    ∀ n, deadline P.target ≤ n →
      let m : Memory := ⟨prefixBits (birthOf s) P.target, code, n, clockSum n⟩
      let b := direct s m
      ∀ retained : Backing Binding, HoldsAt Live initial.binding s retained m →
        (∀ kind, recover P (project b kind) = some b) ∧
        (∀ x y, convert P (project b x) y = some (project b y)) ∧
        (∀ x y, (convert P (project b x) y).bind (fun v => convert P v x) =
          some (project b x)) ∧
        (∀ held, retained.read = some held → recover P (.earned held) = some b) := by
  obtain ⟨code,hcode,hEval⟩ := completion_has_code P hP s hs
  have h := attained_prefix_acquisition P hP s hs
  have hw := h.1
  have hCut := h.2.1
  have hCursor := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨code, hw ▸ hcode,hEval,?_,?_⟩
  · obtain ⟨k,hstop,hcut,hreg,_⟩ := hr
    let m : Memory := ⟨prefixBits (birthOf s) P.target, code,
      deadline P.target, clockSum (deadline P.target)⟩
    refine ⟨k,writeMemory initial m,?_,?_⟩
    · unfold installStopped
      rw [ite_eq_left hstop, hreg]
      dsimp only
      rw [hcode, Option.map_some, hcut, hCut, hCursor, hw]
    · exact ⟨(written_read initial m).2,hLive,(written_read initial m).1⟩
  · intro n hn m b ret hRet
    have hN := deadline_minimal P.target
    have ha := recover_four_exact P s n code (hN.1.trans hn)
      (hN.2.1.trans (stable_mature _ _ hn)) (hw ▸ hcode) hEval
    have hb (x y : ViewKind) : convert P (project b x) y = some (project b y) := by
      unfold convert
      rw [ha x,Option.map_some]
    refine ⟨ha,hb,fun x y => ?_,?_⟩
    · rw [hb, Option.bind_some, hb]
    · intro held hh
      have hRead := hRet.2.2
      rw [hh] at hRead
      have he := Option.some.inj hRead
      subst held
      exact ha .earned

#print axioms earned_memory_recovery

open scoped BigOperators

private theorem constant_binary (b : Bool) (d : Nat) (hd : 1 ≤ d) :
    ClassLegal (.binary d) (fun _ => b) := by
  refine ⟨1, hd, fun _ => true, ?_⟩
  intro i
  change (if b then 1 else 0) = (∑ _j : Fin 1, 1 * (if b then 1 else 0)) % 2
  cases b <;> decide

private theorem constant_machine_emit (b : Bool) (i : Nat) :
    (UnaryMooreSeparation.Machine.emit ⟨id, fun _ : Unit => b, ()⟩) i = b := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

private theorem constant_moore (b : Bool) (K : Nat) (hK : 1 ≤ K) :
    ClassLegal (.moore K) (fun _ => b) := by
  refine ⟨Unit, inferInstance, ⟨id, fun _ => b, ()⟩, ?_, funext (constant_machine_emit b)⟩
  simpa using hK

private theorem const_incidence_diff (n : Nat) (hn : 3 ≤ n) :
    acquired .incidence n (fun _ => false) ≠ acquired .incidence n (fun _ => true) := by
  have h := lawful_source_readiness (.binary 0) trivial n (by omega)
  intro he
  have hw := (h.2.2.2.1 .incidence _ _).mp he
  have hF : 2 ≤ Nat.fib n := Nat.fib_mono hn
  have hm : 0 < matureSize n := by rw [h.2.2.1]; omega
  have hb := congrArg (fun xs : List Bool => xs[0]?) hw
  simp [matureWord, prefixBits, hm, consume, birthOf] at hb

theorem scalar_time_not_incidence (n : Nat) (hn : 3 ≤ n) :
    (∀ d, 1 ≤ d → ∃ f g : OutputStream, ClassLegal (.binary d) f ∧
      ClassLegal (.binary d) g ∧ acquired .incidence n f ≠ acquired .incidence n g) ∧
    (∀ K, 1 ≤ K → ∃ f g : OutputStream, ClassLegal (.moore K) f ∧
      ClassLegal (.moore K) g ∧ acquired .incidence n f ≠ acquired .incidence n g) := by
  exact ⟨fun d hd => ⟨_, _, constant_binary false d hd, constant_binary true d hd,
    const_incidence_diff n hn⟩,
    fun K hK => ⟨_, _, constant_moore false K hK, constant_moore true K hK,
      const_incidence_diff n hn⟩⟩

theorem binary_zero_unique (f : OutputStream) :
    ClassLegal (.binary 0) f ↔ f = fun _ => false := by
  constructor
  · rintro ⟨r, hr, c, hc⟩
    have e : r = 0 := by omega
    subst r
    funext i
    have hi := hc i
    simp only [Nat.add_zero, Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_mod] at hi
    cases h : f i
    · rfl
    · rw [h] at hi
      contradiction
  · rintro rfl
    refine ⟨0, Nat.le_refl 0, Fin.elim0, ?_⟩
    intro i
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_mod]
    rfl

theorem row_zero_unique (c s : Fin 0 → Bool) :
    rowStream c s = fun _ => false := by
  funext i
  have h := public_row_seed_readiness 0 c s 2 (by omega)
  exact h.2.2.2.2.2.2.2.2.2.2.1 rfl i

#print axioms scalar_time_not_incidence
#print axioms binary_zero_unique
#print axioms row_zero_unique


end D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery
