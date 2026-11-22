/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/LawfulSourceReadiness
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/LawfulSourceReadiness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact attained-source readiness and constructive uniform thresholds for two lawful binary classes. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
import D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrenceSharpness
import D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSharpness

/-! Recover an actual source from its acquired mature physical word when the
class threshold holds, and separate the three readiness questions below it. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness

open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock OrderedBirthPrefix
open PublicRowSeedReadiness
open BoundedBinaryRecurrence (Legal)
open UnaryMooreSeparation (Machine)

/-- Reindex a zero-based output stream by positive birth serials. -/
def birthOf (s : Nat → Bool) : BirthStream := fun j => s (j - 1)

private theorem take_birth_prefix (s : Nat → Bool) {k v : Nat} (h : k ≤ v) :
    (prefixBits (birthOf s) v).take k = BoundedBinaryRecurrence.observed k s := by
  rw [prefixBits, ← List.map_take, List.take_range, Nat.min_eq_left h]
  apply List.ext_getElem
  · simp [BoundedBinaryRecurrence.observed]
  · intro i hi hj
    simp [consume, birthOf, BoundedBinaryRecurrence.observed]

private theorem moore_observed {Q : Type} (m : UnaryMooreSeparation.Machine Q) (k : Nat) :
    BoundedBinaryRecurrence.observed k m.emit = UnaryMooreSeparation.observations m k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    let m' : UnaryMooreSeparation.Machine Q := {m with start := m.transition m.start}
    rw [BoundedBinaryRecurrence.observed, List.ofFn_succ]
    change m.emit 0 :: BoundedBinaryRecurrence.observed k m'.emit =
      m.emit 0 :: UnaryMooreSeparation.observations m' k
    rw [ih]

/-- Choose the actual first matching row and return its executable generator. -/
private def synthBinary (d : Nat) (acquired : List Bool) : Option (Nat → Bool) :=
  let word := acquired.take (2 * d)
  (BoundedBinaryRecurrence.synthesize d word).map (fun c => rowStream c (seedFromPrefix word))

/-- Choose the actual first matching Moore table and return its executable generator. -/
private def synthMoore (K : Nat) (acquired : List Bool) : Option (Nat → Bool) :=
  (UnaryMooreSeparation.synthesize K (acquired.take (2 * K - 1))).map
    (fun x => (UnaryMooreSeparation.Table.machine x.2).emit)

private theorem synthBinary_exact (d v : Nat) (s : Nat → Bool)
    (hs : BoundedBinaryRecurrence.Legal d s) (hv : 2 * d ≤ v) :
    synthBinary d (prefixBits (birthOf s) v) = some s := by
  have he := take_birth_prefix s hv
  obtain ⟨c, hc, hCorrect, _⟩ :=
    (BoundedBinaryRecurrence.bounded_binary_recurrence d).2.2.1 _ s hs he
  rw [synthBinary, hc, Option.map_some, funext hCorrect]

private theorem synthMoore_exact (K v : Nat) {Q : Type} [Fintype Q] (m : UnaryMooreSeparation.Machine Q)
    (hK : 1 ≤ K) (hm : Fintype.card Q ≤ K) (hv : 2 * K - 1 ≤ v) :
    synthMoore K (prefixBits (birthOf m.emit) v) = some m.emit := by
  have he := (take_birth_prefix m.emit hv).trans (moore_observed m _)
  obtain ⟨x, hx, _, _, hCorrect, _⟩ :=
    (UnaryMooreSeparation.unary_moore_separation_and_synthesis K hK).2.2.1 _ Q m hm he
  rw [synthMoore, hx, Option.map_some, funext hCorrect]

private theorem binary_short_witness (d n : Nat) (hv : matureSize n < 2 * d) :
    ∃ s t : Nat → Bool, Legal d s ∧ Legal d t ∧
      (∀ i < matureSize n, s i = t i) ∧ s (matureSize n) ≠ t (matureSize n) := by
  have hm := (BoundedBinaryRecurrenceSharpness.bounded_binary_recurrence_sharpness
    d (by omega)).1 (matureSize n) hv
  exact ⟨_, _, hm.2⟩

private theorem moore_short_witness (K n : Nat) (hv : matureSize n < 2 * K - 1) :
    ∃ m m' : Machine (Fin (K - 1 + 1)), Fintype.card (Fin (K - 1 + 1)) ≤ K ∧
      (∀ i < matureSize n, m.emit i = m'.emit i) ∧
      m.emit (matureSize n) ≠ m'.emit (matureSize n) := by
  have hm := (UnaryMooreSharpness.unary_moore_sharpness
    K (by omega)).1 (matureSize n) hv
  exact ⟨_, _, hm.2⟩

private theorem mature_lt_born (n : Nat) (hn : 2 ≤ n) : matureSize n < clockSum n := by
  cases n with
  | zero => omega
  | succ k =>
    have hk : 0 < k := by omega
    simpa [matureSize, clockSum, List.range_succ] using (Nat.fib_pos.mpr hk)

private theorem same_labels_iff (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    (physicalBirthClock z n).tree = (physicalBirthClock z' n).tree ↔
      prefixBits z (clockSum n) = prefixBits z' (clockSum n) :=
  ((exact_ordered_birth_prefix z n hn).2.2.2.2.2.2.1 z').2.2

private theorem shape_eq_iff_same_literal_presence (t u : Labelled) :
    shape t = shape u ↔ ∀ p : Address, present t p = present u p := by
  induction t generalizing u with
  | of v =>
    cases u with
    | of w =>
      constructor
      · intro _ p
        cases p with
        | nil => simp [present, atTree]
        | cons b p => cases b <;> rfl
      · intro _
        rfl
    | mul l r =>
      constructor
      · intro h
        simp [shape] at h
      · intro h
        have hh := h [false]
        simp [present, atTree] at hh
  | mul l r ihl ihr =>
    cases u with
    | of w =>
      constructor
      · intro h
        simp [shape] at h
      · intro h
        have hh := h [false]
        simp [present, atTree] at hh
    | mul l' r' =>
      have hs : shape (.mul l r) = shape (.mul l' r') ↔
          shape l = shape l' ∧ shape r = shape r' := by
        change FreeMagma.mul (shape l) (shape r) = FreeMagma.mul (shape l') (shape r') ↔ _
        constructor
        · intro h
          injection h with h₁ h₂
          exact ⟨h₁, h₂⟩
        · rintro ⟨h₁, h₂⟩
          rw [h₁, h₂]
      rw [hs, ihl, ihr]
      constructor
      · rintro ⟨hl, hr⟩ p
        cases p with
        | nil => simp [present, atTree]
        | cons b p =>
          cases b
          · exact hl p
          · exact hr p
      · intro h
        exact ⟨fun p => h (false :: p), fun p => h (true :: p)⟩

private theorem same_presence_iff_mature (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    (∀ p : Address, present (physicalBirthClock z n).tree p =
      present (physicalBirthClock z' n).tree p) ↔
        prefixBits z (clockSum (n-1)) = prefixBits z' (clockSum (n-1)) := by
  rw [← shape_eq_iff_same_literal_presence]
  have a := exact_ordered_birth_prefix z n hn
  have b := exact_ordered_birth_prefix z' n hn
  constructor
  · intro h
    exact ((a.2.2.2.2.2.2.1 z').1).mp (fun p => by rw [h])
  · intro h
    exact a.2.2.2.2.2.2.2.2.2.1.symm.trans (h ▸ b.2.2.2.2.2.2.2.2.2.1)

private theorem same_successor_presence_iff (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    (∀ p : Address, present (physicalBirthClock z (n+1)).tree p =
      present (physicalBirthClock z' (n+1)).tree p) ↔
        prefixBits z (clockSum n) = prefixBits z' (clockSum n) :=
  same_presence_iff_mature z z' (n+1) (by omega)

private theorem clock_lower (m : Nat) : m - 1 ≤ clockSum m := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hstep : clockSum (k+1+1) = clockSum (k+1) + Nat.fib (k+1) := by
        simp [clockSum, List.range_succ, Nat.add_assoc]
      have hp := Nat.fib_pos.mpr (show 0 < k+1 by omega)
      omega

private theorem pref_iff (z z' : BirthStream) (k : Nat) :
    prefixBits z k = prefixBits z' k ↔ ∀ i < k, consume z i = consume z' i := by
  unfold prefixBits
  rw [List.map_inj_left]
  simp

private theorem eval_replies_update_read (z : BirthStream) (n k : Nat) (p : Address) :
    (eval z n (List.replicate k .update ++ [.read p])).1 =
      List.replicate k .ack ++ [.answer (present (physicalBirthClock z (n+k)).tree p)] := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, eval, reply, nextEpoch]
    rw [ih, show n+1+k = n+(k+1) by omega]

private theorem tree_eq_of_consume_eq {z z' : BirthStream}
    (h : ∀ i, consume z i = consume z' i) (n : Nat) :
    (physicalBirthClock z n).tree = (physicalBirthClock z' n).tree := by
  have hr := (physical_birth_clock z n).2.2.2.2.2.2.2.2.2.2 z'
  apply congrArg BirthRun.tree
  apply hr
  intro j hj _
  have e := h (j-1)
  unfold consume at e
  rwa [show j-1+1=j by omega] at e

private theorem eval_eq_of_consume_eq {z z' : BirthStream}
    (h : ∀ i, consume z i = consume z' i) (n : Nat) (as : List Action) :
    eval z n as = eval z' n as := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih =>
    cases a <;> simp [eval, reply, updateSnapshots, ih, tree_eq_of_consume_eq h]

private theorem same_script_replies_iff (z z' : BirthStream) (n : Nat) :
    (∀ as, (eval z n as).1 = (eval z' n as).1) ↔
      ∀ i, consume z i = consume z' i := by
  constructor
  · intro h i
    let k := i + 3
    have hN : 2 ≤ n+k := by dsimp [k]; omega
    have hend : ∀ p, present (physicalBirthClock z (n+k)).tree p =
      present (physicalBirthClock z' (n+k)).tree p := by
      intro p
      have hp := h (List.replicate k .update ++ [.read p])
      rw [eval_replies_update_read, eval_replies_update_read] at hp
      exact Reply.answer.inj (List.cons.inj (List.append_cancel_left hp)).1
    have hi := clock_lower (n+k-1)
    exact (pref_iff z z' _).mp ((same_presence_iff_mature z z' _ hN).mp hend) i
      (by dsimp [k] at *; omega)
  · intro h as
    exact congrArg Prod.fst (eval_eq_of_consume_eq h n as)

private theorem same_scripts_iff (z z' : BirthStream) (n : Nat) :
    (∀ as, eval z n as = eval z' n as) ↔ ∀ i, consume z i = consume z' i :=
  ⟨fun h => (same_script_replies_iff z z' n).mp
      (fun as => congrArg Prod.fst (h as)),
    fun h => eval_eq_of_consume_eq h n⟩

private theorem indexed_adaptive_script (z : BirthStream) (n : Nat)
    (pre as : List Action) (hist : List Reply) (hh : hist.length = pre.length) :
    adaptiveScript (fun hs => (pre ++ as)[hs.length]?) z as.length n hist = as := by
  induction as generalizing n pre hist with
  | nil => rfl
  | cons a as ih =>
    have hhead : (pre ++ a :: as)[hist.length]? = some a := by
      simp [hh]
    simp only [List.length_cons, adaptiveScript, hhead, List.cons.injEq, true_and]
    have ht := ih (nextEpoch n a) (pre ++ [a]) (hist ++ [reply z n a])
      (by simp [hh])
    simpa only [List.append_assoc, List.singleton_append] using ht

private theorem adaptive_script_eq_of_consume_eq {z z' : BirthStream}
    (h : ∀ i, consume z i = consume z' i) (policy : List Reply → Option Action)
    (fuel n : Nat) (hist : List Reply) :
    adaptiveScript policy z fuel n hist = adaptiveScript policy z' fuel n hist := by
  induction fuel generalizing n hist with
  | zero => rfl
  | succ fuel ih =>
    cases hp : policy hist with
    | none => simp [adaptiveScript, hp]
    | some a =>
      have hr : reply z n a = reply z' n a := by
        cases a <;> simp [reply, tree_eq_of_consume_eq h]
      simp [adaptiveScript, hp, hr, ih]

private theorem same_adaptive_iff (z z' : BirthStream) (n : Nat) :
    (∀ policy fuel hist, adaptiveEval policy z fuel n hist =
      adaptiveEval policy z' fuel n hist) ↔ ∀ i, consume z i = consume z' i := by
  constructor
  · intro h
    apply (same_scripts_iff z z' n).mp
    intro as
    have he := congrArg Prod.snd (h (fun hist => as[hist.length]?) as.length [])
    have hz : adaptiveScript (fun hist => as[hist.length]?) z as.length n [] = as :=
      indexed_adaptive_script z n [] as [] rfl
    have hz' : adaptiveScript (fun hist => as[hist.length]?) z' as.length n [] = as :=
      indexed_adaptive_script z' n [] as [] rfl
    simpa only [adaptiveEval, List.nil_append, hz, hz'] using he
  · intro h policy fuel hist
    dsimp only [adaptiveEval]
    rw [adaptive_script_eq_of_consume_eq h, eval_eq_of_consume_eq h]

/-- The two authentic source laws, with only their width or state bound public. -/
inductive LawfulClass
  | binary (d : Nat)
  | moore (K : Nat)

abbrev OutputStream := Nat → Bool

/-- The authentic Moore bound is positive; binary order zero is allowed. -/
def ValidClass : LawfulClass → Prop
  | .binary _ => True
  | .moore K => 1 ≤ K

/-- Legal output laws, independently of their reproduction by synthesis. -/
def ClassLegal : LawfulClass → OutputStream → Prop
  | .binary d, s => BoundedBinaryRecurrence.Legal d s
  | .moore K, s => ∃ (Q : Type) (fQ : Fintype Q) (m : UnaryMooreSeparation.Machine Q),
      @Fintype.card Q fQ ≤ K ∧ m.emit = s

/-- The exact uniform threshold, measured in mature bits. -/
def requiredBits : LawfulClass → Nat
  | .binary d => 2*d
  | .moore K => 2*K-1

/-- The existing finite, first-match synthesizer belonging to the public class. -/
def synthesizeClass : LawfulClass → List Bool → Option OutputStream
  | .binary d, word => synthBinary d word
  | .moore K, word => synthMoore K word

private theorem synthesize_class_exact (C : LawfulClass) (v : Nat) (s : OutputStream)
    (hC : ValidClass C) (hs : ClassLegal C s) (hv : requiredBits C ≤ v) :
    synthesizeClass C (prefixBits (birthOf s) v) = some s := by
  cases C with
  | binary d => exact synthBinary_exact d v s hs hv
  | moore K =>
    obtain ⟨Q, fQ, m, hm, rfl⟩ := hs
    exact @synthMoore_exact K v Q fQ m hC hm hv

/-- The actual reached physical tree of a zero-based source at cut n. -/
def physicalTree (n : Nat) (s : OutputStream) : Labelled :=
  (physicalBirthClock (birthOf s) n).tree

/-- Bits decoded from the already acquired geometry at the attained cut. -/
def matureWord (n : Nat) (s : OutputStream) : List Bool :=
  prefixBits (birthOf s) (matureSize n)

/-- Complete actual ordered bits born through cut n, including the newest batch. -/
def bornWord (n : Nat) (s : OutputStream) : List Bool :=
  prefixBits (birthOf s) (clockSum n)

/-- A candidate must satisfy the same public law and the attained mature prefix. -/
def Compatible (C : LawfulClass) (n : Nat) (s t : OutputStream) : Prop :=
  ClassLegal C t ∧ matureWord n s = matureWord n t

/-- Literal next-cut presence at address p; no update is performed by querying this function. -/
def queryNext (n : Nat) (p : Address) (s : OutputStream) : Bool :=
  present (physicalTree (n+1) s) p

/-- Both equivalent forms of already acquired geometry. -/
inductive Geometry
  | incidence
  | frontier

/-- The actual incidence or terminal boundary of the reached physical tree. -/
def acquired (g : Geometry) (n : Nat) (s : OutputStream) : List Address :=
  match g with
  | .incidence => incidenceAddresses (shape (physicalTree n s))
  | .frontier => frontierAddresses (shape (physicalTree n s))

private def decodeGeometry : Geometry → List Address → Option Shape
  | .incidence => shapeFromIncidence
  | .frontier => shapeFromFrontier

/-- Recover the reached epoch and a genuine generator from the acquired geometry. -/
def install (C : LawfulClass) (g : Geometry) (xs : List Address) :
    Option (Nat × OutputStream) :=
  ((decodeGeometry g xs).bind maturePrefix).bind
    fun p => (synthesizeClass C p.2).map (fun s => (p.1,s))

abbrev Policy := List Reply → Option Action
abbrev FutureBehavior := (List Action → Behavior) ×
  (Policy → Nat → List Reply → List Action × Behavior)
abbrev Answers := Labelled × (Address → Bool) × FutureBehavior

/-- Physical replies and update snapshots; adaptive choices receive only actual replies. -/
def future (n : Nat) (s : OutputStream) : FutureBehavior :=
  (eval (birthOf s) n, fun policy fuel hist => adaptiveEval policy (birthOf s) fuel n hist)

private def answers (n : Nat) (s : OutputStream) : Answers :=
  (physicalTree n s, fun p => queryNext n p s, future n s)

/-- The effective recovery of all tasks; domain is the attained geometry image at readiness. -/
def solve (C : LawfulClass) (g : Geometry) (xs : List Address) : Option Answers :=
  (install C g xs).map fun ns => answers ns.1 ns.2

/-- One rule must work on every lawful source with that public class and attained cut. -/
def UniformReady {O : Type} (C : LawfulClass) (g : Geometry) (n : Nat)
    (task : OutputStream → O) : Prop :=
  ∃ recover : List Address → Option O, ∀ s, ClassLegal C s →
    recover (acquired g n s) = some (task s)

private theorem prefix_iff (k : Nat) (s t : OutputStream) :
    prefixBits (birthOf s) k = prefixBits (birthOf t) k ↔ ∀ i < k, s i = t i := by
  simpa [consume, birthOf] using (pref_iff (birthOf s) (birthOf t) k)

private theorem actual_acquired_iff (g : Geometry) (n : Nat) (s t : OutputStream) (hn : 2 ≤ n) :
    acquired g n s = acquired g n t ↔ matureWord n s = matureWord n t := by
  have h := exact_ordered_birth_prefix (birthOf s) n hn
  have h' := exact_ordered_birth_prefix (birthOf t) n hn
  constructor
  · intro he
    cases g
    · apply (h.2.2.2.2.2.2.1 (birthOf t)).1.mp
      intro p
      change p ∈ acquired .incidence n s ↔ p ∈ acquired .incidence n t
      rw [he]
    · apply (h.2.2.2.2.2.2.1 (birthOf t)).2.1.mp
      intro p
      change p ∈ acquired .frontier n s ↔ p ∈ acquired .frontier n t
      rw [he]
  · intro hw
    have a := h.2.2.2.2.2.2.2.2.2.1
    have b := h'.2.2.2.2.2.2.2.2.2.1
    have eq : shape (physicalTree n s) = shape (physicalTree n t) := a.symm.trans
      ((congrArg (shapeOfPrefix n) hw).trans b)
    cases g <;> simp only [acquired, eq]

private theorem actual_mature (g : Geometry) (n : Nat) (s : OutputStream) (hn : 2 ≤ n) :
    (decodeGeometry g (acquired g n s)).bind maturePrefix = some (n, matureWord n s) := by
  have h := exact_ordered_birth_prefix (birthOf s) n hn
  have hw := h.2.2.2.2.2.2.2.2.1
  cases g
  · simpa only [decodeGeometry, acquired, physicalTree, matureWord, matureSize, h.2.2.2.1, Option.bind_some] using hw
  · simpa only [decodeGeometry, acquired, physicalTree, matureWord, matureSize, h.2.2.2.2.1, Option.bind_some] using hw

private theorem install_exact (C : LawfulClass) (g : Geometry) (n : Nat) (s : OutputStream)
    (hC : ValidClass C) (hn : 2 ≤ n) (hs : ClassLegal C s) (hv : requiredBits C ≤ matureSize n) :
    install C g (acquired g n s) = some (n,s) := by
  rw [install, actual_mature g n s hn, Option.bind_some]
  change (synthesizeClass C (prefixBits (birthOf s) (matureSize n))).map _ = some (n,s)
  rw [synthesize_class_exact C (matureSize n) s hC hs hv]
  rfl

private theorem solve_exact (C : LawfulClass) (g : Geometry) (n : Nat) (s : OutputStream)
    (hC : ValidClass C) (hn : 2 ≤ n) (hs : ClassLegal C s) (hv : requiredBits C ≤ matureSize n) :
    solve C g (acquired g n s) = some (answers n s) := by
  rw [solve, install_exact C g n s hC hn hs hv]
  rfl

private theorem future_iff (n : Nat) (s t : OutputStream) :
    future n s = future n t ↔ s = t := by
  constructor
  · intro h
    have he := (same_scripts_iff (birthOf s) (birthOf t) n).mp
      (fun as => congrFun (congrArg Prod.fst h) as)
    exact funext (by simpa [consume, birthOf] using he)
  · rintro rfl
    rfl

private theorem source_replies_iff (n : Nat) (s t : OutputStream) :
    (∀ as, (eval (birthOf s) n as).1 = (eval (birthOf t) n as).1) ↔ s = t := by
  rw [same_script_replies_iff]
  constructor
  · intro h
    exact funext (by simpa [consume, birthOf] using h)
  · rintro rfl
    intro i
    rfl

private theorem source_adaptive_iff (n : Nat) (s t : OutputStream) :
    (∀ policy fuel hist, adaptiveEval policy (birthOf s) fuel n hist =
      adaptiveEval policy (birthOf t) fuel n hist) ↔ s = t := by
  rw [same_adaptive_iff]
  constructor
  · intro h
    exact funext (by simpa [consume, birthOf] using h)
  · rintro rfl
    intro i
    rfl

private theorem lawful_short_witness (C : LawfulClass) (n : Nat) (hv : matureSize n < requiredBits C) :
    ∃ s t, ClassLegal C s ∧ ClassLegal C t ∧
      (∀ i < matureSize n, s i = t i) ∧ s (matureSize n) ≠ t (matureSize n) := by
  cases C with
  | binary d => exact binary_short_witness d n hv
  | moore K =>
    obtain ⟨a, b, hcard, he, hf⟩ := moore_short_witness K n hv
    exact ⟨a.emit, b.emit, ⟨_, inferInstance, a, hcard, rfl⟩,
      ⟨_, inferInstance, b, hcard, rfl⟩, he, hf⟩

private theorem uniform_from_answer {O : Type} (C : LawfulClass) (g : Geometry) (n : Nat)
    (f : Answers → O) (hC : ValidClass C) (hn : 2 ≤ n) (hv : requiredBits C ≤ matureSize n) :
    UniformReady C g n (fun s => f (answers n s)) := by
  refine ⟨fun xs => (solve C g xs).map f, ?_⟩
  intro s hs
  change (solve C g (acquired g n s)).map f = some (f (answers n s))
  rw [solve_exact C g n s hC hn hs hv]
  rfl

private theorem uniform_agree {O : Type} {C : LawfulClass} {g : Geometry} {n : Nat}
    {f : OutputStream → O} (h : UniformReady C g n f) {s t : OutputStream}
    (hs : ClassLegal C s) (ht : ClassLegal C t) (hinput : acquired g n s = acquired g n t) :
    f s = f t := by
  obtain ⟨recover, hr⟩ := h
  exact Option.some.inj ((hr s hs).symm.trans ((congrArg recover hinput).trans (hr t ht)))

private theorem not_uniform (C : LawfulClass) (g : Geometry) (n : Nat) (hn : 2 ≤ n)
    (hshort : matureSize n < requiredBits C) :
    ¬ UniformReady C g n (physicalTree n) ∧
    ¬ UniformReady C g n (fun s p => queryNext n p s) ∧
    ¬ UniformReady C g n (future n) := by
  obtain ⟨s,t,hs,ht,hm,hbit⟩ := lawful_short_witness C n hshort
  have hs₀ : matureWord n s = matureWord n t := (prefix_iff _ s t).mpr hm
  have hinput := (actual_acquired_iff g n s t hn).mpr hs₀
  have hborn : bornWord n s ≠ bornWord n t := fun h =>
    hbit ((prefix_iff _ s t).mp h (matureSize n) (mature_lt_born n hn))
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hborn
    exact (same_labels_iff (birthOf s) (birthOf t) n hn).mp (uniform_agree h hs ht hinput)
  · intro h
    apply hborn
    exact (same_successor_presence_iff (birthOf s) (birthOf t) n hn).mp
      (fun p => congrFun (uniform_agree h hs ht hinput) p)
  · intro h
    exact hbit (congrFun ((future_iff n s t).mp (uniform_agree h hs ht hinput)) (matureSize n))

/-- Individual attained-fiber criteria and all three independent uniform readiness thresholds. -/
theorem lawful_source_readiness (C : LawfulClass) (hC : ValidClass C) (n : Nat) (hn : 2 ≤ n) :
    (∀ (s : OutputStream) (_hs : ClassLegal C s),
      ((∀ t, Compatible C n s t → ∀ p : Address, queryNext n p s = queryNext n p t) ↔
        (∀ t, Compatible C n s t → bornWord n s = bornWord n t)) ∧
      ((∀ t, Compatible C n s t → physicalTree n s = physicalTree n t) ↔
        (∀ t, Compatible C n s t → bornWord n s = bornWord n t)) ∧
      ((∀ t, Compatible C n s t → future n s = future n t) ↔
        (∀ t, Compatible C n s t → s = t))) ∧
    (∀ g : Geometry,
      (UniformReady C g n (physicalTree n) ↔ requiredBits C ≤ matureSize n) ∧
      (UniformReady C g n (fun s p => queryNext n p s) ↔ requiredBits C ≤ matureSize n) ∧
      (UniformReady C g n (future n) ↔ requiredBits C ≤ matureSize n)) ∧
    matureSize n = Nat.fib n - 1 ∧
    (∀ g : Geometry, ∀ s t : OutputStream, acquired g n s = acquired g n t ↔
      matureWord n s = matureWord n t) ∧
    (∀ s t : OutputStream, (∀ as, (eval (birthOf s) n as).1 = (eval (birthOf t) n as).1) ↔ s = t) ∧
    (∀ s t : OutputStream, (∀ policy fuel hist, adaptiveEval policy (birthOf s) fuel n hist =
      adaptiveEval policy (birthOf t) fuel n hist) ↔ s = t) ∧
    (∀ (g : Geometry) (s : OutputStream), ClassLegal C s → requiredBits C ≤ matureSize n →
      install C g (acquired g n s) = some (n,s) ∧
      solve C g (acquired g n s) = some (physicalTree n s, fun p => queryNext n p s, future n s)) := by
  refine ⟨?_, ?_, ?_, fun g s t => actual_acquired_iff g n s t hn, source_replies_iff n, source_adaptive_iff n, ?_⟩
  · intro s _
    exact ⟨⟨fun h t ht => (same_successor_presence_iff (birthOf s) (birthOf t) n hn).mp (h t ht),
      fun h t ht => (same_successor_presence_iff (birthOf s) (birthOf t) n hn).mpr (h t ht)⟩,
      ⟨fun h t ht => (same_labels_iff (birthOf s) (birthOf t) n hn).mp (h t ht),
      fun h t ht => (same_labels_iff (birthOf s) (birthOf t) n hn).mpr (h t ht)⟩,
      ⟨fun h t ht => (future_iff n s t).mp (h t ht),
      fun h t ht => (future_iff n s t).mpr (h t ht)⟩⟩
  · intro g
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro h; by_contra! hv; exact (not_uniform C g n hn hv).1 h
    · exact uniform_from_answer C g n Prod.fst hC hn
    · intro h; by_contra! hv; exact (not_uniform C g n hn hv).2.1 h
    · exact uniform_from_answer C g n (fun a => a.2.1) hC hn
    · intro h; by_contra! hv; exact (not_uniform C g n hn hv).2.2 h
    · exact uniform_from_answer C g n (fun a => a.2.2) hC hn
  · exact (public_row_seed_readiness 0 Fin.elim0 Fin.elim0 n hn).2.2.2.1
  · intro g s hs hv
    exact ⟨install_exact C g n s hC hn hs hv, solve_exact C g n s hC hn hs hv⟩

#print axioms lawful_source_readiness

end D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness
