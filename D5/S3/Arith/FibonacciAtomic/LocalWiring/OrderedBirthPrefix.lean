/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/OrderedBirthPrefix
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/OrderedBirthPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic]
   utility: none
   digest: Exact finite inversion of mature and full chronological birth prefixes. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock

/-! Recover the actual chronological birth events, from incidence or labels. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix

open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock


/-- The middle physical tree from an old labelled tree and a shape two updates later. -/
def middleOf : Labelled → Shape → Option Labelled
  | .of true, .mul (.of _) (.of _) => some beta
  | .of false, .mul (.mul (.of _) (.of _)) (.of _) => some (.mul beta alpha)
  | .of false, .mul (.of _) (.mul (.of _) (.of _)) => some (.mul alpha beta)
  | .mul l r, .mul x y => do
    let a ← middleOf l x
    let b ← middleOf r y
    pure (.mul a b)
  | _, _ => none

private theorem middleOf_actual {u v w : Labelled} (h : Step u v) (j : Step v w) :
    middleOf u (shape w) = some v := by
  induction h generalizing w with
  | alphaToBeta =>
    cases j <;> rfl
  | betaLeft =>
    cases j with
    | branch a b => cases a <;> cases b <;> rfl
  | betaRight =>
    cases j with
    | branch a b => cases a; cases b <;> rfl
  | branch _ _ il ir =>
    cases j with
    | branch a b =>
      simp only [show shape (.mul _ _) = .mul (shape _) (shape _) from rfl, middleOf,
        il a, ir b]
      rfl

/-- Recover the immediate physical predecessor from the present two-step shape. -/
def predecessorFromShape (s : Shape) : Option Labelled :=
  (decode s).bind (fun u => middleOf u s)

private theorem predecessorFromShape_actual {u v w : Labelled} (h : Step u v) (j : Step v w) :
    predecessorFromShape (shape w) = some v := by
  have hd := (exact_local_two_step.1 (shape w) u).mpr ⟨v, w, h, j, rfl⟩
  simp only [predecessorFromShape, hd, Option.bind_some]
  exact middleOf_actual h j

private theorem shapeNextEqual {t w v : Labelled} (h : Step t w) (j : Step t v) :
    shape w = shape v := by
  induction h generalizing v with
  | alphaToBeta => cases j; rfl
  | betaLeft => cases j <;> rfl
  | betaRight => cases j <;> rfl
  | branch _ _ il ir =>
    cases j with
    | branch a b => exact congrArg₂ FreeMagma.mul (il a) (ir b)




/-- Reverse a labelled round. A mixed cherry is a newborn beta branch; a
stable branch is rewound through the same physical links. -/
def rewind : Labelled → Option Labelled
  | .of true => none
  | .of false => some alpha
  | .mul l r =>
    if (l = beta ∧ r = alpha) ∨ (l = alpha ∧ r = beta) then some beta
    else
      match rewind l, rewind r with
      | some u, some v => some (.mul u v)
      | _, _ => none

private theorem rewind_step {t w : Labelled} (hw : Step t w) : rewind w = some t := by
  have noAlpha {u v : Labelled} (h : Step u v) : v ≠ alpha := by
    cases h with
    | alphaToBeta => decide
    | betaLeft => intro he; cases he
    | betaRight => intro he; cases he
    | branch _ _ => intro he; cases he
  induction hw with
  | alphaToBeta => rfl
  | betaLeft => decide
  | betaRight => decide
  | @branch l l' r r' hl hr il ir =>
    have hMixed : ¬ ((l' = beta ∧ r' = alpha) ∨ (l' = alpha ∧ r' = beta)) := by
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact noAlpha hr h
      · exact noAlpha hl h
    rw [rewind, ite_eq_right hMixed, il, ir]

private theorem rewind_of_step {n : Nat} {t w : Labelled} (_ht : After n t) (hw : Step t w) :
    rewind w = some t := rewind_step hw




/-- Read back only the batch at beta sites of the old tree, left-first.
The counter is threaded through those same old physical links. -/
private def readBatch (epoch c : Nat) (p : Address) (old new : Labelled) :
    Nat × List BirthEvent :=
  match old, new with
  | .of true, _ => (c, [])
  | .of false, _ => (c+1, [⟨c+1, epoch, p, terminalBit new []⟩])
  | .mul l r, .mul u v =>
    let a := readBatch epoch c (p ++ [false]) l u
    let b := readBatch epoch a.1 (p ++ [true]) r v
    (b.1, a.2 ++ b.2)
  | .mul _ _, .of _ => (c, [])

private theorem read_actual_batch (z : BirthStream) (e c : Nat) (p : Address) (t : Labelled) :
    let r := birthRound z e c p t
    readBatch e c p t r.tree = (r.cursor, r.births) := by
  induction t generalizing c p with
  | of b =>
    cases b
    · cases h : consume z c <;> simp [birthRound, readBatch, h, terminalBit, isBeta, atTree,
        beta, alpha]
      decide
    · simp [birthRound, readBatch]
  | mul l r il ir =>
    let a := birthRound z e c (p ++ [false]) l
    let b := birthRound z e a.cursor (p ++ [true]) r
    change (let a' := readBatch e c (p ++ [false]) l a.tree
      let b' := readBatch e a'.1 (p ++ [true]) r b.tree
      (b'.1, a'.2 ++ b'.2)) = _
    rw [il c (p ++ [false])]
    dsimp only
    rw [ir a.cursor (p ++ [true])]
    rfl

/-- Rewind the labelled tree by actual single-step inversion, then read the
orientation bits in their original batch order, not semantic tree order. -/
def traceOfLabelled : Nat → Labelled → Option (List BirthEvent)
  | 0, t => if t = alpha then some [] else none
  | n+1, t => do
    let old ← rewind t
    let es ← traceOfLabelled n old
    pure (es ++ (readBatch (n+1) es.length [] old t).2)

private theorem trace_actual (z : BirthStream) (n : Nat) :
    traceOfLabelled n (physicalBirthClock z n).tree = some (physicalBirthClock z n).births := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let old := physicalBirthClock z n
    let s := physicalBirthClock z (n+1)
    let r := birthRound z (n+1) old.cursor [] old.tree
    have hw := physical_birth_clock z n
    have hrew : rewind s.tree = some old.tree := rewind_of_step hw.2.1 hw.2.2.1
    change (do
      let t ← rewind s.tree
      let es ← traceOfLabelled n t
      pure (es ++ (readBatch (n+1) es.length [] t s.tree).2)) = some (old.births ++ r.births)
    rw [hrew]
    change (do let es ← traceOfLabelled n old.tree
               pure (es ++ (readBatch (n+1) es.length [] old.tree s.tree).2)) = _
    rw [ih]
    change some (old.births ++ (readBatch (n+1) old.births.length [] old.tree r.tree).2) = _
    rw [← hw.2.2.2.1, read_actual_batch]

/-- The first k genuinely consumed source marks, not their values at index zero. -/
def prefixBits (z : BirthStream) (k : Nat) : List Bool := (List.range k).map (consume z)

/-- Extend any finite input prefix; the chosen values past this input are
irrelevant to every completed cut that has not consumed them. -/
def extendBits (bits : List Bool) (j : Nat) : Bool := bits[j-1]?.getD false

private theorem prefix_length (z : BirthStream) (k : Nat) : (prefixBits z k).length = k := by
  simp [prefixBits]

private theorem prefix_eq_iff (z z' : BirthStream) (k : Nat) :
    prefixBits z k = prefixBits z' k ↔ (∀ j, 1 ≤ j → j ≤ k → z j = z' j) := by
  rw [prefixBits, prefixBits, List.map_inj_left]
  constructor
  · intro h j hj hJ
    simpa [consume, Nat.sub_add_cancel hj] using h (j-1) (List.mem_range.mpr (by omega))
  · intro h i hi
    exact h (i+1) (by omega) (by have := List.mem_range.mp hi; omega)

private theorem prefix_from_bits (bits : List Bool) : prefixBits (extendBits bits) bits.length = bits := by
  apply List.ext_getElem (prefix_length ..)
  intro i hi hi'
  simp [prefixBits, consume, extendBits, hi']

private theorem prefix_take (z : BirthStream) {i k : Nat} (h : i ≤ k) :
    (prefixBits z k).take i = prefixBits z i := by
  apply List.ext_getElem
  · simp [prefix_length, h]
  · intro a ha ha'
    simp [prefixBits]

private theorem recorded_prefix (z : BirthStream) (n : Nat) :
    ((physicalBirthClock z n).births.map BirthEvent.mark) = prefixBits z (clockSum n) := by
  have hw := physical_birth_clock z n
  apply List.ext_getElem
  · simp [prefix_length, hw.2.2.2.2.1]
  · intro i hi hi'
    have hl : i < (physicalBirthClock z n).births.length := by simpa using hi
    have he : (physicalBirthClock z n).births[i]? = some ((physicalBirthClock z n).births[i]'hl) :=
      List.getElem?_eq_getElem hl
    simpa [prefixBits] using (hw.1 _ _ he).1.symm

private theorem exact_labelled_prefix (z z' : BirthStream) (n : Nat) :
    (physicalBirthClock z n).tree = (physicalBirthClock z' n).tree ↔
      prefixBits z (clockSum n) = prefixBits z' (clockSum n) := by
  constructor
  · intro h
    have hE : (physicalBirthClock z n).births = (physicalBirthClock z' n).births := by
      apply Option.some.inj
      rw [← trace_actual z n, ← trace_actual z' n, h]
    rw [← recorded_prefix z n, ← recorded_prefix z' n, hE]
  · intro h
    have hw := physical_birth_clock z n
    have hc : (physicalBirthClock z n).cursor = clockSum n := hw.2.2.2.1.trans hw.2.2.2.2.1
    have hEq := hw.2.2.2.2.2.2.2.2.2.2 z' (by
      rw [hc]
      exact (prefix_eq_iff z z' (clockSum n)).mp h)
    exact congrArg BirthRun.tree hEq

private theorem preceding_actual (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    predecessorFromShape (shape (physicalBirthClock z n).tree) =
      some (physicalBirthClock z (n-1)).tree := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  exact predecessorFromShape_actual (physical_birth_clock z k).2.2.1
    (physical_birth_clock z (k+1)).2.2.1

private theorem shape_prefix_actual (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    shape (physicalBirthClock z n).tree = shape (physicalBirthClock z' n).tree ↔
      prefixBits z (clockSum (n-1)) = prefixBits z' (clockSum (n-1)) := by
  constructor
  · intro h
    have hP := congrArg predecessorFromShape h
    rw [preceding_actual z n hn, preceding_actual z' n hn] at hP
    exact (exact_labelled_prefix z z' (n-1)).mp (Option.some.inj hP)
  · intro h
    have hp := (exact_labelled_prefix z z' (n-1)).mpr h
    have hu := (physical_birth_clock z (n-1)).2.2.1
    have hv := (physical_birth_clock z' (n-1)).2.2.1
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hu hv
    rw [← hp] at hv
    exact shapeNextEqual hu hv



/-- Recover the completed epoch from the acquired number of leaves alone.
The two leaf-count-one seed epochs are outside the calibrated range. -/
def epochFromShape (s : Shape) : Option Nat :=
  (List.range (s.length + 1)).find? fun n => decide (2 ≤ n ∧ Nat.fib (n+1) = s.length)

private theorem incidence_length (t : Labelled) :
    (shape t).length = alphaLeaves t + betaLeaves t := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r hl hr =>
    change (shape l).length + (shape r).length =
      (alphaLeaves l + alphaLeaves r) + (betaLeaves l + betaLeaves r)
    omega

private theorem epochFromShape_eq_some (s : Shape) {n : Nat} (hn : 2 ≤ n)
    (hcard : Nat.fib (n+1) = s.length) : epochFromShape s = some n := by
  have hb : n < s.length + 1 := by
    have h := Nat.le_fib_add_one (n+1)
    omega
  unfold epochFromShape
  cases h : (List.range (s.length + 1)).find? (fun k =>
      decide (2 ≤ k ∧ Nat.fib (k+1) = s.length)) with
  | none => exact False.elim ((List.find?_eq_none.mp h) n
      (List.mem_range.mpr hb) (decide_eq_true ⟨hn,hcard⟩))
  | some m =>
    have hp : 2 ≤ m ∧ Nat.fib (m+1) = s.length := by
      have H := List.find?_some h
      exact of_decide_eq_true H
    have he : m + 1 = n + 1 := by
      apply Nat.fib_strictMonoOn.injOn (by change 2 ≤ m + 1; omega)
        (by change 2 ≤ n + 1; omega)
      exact hp.2.trans hcard.symm
    congr 1
    omega

private theorem epochFromShape_physical (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    epochFromShape (shape (physicalBirthClock z n).tree) = some n := by
  apply epochFromShape_eq_some _ hn
  have h := (physical_birth_clock z n).2.2.2.2.2.2.2.2.1 hn
  rw [incidence_length, h.2.2.1, h.2.2.2]
  obtain ⟨k, hk⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.fib_add_two]



def incidenceAddresses : Shape → List Address
  | .of _ => [[]]
  | .mul l r => [] :: ((incidenceAddresses l).map (false :: ·) ++
      (incidenceAddresses r).map (true :: ·))

def frontierAddresses : Shape → List Address
  | .of _ => [[]]
  | .mul l r => (frontierAddresses l).map (false :: ·) ++
      (frontierAddresses r).map (true :: ·)

private def strip (b : Bool) : List Address → List Address :=
  List.filterMap fun
    | [] => none
    | c :: w => if b = c then some w else none

private theorem strip_append (b : Bool) (l r : List Address) :
    strip b (l ++ r) = strip b l ++ strip b r := by
  simp [strip]

private theorem strip_same (b : Bool) (l : List Address) :
    strip b (l.map (b :: ·)) = l := by
  induction l <;> simp [strip, *]

private theorem strip_other (b c : Bool) (h : b ≠ c) (l : List Address) :
    strip b (l.map (c :: ·)) = [] := by
  induction l <;> simp [strip, *]

private theorem strip_nil_head (b : Bool) (l : List Address) :
    strip b ([] :: l) = strip b l := rfl

private def recover : Nat → List Address → Option Shape
  | 0, _ => none
  | n + 1, xs =>
    if xs = [[]] then some tip
    else do
      let l ← recover n (strip false xs)
      let r ← recover n (strip true xs)
      pure (.mul l r)

def shapeFromIncidence (xs : List Address) : Option Shape := do
  let s ← recover xs.length xs
  if incidenceAddresses s = xs then some s else none

def shapeFromFrontier (xs : List Address) : Option Shape := do
  let s ← recover xs.length xs
  if frontierAddresses s = xs then some s else none

private theorem incidence_pos (s : Shape) : 0 < (incidenceAddresses s).length := by
  cases s <;> simp [incidenceAddresses]

private theorem frontier_pos (s : Shape) : 0 < (frontierAddresses s).length := by
  induction s with
  | of a => simp [frontierAddresses]
  | mul l r hl hr => simp only [frontierAddresses, List.length_append, List.length_map]; omega

private theorem recover_incidence (s : Shape) (n : Nat)
    (hn : (incidenceAddresses s).length ≤ n) :
    recover n (incidenceAddresses s) = some s := by
  induction s generalizing n with
  | of a =>
    cases a
    cases n with
    | zero => simp [incidenceAddresses] at hn
    | succ n => simp [recover, incidenceAddresses]
  | mul l r hl hr =>
    cases n with
    | zero => exact (Nat.not_lt_zero _ ((incidence_pos (.mul l r)).trans_le hn)).elim
    | succ n =>
      have hlen : 1 + (incidenceAddresses l).length + (incidenceAddresses r).length ≤ n + 1 := by
        simp only [incidenceAddresses, List.length_cons, List.length_append, List.length_map] at hn
        omega
      have hne : incidenceAddresses (.mul l r) ≠ [[]] := by
        intro h
        have hh := congrArg List.length h
        simp only [incidenceAddresses, List.length_cons, List.length_append,
          List.length_map, List.length_nil] at hh
        have hpl := incidence_pos l
        omega
      rw [recover, ite_eq_right hne]
      simp only [incidenceAddresses, strip_nil_head, strip_append, strip_same,
        strip_other false true (by decide), strip_other true false (by decide),
        List.nil_append, List.append_nil, hl n (by omega), hr n (by omega)]
      rfl

private theorem recover_frontier (s : Shape) (n : Nat)
    (hn : (frontierAddresses s).length ≤ n) :
    recover n (frontierAddresses s) = some s := by
  induction s generalizing n with
  | of a =>
    cases a
    cases n with
    | zero => simp [frontierAddresses] at hn
    | succ n => simp [recover, frontierAddresses]
  | mul l r hl hr =>
    have hpl := frontier_pos l
    have hpr := frontier_pos r
    cases n with
    | zero => exact (Nat.not_lt_zero _ ((frontier_pos (.mul l r)).trans_le hn)).elim
    | succ n =>
      have hlen : (frontierAddresses l).length + (frontierAddresses r).length ≤ n + 1 := by
        simpa [frontierAddresses] using hn
      have hne : frontierAddresses (.mul l r) ≠ [[]] := by
        intro h
        have hh := congrArg List.length h
        simp [frontierAddresses] at hh
        omega
      rw [recover, ite_eq_right hne]
      simp only [frontierAddresses, strip_append, strip_same,
        strip_other false true (by decide), strip_other true false (by decide),
        List.nil_append, List.append_nil, hl n (by omega), hr n (by omega)]
      rfl

private theorem shapeFromIncidence_roundtrip (s : Shape) :
    shapeFromIncidence (incidenceAddresses s) = some s := by
  simp [shapeFromIncidence, recover_incidence s _ le_rfl]

private theorem shapeFromFrontier_roundtrip (s : Shape) :
    shapeFromFrontier (frontierAddresses s) = some s := by
  simp [shapeFromFrontier, recover_frontier s _ le_rfl]

private theorem mem_incidenceAddresses (s : Shape) (p : Address) :
    p ∈ incidenceAddresses s ↔ present s p = true := by
  induction s generalizing p <;> cases p with
  | nil => simp [incidenceAddresses, present, atTree]
  | cons b ps => cases b <;> simp [incidenceAddresses, present, atTree, *]

private theorem mem_frontierAddresses (s : Shape) (p : Address) :
    p ∈ frontierAddresses s ↔ atTree s p = some tip := by
  induction s generalizing p <;> cases p with
  | nil => simp [frontierAddresses, atTree, tip]
  | cons b ps => cases b <;> simp [frontierAddresses, atTree, *]

private theorem incidenceAddresses_eq_prefixClosure (s : Shape) (p : Address) :
    p ∈ incidenceAddresses s ↔ ∃ q : Address, p ++ q ∈ frontierAddresses s := by
  induction s generalizing p with
  | of a =>
    constructor
    · intro h
      have hp : p = [] := by simpa [incidenceAddresses] using h
      subst p
      exact ⟨[], by simp [frontierAddresses]⟩
    · rintro ⟨q,h⟩
      have hnil : p ++ q = [] := by simpa [frontierAddresses] using h
      simp [incidenceAddresses, (List.append_eq_nil_iff.mp hnil).1]
  | mul l r hl hr =>
    cases p with
    | nil =>
      refine ⟨fun _ => ?_, fun _ => by simp [incidenceAddresses]⟩
      obtain ⟨q,hq⟩ := (hl []).mp (by simp [mem_incidenceAddresses, present, atTree])
      exact ⟨false :: q, by simpa [frontierAddresses] using hq⟩
    | cons b p =>
      cases b
      · simpa [incidenceAddresses, frontierAddresses] using hl p
      · simpa [incidenceAddresses, frontierAddresses] using hr p

private theorem frontierAddresses_iff_maximal (s : Shape) (p : Address) :
    p ∈ frontierAddresses s ↔
      p ∈ incidenceAddresses s ∧
        ∀ q : Address, p ++ q ∈ incidenceAddresses s → q = [] := by
  induction s generalizing p with
  | of a =>
    simp only [frontierAddresses, incidenceAddresses, List.mem_singleton]
    refine ⟨fun h => ⟨h, ?_⟩, And.left⟩
    intro q hq
    exact (List.append_eq_nil_iff.mp hq).2
  | mul l r hl hr =>
    cases p with
    | nil =>
      constructor
      · simp [frontierAddresses]
      · intro h
        have bad := h.2 [false] (by
          have hroot : [] ∈ incidenceAddresses l := by
            rw [mem_incidenceAddresses]
            simp [present, atTree]
          simp [incidenceAddresses, hroot])
        cases bad
    | cons b p =>
      cases b
      · simpa [frontierAddresses, incidenceAddresses] using hl p
      · simpa [frontierAddresses, incidenceAddresses] using hr p



/-- The intrinsic epoch and the complete marked word through the preceding cut,
as finite data computed from physical shape alone. -/
def matureFromShape (s : Shape) : Option (Nat × List BirthEvent) := do
  let n ← epochFromShape s
  let old ← predecessorFromShape s
  let es ← traceOfLabelled (n-1) old
  pure (n, es)

def completeFromLabelled (t : Labelled) : Option (Nat × List BirthEvent) := do
  let n ← epochFromShape (shape t)
  let es ← traceOfLabelled n t
  pure (n, es)

def maturePrefix (s : Shape) : Option (Nat × List Bool) :=
  (matureFromShape s).map fun (n, es) => (n, es.map BirthEvent.mark)

def completePrefix (t : Labelled) : Option (Nat × List Bool) :=
  (completeFromLabelled t).map fun (n, es) => (n, es.map BirthEvent.mark)

/-- Replay from the known alpha seed with the selected finite prefix. -/
def shapeOfPrefix (n : Nat) (bits : List Bool) : Shape :=
  shape (physicalBirthClock (extendBits bits) n).tree

def labelsOfPrefix (n : Nat) (bits : List Bool) : Labelled :=
  (physicalBirthClock (extendBits bits) n).tree

private theorem mature_actual (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    matureFromShape (shape (physicalBirthClock z n).tree) =
      some (n, (physicalBirthClock z (n-1)).births) := by
  unfold matureFromShape
  rw [epochFromShape_physical z n hn]
  change (do
    let old ← predecessorFromShape (shape (physicalBirthClock z n).tree)
    let es ← traceOfLabelled (n-1) old
    pure (n, es)) = _
  rw [preceding_actual z n hn]
  change (do let es ← traceOfLabelled (n-1) (physicalBirthClock z (n-1)).tree
             pure (n, es)) = _
  rw [trace_actual]
  rfl

private theorem complete_actual (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    completeFromLabelled (physicalBirthClock z n).tree = some (n, (physicalBirthClock z n).births) := by
  unfold completeFromLabelled
  rw [epochFromShape_physical z n hn]
  change (do let es ← traceOfLabelled n (physicalBirthClock z n).tree
             pure (n, es)) = _
  rw [trace_actual]
  rfl

private theorem mature_bits_actual (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    maturePrefix (shape (physicalBirthClock z n).tree) =
      some (n, prefixBits z (clockSum (n-1))) := by
  unfold maturePrefix
  rw [mature_actual z n hn, Option.map_some]
  change some (n, ((physicalBirthClock z (n-1)).births.map BirthEvent.mark)) = _
  rw [recorded_prefix]

private theorem complete_bits_actual (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    completePrefix (physicalBirthClock z n).tree = some (n, prefixBits z (clockSum n)) := by
  unfold completePrefix
  rw [complete_actual z n hn, Option.map_some]
  change some (n, ((physicalBirthClock z n).births.map BirthEvent.mark)) = _
  rw [recorded_prefix]

private theorem clock_sum_le (n : Nat) : clockSum (n-1) ≤ clockSum n := by
  cases n with
  | zero => rfl
  | succ n => simp [clockSum, List.range_succ]

private theorem clock_gap (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    clockSum n - clockSum (n-1) = Nat.fib (n-1) := by
  have h := (physical_birth_clock z n).2.2.2.2.2.2.2.2.1 hn
  rw [← (physical_birth_clock z n).2.2.2.2.1,
    ← (physical_birth_clock z (n-1)).2.2.2.2.1]
  exact h.2.1

private theorem mature_word_take (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    ((physicalBirthClock z n).births.take (clockSum (n-1))) =
      (physicalBirthClock z (n-1)).births := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨r, he, _, _⟩ := (physical_birth_clock z n).2.2.2.2.2.2.2.1
    rw [Nat.add_sub_cancel, ← (physical_birth_clock z n).2.2.2.2.1, he, List.take_append_length]

private theorem same_incidence {s t : Shape}
    (h : ∀ p, p ∈ incidenceAddresses s ↔ p ∈ incidenceAddresses t) : s = t := by
  induction s generalizing t with
  | of a =>
    cases t with
    | of b => cases a; cases b; rfl
    | mul l r =>
      have hp : [false] ∈ incidenceAddresses (.mul l r) :=
        (mem_incidenceAddresses _ _).mpr (by simp [present, atTree])
      have hz := (h [false]).mpr hp
      simp [incidenceAddresses] at hz
  | mul l r il ir =>
    cases t with
    | of a =>
      have hp : [false] ∈ incidenceAddresses (.mul l r) :=
        (mem_incidenceAddresses _ _).mpr (by simp [present, atTree])
      have hz := (h [false]).mp hp
      simp [incidenceAddresses] at hz
    | mul l' r' =>
      have hL := il (t:=l') (fun p => by
        simpa [mem_incidenceAddresses, present, atTree] using h (false::p))
      have hR := ir (t:=r') (fun p => by
        simpa [mem_incidenceAddresses, present, atTree] using h (true::p))
      rw [hL,hR]

private theorem same_frontier {s t : Shape}
    (h : ∀ p, p ∈ frontierAddresses s ↔ p ∈ frontierAddresses t) : s = t := by
  apply same_incidence
  intro p
  rw [incidenceAddresses_eq_prefixClosure, incidenceAddresses_eq_prefixClosure]
  exact exists_congr fun q => h (p++q)

private theorem arbitrary_newest (z : BirthStream) (n : Nat) (hn : 2 ≤ n)
    (bits : List Bool) (hb : bits.length = Nat.fib (n-1)) :
    ∃! t : Labelled, ∃ z' : BirthStream,
      (physicalBirthClock z' n).tree = t ∧
      shape t = shape (physicalBirthClock z n).tree ∧
      prefixBits z' (clockSum n) = prefixBits z (clockSum (n-1)) ++ bits := by
  let p := prefixBits z (clockSum (n-1))
  let z' := extendBits (p ++ bits)
  have hlen : (p ++ bits).length = clockSum n := by
    have hgap := clock_gap z n hn
    have hle := clock_sum_le n
    simp only [List.length_append, p, prefix_length, hb]
    omega
  have hf : prefixBits z' (clockSum n) = p ++ bits := by
    rw [← hlen]
    exact prefix_from_bits _
  have hp : prefixBits z' (clockSum (n-1)) = p := by
    rw [← prefix_take z' (clock_sum_le n), hf, ← prefix_length z (clockSum (n-1))]
    exact List.take_append_length
  refine ⟨(physicalBirthClock z' n).tree, ⟨z', rfl,
    (shape_prefix_actual z' z n hn).mpr hp, hf⟩, ?_⟩
  intro t ht
  obtain ⟨q, hT, _, hP⟩ := ht
  rw [← hT]
  exact (exact_labelled_prefix q z' n).mpr (hP.trans hf.symm)

private theorem only_newest (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n)
    (hs : shape (physicalBirthClock z n).tree = shape (physicalBirthClock z' n).tree) :
    ∃ bits : List Bool, bits.length = Nat.fib (n-1) ∧
      prefixBits z' (clockSum n) = prefixBits z (clockSum (n-1)) ++ bits := by
  let word := prefixBits z' (clockSum n)
  have hM := (shape_prefix_actual z z' n hn).mp hs
  refine ⟨word.drop (clockSum (n-1)), ?_, ?_⟩
  · rw [List.length_drop, prefix_length, clock_gap z n hn]
  · rw [hM, ← prefix_take z' (clock_sum_le n)]
    exact (List.take_append_drop _ word).symm

/-- Incidence determines exactly the mature ordered birth data; full labels
determine the entire used prefix. The fixed source sees no additional port,
and the newest bits admit all finite assignments at fixed incidence. -/
theorem exact_ordered_birth_prefix (z : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    let t := (physicalBirthClock z n).tree
    let s := shape t
    matureFromShape s = some (n, (physicalBirthClock z (n-1)).births) ∧
    (shapeFromIncidence (incidenceAddresses s)).bind epochFromShape = some n ∧
    (shapeFromFrontier (frontierAddresses s)).bind epochFromShape = some n ∧
    shapeFromIncidence (incidenceAddresses s) = some s ∧
    shapeFromFrontier (frontierAddresses s) = some s ∧
    (∀ p, (p ∈ incidenceAddresses s ↔ present s p = true) ∧
      (p ∈ frontierAddresses s ↔ atTree s p = some tip) ∧
      (p ∈ incidenceAddresses s ↔ ∃ q : Address, p ++ q ∈ frontierAddresses s) ∧
      (p ∈ frontierAddresses s ↔ p ∈ incidenceAddresses s ∧
        ∀ q : Address, p ++ q ∈ incidenceAddresses s → q = [])) ∧
    (∀ z' : BirthStream,
      ((∀ p, p ∈ incidenceAddresses s ↔
        p ∈ incidenceAddresses (shape (physicalBirthClock z' n).tree)) ↔
          prefixBits z (clockSum (n-1)) = prefixBits z' (clockSum (n-1))) ∧
      ((∀ p, p ∈ frontierAddresses s ↔
        p ∈ frontierAddresses (shape (physicalBirthClock z' n).tree)) ↔
          prefixBits z (clockSum (n-1)) = prefixBits z' (clockSum (n-1))) ∧
      (t = (physicalBirthClock z' n).tree ↔ prefixBits z (clockSum n) = prefixBits z' (clockSum n))) ∧
    (physicalBirthClock z n).births.take (clockSum (n-1)) = (physicalBirthClock z (n-1)).births ∧
    maturePrefix s = some (n, prefixBits z (clockSum (n-1))) ∧
    shapeOfPrefix n (prefixBits z (clockSum (n-1))) = s ∧
    completeFromLabelled t = some (n, (physicalBirthClock z n).births) ∧
    completePrefix t = some (n, prefixBits z (clockSum n)) ∧
    labelsOfPrefix n (prefixBits z (clockSum n)) = t ∧
    (∀ bits : List Bool, bits.length = clockSum (n-1) →
      maturePrefix (shapeOfPrefix n bits) = some (n, bits)) ∧
    (∀ bits : List Bool, bits.length = clockSum n →
      completePrefix (labelsOfPrefix n bits) = some (n, bits)) ∧
    (∀ z' : BirthStream, s = shape (physicalBirthClock z' n).tree →
      ∃ bits : List Bool, bits.length = Nat.fib (n-1) ∧
        prefixBits z' (clockSum n) = prefixBits z (clockSum (n-1)) ++ bits) ∧
    (∀ bits : List Bool, bits.length = Nat.fib (n-1) →
      ∃! w : Labelled, ∃ z' : BirthStream,
        (physicalBirthClock z' n).tree = w ∧ shape w = s ∧
        prefixBits z' (clockSum n) = prefixBits z (clockSum (n-1)) ++ bits) := by
  dsimp only
  let s := shape (physicalBirthClock z n).tree
  have m := mature_actual z n hn
  have f := complete_actual z n hn
  have hE := epochFromShape_physical z n hn
  refine ⟨m, ?_, ?_, shapeFromIncidence_roundtrip s, shapeFromFrontier_roundtrip s,
    ?_, ?_, mature_word_take z n hn, mature_bits_actual z n hn, ?_, f,
    complete_bits_actual z n hn, ?_, ?_, ?_, fun z' => only_newest z z' n hn,
    arbitrary_newest z n hn⟩
  · rw [shapeFromIncidence_roundtrip]
    exact hE
  · rw [shapeFromFrontier_roundtrip]
    exact hE
  · intro p
    exact ⟨mem_incidenceAddresses s p, mem_frontierAddresses s p,
      incidenceAddresses_eq_prefixClosure s p, frontierAddresses_iff_maximal s p⟩
  · intro z'
    have h := shape_prefix_actual z z' n hn
    exact ⟨⟨fun hI => h.mp (same_incidence hI), fun hp => by rw [h.mpr hp]; simp⟩,
      ⟨fun hF => h.mp (same_frontier hF), fun hp => by rw [h.mpr hp]; simp⟩,
      exact_labelled_prefix z z' n⟩
  · apply (shape_prefix_actual _ _ n hn).mpr
    have h := prefix_from_bits (prefixBits z (clockSum (n-1)))
    rw [prefix_length] at h
    exact h
  · apply (exact_labelled_prefix _ _ n).mpr
    have h := prefix_from_bits (prefixBits z (clockSum n))
    rw [prefix_length] at h
    exact h
  · intro bits hb
    unfold shapeOfPrefix
    rw [mature_bits_actual _ _ hn, ← hb, prefix_from_bits]
  · intro bits hb
    unfold labelsOfPrefix
    rw [complete_bits_actual _ _ hn, ← hb, prefix_from_bits]


#print axioms exact_ordered_birth_prefix

end D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
