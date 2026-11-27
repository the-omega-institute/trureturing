/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/PublicRowSeedReadiness
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/PublicRowSeedReadiness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Exact seed-only readiness for a supplied finite binary recurrence row. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
import Mathlib.Algebra.BigOperators.Fin

/-! Recover only the seed once the public row's full initial prefix is mature. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness

open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
open D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
open scoped BigOperators

/-- The zero-based stream associated with a finite Boolean recurrence row. -/
def rowStream {r : Nat} (c seed : Fin r → Bool) (n : Nat) : Bool :=
  if h : n < r then seed ⟨n, h⟩
  else (List.ofFn (fun j : Fin r =>
    c j && rowStream c seed (n - r + j.val))).foldl Bool.xor false
termination_by n
decreasing_by omega

private theorem rowStream_initial {r : Nat} (c seed : Fin r → Bool) (j : Fin r) :
    rowStream c seed j.val = seed j := by
  rw [rowStream, dite_eq_left j.isLt]

private theorem rowStream_zero (c seed : Fin 0 → Bool) (n : Nat) :
    rowStream c seed n = false := by
  rw [rowStream]
  simp

private theorem rowStream_recurrence {r : Nat} (c seed : Fin r → Bool) (i : Nat) :
    rowStream c seed (i + r) =
      (List.ofFn (fun j : Fin r => c j && rowStream c seed (i + j.val))).foldl Bool.xor false := by
  rw [rowStream, dite_eq_right (by omega), Nat.add_sub_cancel]

private theorem rowStream_unique {r : Nat} (c seed : Fin r → Bool) (s : Nat → Bool)
    (hseed : ∀ j : Fin r, s j.val = seed j)
    (hrec : ∀ i : Nat, s (i + r) =
      (List.ofFn (fun j : Fin r => c j && s (i + j.val))).foldl Bool.xor false) :
    s = rowStream c seed := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < r
    · exact (hseed ⟨n, hn⟩).trans (rowStream_initial c seed ⟨n, hn⟩).symm
    · have hnr : n - r + r = n := by omega
      rw [← hnr, hrec, rowStream_recurrence]
      have he : (fun j : Fin r => c j && s (n - r + j.val)) =
          (fun j : Fin r => c j && rowStream c seed (n - r + j.val)) := by
        funext j
        rw [ih _ (by omega)]
      rw [he]

/-- Birth indices are one-based; a valid birth index is positive. -/
def birthStream {r : Nat} (c seed : Fin r → Bool) (j : Nat) : Bool :=
  rowStream c seed (j - 1)

private theorem birthStream_succ {r : Nat} (c seed : Fin r → Bool) (i : Nat) :
    birthStream c seed (i + 1) = rowStream c seed i := rfl



def bitNat (b : Bool) : Nat := if b then 1 else 0

private theorem bitNat_and (a b : Bool) :
    bitNat (a && b) = bitNat a * bitNat b := by
  cases a <;> cases b <;> decide

private theorem bitNat_xor (a b : Bool) :
    bitNat (a ^^ b) = (bitNat a + bitNat b) % 2 := by
  cases a <;> cases b <;> decide

private theorem bitNat_lt (a : Bool) : bitNat a < 2 := by
  cases a <;> decide

private theorem bitNat_foldl (xs : List (Bool × Bool)) (seed : Bool) :
    bitNat (xs.foldl (fun z x => z ^^ (x.1 && x.2)) seed) =
      (bitNat seed + (xs.map (fun x => bitNat x.1 * bitNat x.2)).sum) % 2 := by
  induction xs generalizing seed with
  | nil => simpa using (Nat.mod_eq_of_lt (bitNat_lt seed)).symm
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, bitNat_xor, bitNat_and]
    omega

private theorem bitNat_dot_foldl {r : Nat} (a b : Fin r → Bool) :
    bitNat ((List.ofFn fun j => (a j, b j)).foldl
      (fun z x => z ^^ (x.1 && x.2)) false) =
        (List.ofFn fun j => bitNat (a j) * bitNat (b j)).sum % 2 := by
  rw [bitNat_foldl, List.map_ofFn]
  simp only [bitNat, Bool.false_eq_true, ite_false, Nat.zero_add]
  rfl




private theorem bitNat_dot_finset_foldl {r : Nat} (a b : Fin r → Bool) :
    bitNat ((List.ofFn fun j => (a j, b j)).foldl
      (fun z x => z ^^ (x.1 && x.2)) false) =
        (∑ j, bitNat (a j) * bitNat (b j)) % 2 := by
  rw [bitNat_dot_foldl, List.sum_ofFn]



/-- Fixed public recurrence, varied only through the finite initial seed. -/
def rowTree {r : Nat} (c seed : Fin r → Bool) (n : Nat) : Labelled :=
  (physicalBirthClock (birthStream c seed) n).tree

def matureSize (n : Nat) : Nat := clockSum (n-1)

def compatibleSeeds {r : Nat} (c a b : Fin r → Bool) (n : Nat) : Prop :=
  shape (rowTree c a n) = shape (rowTree c b n)

/-- An initial seed suitable for a public row, when the given prefix is long enough. -/
def seedFromPrefix {r : Nat} (bits : List Bool) (i : Fin r) : Bool := bits[i.val]?.getD false

/-- Only the already available finite geometric inverse is used; an insufficient
prefix is rejected, and no other access to the source is available. -/
def installRow {r : Nat} (c : Fin r → Bool) (shape : Shape) : Option (Nat × BirthStream) := do
  let (n, bits) ← maturePrefix shape
  if r ≤ bits.length then
    pure (n, birthStream c (seedFromPrefix bits))
  else none

private theorem mature_size_value (n : Nat) (hn : 2 ≤ n) :
    matureSize n = Nat.fib n - 1 := by
  let z : BirthStream := fun _ => false
  have hh := (physical_birth_clock z n).2.2.2.2.2.2.2.2.1 hn
  exact ((physical_birth_clock z (n-1)).2.2.2.2.1).symm.trans hh.1

private theorem used_gap (n : Nat) (hn : 2 ≤ n) : matureSize n < clockSum n := by
  let z : BirthStream := fun _ => false
  have hh := (physical_birth_clock z n).2.2.2.2.2.2.2.2.1 hn
  have eq := hh.2.1
  rw [(physical_birth_clock z n).2.2.2.2.1,
    (physical_birth_clock z (n-1)).2.2.2.2.1] at eq
  have hp := Nat.fib_pos.mpr (by omega : 0 < n-1)
  unfold matureSize
  omega

private theorem same_incidence_prefix (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    shape (physicalBirthClock z n).tree = shape (physicalBirthClock z' n).tree ↔
      prefixBits z (matureSize n) = prefixBits z' (matureSize n) := by
  have a := exact_ordered_birth_prefix z n hn
  have b := exact_ordered_birth_prefix z' n hn
  constructor
  · intro h
    exact ((a.2.2.2.2.2.2.1 z').1).mp (fun p => by rw [h])
  · intro h
    exact a.2.2.2.2.2.2.2.2.2.1.symm.trans (h ▸ b.2.2.2.2.2.2.2.2.2.1)

private theorem same_labels_prefix (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n) :
    (physicalBirthClock z n).tree = (physicalBirthClock z' n).tree ↔
      prefixBits z (clockSum n) = prefixBits z' (clockSum n) :=
  ((exact_ordered_birth_prefix z n hn).2.2.2.2.2.2.1 z').2.2

private theorem row_bits_iff {r : Nat} (c a b : Fin r → Bool) (k : Nat) :
    prefixBits (birthStream c a) k = prefixBits (birthStream c b) k ↔
      ∀ j, j < k → rowStream c a j = rowStream c b j := by
  unfold prefixBits
  rw [List.map_inj_left]
  simp [consume, birthStream_succ]

private theorem enough_implies_seed_eq {r : Nat} (c a b : Fin r → Bool) (n : Nat) (hn : 2 ≤ n)
    (hr : r ≤ matureSize n) (h : compatibleSeeds c a b n) : a = b := by
  have e := (same_incidence_prefix _ _ n hn).mp h
  have he := (row_bits_iff c a b (matureSize n)).mp e
  funext j
  rw [← rowStream_initial c a j, ← rowStream_initial c b j]
  exact he _ (j.isLt.trans_le hr)

private theorem install_actual {r : Nat} (c seed : Fin r → Bool) (n : Nat) (hn : 2 ≤ n)
    (hr : r ≤ matureSize n) :
    installRow c (shape (rowTree c seed n)) = some (n, birthStream c seed) := by
  let z := birthStream c seed
  let bits := prefixBits z (matureSize n)
  have hm : maturePrefix (shape (rowTree c seed n)) = some (n, bits) :=
    (exact_ordered_birth_prefix z n hn).2.2.2.2.2.2.2.2.1
  have hlen : bits.length = matureSize n := by simp [bits, prefixBits]
  have hs : seedFromPrefix (r:=r) bits = seed := by
    funext j
    have hj := j.isLt.trans_le hr
    simp only [seedFromPrefix, bits, prefixBits, List.getElem?_map, List.getElem?_range hj,
      Option.map_some, Option.getD_some, consume]
    exact (birthStream_succ c seed j.val).trans (rowStream_initial c seed j)
  unfold installRow
  rw [hm]
  change (if r ≤ bits.length then some (n, birthStream c (seedFromPrefix bits)) else none) = _
  rw [ite_eq_left (by simpa [hlen] using hr), hs]

private theorem label_shape_presence (t : Labelled) (p : Address) :
    present t p = present (shape t) p := by
  induction p generalizing t with
  | nil => simp [present, atTree]
  | cons b p ih =>
    cases t with
    | of c => cases b <;> rfl
    | mul l r => cases b
                 · exact ih l
                 · exact ih r

private theorem actual_difference_at_word (z z' : BirthStream) (n : Nat) (hn : 2 ≤ n)
    (h : prefixBits z (matureSize n) ≠ prefixBits z' (matureSize n)) :
    ∃ p, present (physicalBirthClock z n).tree p ≠ present (physicalBirthClock z' n).tree p := by
  by_contra! uniform
  apply h
  have a := exact_ordered_birth_prefix z n hn
  have b := exact_ordered_birth_prefix z' n hn
  apply ((a.2.2.2.2.2.2.1 z').1).mp
  intro p
  rw [(a.2.2.2.2.2.1 p).1, (b.2.2.2.2.2.1 p).1,
    ← label_shape_presence, ← label_shape_presence, uniform]

private theorem hidden_seed_witness {r : Nat} (c seed : Fin r → Bool) (n : Nat)
    (hn : 2 ≤ n) (hr : matureSize n < r) :
    ∃ b : Fin r → Bool, compatibleSeeds c seed b n ∧ rowTree c seed n ≠ rowTree c b n ∧
      ∃ p, present (rowTree c seed (n+1)) p ≠ present (rowTree c b (n+1)) p := by
  let v := matureSize n
  let b : Fin r → Bool := fun j => if j.val = v then !seed j else seed j
  let j : Fin r := ⟨v, hr⟩
  have hb : rowStream c seed v ≠ rowStream c b v := by
    change rowStream c seed j.val ≠ rowStream c b j.val
    rw [rowStream_initial, rowStream_initial]
    change seed j ≠ (if j.val = v then !seed j else seed j)
    cases seed j <;> simp [j]
  have hp : prefixBits (birthStream c seed) v = prefixBits (birthStream c b) v := by
    apply (row_bits_iff c seed b v).mpr
    intro i hi
    let k : Fin r := ⟨i, by omega⟩
    change rowStream c seed k.val = rowStream c b k.val
    rw [rowStream_initial, rowStream_initial]
    have h' : k.val ≠ v := by dsimp [k]; omega
    simp [b, h']
  have hor : prefixBits (birthStream c seed) (clockSum n) ≠
      prefixBits (birthStream c b) (clockSum n) := by
    intro e
    apply hb
    exact (row_bits_iff c seed b (clockSum n)).mp e v (used_gap n hn)
  refine ⟨b, (same_incidence_prefix _ _ n hn).mpr hp,
    fun he => hor ((same_labels_prefix _ _ n hn).mp he), ?_⟩
  apply actual_difference_at_word _ _ (n+1) (by omega)
  simpa [matureSize] using hor



inductive Action
  | read : Address → Action
  | update
  deriving DecidableEq

inductive Reply
  | answer : Bool → Reply
  | ack
  deriving DecidableEq

abbrev Behavior := List Reply × List (List Address × Labelled)

def nextEpoch (n : Nat) : Action → Nat
  | .read _ => n
  | .update => n + 1

def reply (z : BirthStream) (n : Nat) : Action → Reply
  | .read p => .answer (present (physicalBirthClock z n).tree p)
  | .update => .ack

def updateSnapshots (z : BirthStream) (n : Nat) : Action → List (List Address × Labelled)
  | .read _ => []
  | .update =>
    let t := (physicalBirthClock z (n + 1)).tree
    [(incidenceAddresses (shape t), t)]

/-- Observe replies, retaining actual update snapshots as a separate task result. -/
def eval (z : BirthStream) (n : Nat) : List Action → Behavior
  | [] => ([], [])
  | a :: as =>
    let tail := eval z (nextEpoch n a) as
    (reply z n a :: tail.1, updateSnapshots z n a ++ tail.2)

private theorem update_is_step (z : BirthStream) (n : Nat) :
    Step (physicalBirthClock z n).tree (physicalBirthClock z (n + 1)).tree :=
  (physical_birth_clock z n).2.2.1

private theorem eval_eq_of_birthStream_eq {z z' : BirthStream} (h : z = z') (n : Nat)
    (as : List Action) : eval z n as = eval z' n as := by
  subst z'
  rfl

private theorem reply_eq_on_singleton {z z' : BirthStream} {n : Nat}
    (h : ∀ as, eval z n as = eval z' n as) (a : Action) :
    reply z n a = reply z' n a := by
  exact List.cons.inj (congrArg Prod.fst (h [a])) |>.1

private theorem eval_eq_on_tail {z z' : BirthStream} {n : Nat}
    (h : ∀ as, eval z n as = eval z' n as) (a : Action) :
    ∀ as, eval z (nextEpoch n a) as = eval z' (nextEpoch n a) as := by
  intro as
  have hu : updateSnapshots z n a = updateSnapshots z' n a := by
    simpa [eval] using congrArg Prod.snd (h [a])
  have he := h (a :: as)
  apply Prod.ext
  · exact List.cons.inj (congrArg Prod.fst he) |>.2
  · have hs := congrArg Prod.snd he
    change updateSnapshots z n a ++ (eval z (nextEpoch n a) as).2 =
      updateSnapshots z' n a ++ (eval z' (nextEpoch n a) as).2 at hs
    rw [hu] at hs
    exact List.append_cancel_left hs

/-- Bounded adaptive policy receives only the observed prefix, not the task snapshots. -/
def adaptiveScript (policy : List Reply → Option Action) (z : BirthStream) :
    Nat → Nat → List Reply → List Action
  | 0, _, _ => []
  | k + 1, n, hist =>
    match policy hist with
    | none => []
    | some a =>
      a :: adaptiveScript policy z k (nextEpoch n a) (hist ++ [reply z n a])

private theorem adaptiveScript_eq_of_eval_eq {z z' : BirthStream} {n : Nat}
    (h : ∀ as, eval z n as = eval z' n as)
    (policy : List Reply → Option Action) (fuel : Nat) (hist : List Reply) :
    adaptiveScript policy z fuel n hist = adaptiveScript policy z' fuel n hist := by
  induction fuel generalizing n hist with
  | zero => rfl
  | succ k ih =>
    cases hh : policy hist with
    | none => simp [adaptiveScript, hh]
    | some a =>
      simpa only [adaptiveScript, hh, reply_eq_on_singleton h a, List.cons.injEq, true_and] using
        ih (eval_eq_on_tail h a) (hist ++ [reply z' n a])

def adaptiveEval (policy : List Reply → Option Action) (z : BirthStream)
    (fuel n : Nat) (hist : List Reply) : List Action × Behavior :=
  let as := adaptiveScript policy z fuel n hist
  (as, eval z n as)

private theorem adaptive_eq_of_eval_eq {z z' : BirthStream} {n : Nat}
    (h : ∀ as, eval z n as = eval z' n as)
    (policy : List Reply → Option Action) (fuel : Nat) (hist : List Reply) :
    adaptiveEval policy z fuel n hist = adaptiveEval policy z' fuel n hist := by
  dsimp only [adaptiveEval]
  rw [adaptiveScript_eq_of_eval_eq h, h]

private theorem eval_two_step_ne {z z' : BirthStream} {n : Nat} {p : Address}
    (h : present (physicalBirthClock z (n + 1)).tree p ≠
      present (physicalBirthClock z' (n + 1)).tree p) :
    (eval z n [.update, .read p]).1 ≠ (eval z' n [.update, .read p]).1 := by
  intro he
  apply h
  have ha := (List.cons.inj he).2
  exact Reply.answer.inj ((List.cons.inj ha).1)


/-- At an attained cut from the fixed alpha source, the public row leaves
exactly the finite initial seed to be learned. All three readiness tests
have the same sharp mature-prefix threshold for each actual seed. -/
theorem public_row_seed_readiness (r : Nat) (c seed : Fin r → Bool) (n : Nat) (hn : 2 ≤ n) :
    (r ≤ matureSize n ↔ ∀ b : Fin r → Bool, compatibleSeeds c seed b n → ∀ p : Address,
      present (rowTree c seed (n+1)) p = present (rowTree c b (n+1)) p) ∧
    (r ≤ matureSize n ↔ ∀ b : Fin r → Bool, compatibleSeeds c seed b n →
       rowTree c seed n = rowTree c b n) ∧
    (r ≤ matureSize n ↔ ∀ b : Fin r → Bool, compatibleSeeds c seed b n →
      (∀ as : List Action, eval (birthStream c seed) n as = eval (birthStream c b) n as) ∧
      (∀ (policy : List Reply → Option Action) (fuel : Nat) (hist : List Reply),
        adaptiveEval policy (birthStream c seed) fuel n hist =
        adaptiveEval policy (birthStream c b) fuel n hist)) ∧
    matureSize n = Nat.fib n - 1 ∧
    maturePrefix (shape (rowTree c seed n)) =
      some (n, prefixBits (birthStream c seed) (matureSize n)) ∧
    (r ≤ matureSize n →
      installRow c (shape (rowTree c seed n)) = some (n, birthStream c seed) ∧
      (shapeFromIncidence (incidenceAddresses (shape (rowTree c seed n)))).bind (installRow c) =
        some (n, birthStream c seed) ∧
      (shapeFromFrontier (frontierAddresses (shape (rowTree c seed n)))).bind (installRow c) =
        some (n, birthStream c seed)) ∧
    (∀ j : Fin r, rowStream c seed j.val = seed j) ∧
    (∀ i : Nat, rowStream c seed (i+r) =
      (List.ofFn (fun j : Fin r => c j && rowStream c seed (i+j.val))).foldl Bool.xor false) ∧
    (∀ i : Nat, bitNat (rowStream c seed (i+r)) =
      (∑ j : Fin r, bitNat (c j) * bitNat (rowStream c seed (i+j.val))) % 2) ∧
    (∀ s : Nat → Bool, (∀ j : Fin r, s j.val = seed j) →
      (∀ i : Nat, s (i+r) = (List.ofFn (fun j : Fin r => c j && s (i+j.val))).foldl Bool.xor false) →
      s = rowStream c seed) ∧
    (r = 0 → ∀ i, rowStream c seed i = false) ∧
    Step (rowTree c seed n) (rowTree c seed (n+1)) ∧
    reply (birthStream c seed) n .update = .ack := by
  have old := exact_ordered_birth_prefix (birthStream c seed) n hn
  refine ⟨?_, ?_, ?_, mature_size_value n hn, old.2.2.2.2.2.2.2.2.1, ?_,
    rowStream_initial c seed, rowStream_recurrence c seed, ?_, rowStream_unique c seed, ?_,
    update_is_step _ _, rfl⟩
  · constructor
    · intro h b hb p
      rw [enough_implies_seed_eq c seed b n hn h hb]
    · intro h
      by_contra! hs
      obtain ⟨b, hb, _, p, hp⟩ := hidden_seed_witness c seed n hn hs
      exact hp (h b hb p)
  · constructor
    · intro h b hb
      rw [enough_implies_seed_eq c seed b n hn h hb]
    · intro h
      by_contra! hs
      obtain ⟨b, hb, ht, _, _⟩ := hidden_seed_witness c seed n hn hs
      exact ht (h b hb)
  · constructor
    · intro h b hb
      have he : birthStream c seed = birthStream c b :=
        congrArg (birthStream c) (enough_implies_seed_eq c seed b n hn h hb)
      have fixed := eval_eq_of_birthStream_eq he n
      exact ⟨fixed, fun policy fuel hist => adaptive_eq_of_eval_eq fixed policy fuel hist⟩
    · intro h
      by_contra! hs
      obtain ⟨b, hb, _, p, hp⟩ := hidden_seed_witness c seed n hn hs
      exact eval_two_step_ne hp (congrArg Prod.fst ((h b hb).1 [.update, .read p]))
  · intro h
    have hi := install_actual c seed n hn h
    refine ⟨hi, ?_, ?_⟩
    · have e : shapeFromIncidence (incidenceAddresses (shape (rowTree c seed n))) =
          some (shape (rowTree c seed n)) := old.2.2.2.1
      rw [e]
      exact hi
    · have e : shapeFromFrontier (frontierAddresses (shape (rowTree c seed n))) =
          some (shape (rowTree c seed n)) := old.2.2.2.2.1
      rw [e]
      exact hi
  · intro i
    rw [rowStream_recurrence]
    let s (j : Fin r) := rowStream c seed (i+j.val)
    have hm : List.ofFn (fun j : Fin r => c j && s j) =
        (List.ofFn (fun j : Fin r => (c j, s j))).map (fun p => p.1 && p.2) := by
      rw [List.map_ofFn]
      rfl
    change bitNat ((List.ofFn (fun j : Fin r => c j && s j)).foldl Bool.xor false) = _
    rw [hm, List.foldl_map]
    exact bitNat_dot_finset_foldl c s
  · intro h
    subst r
    exact rowStream_zero c seed


#print axioms public_row_seed_readiness

end D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
