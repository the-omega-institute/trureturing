/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301; premises=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_certificate,D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_residual_succ
   digest: Exact weighted row transfer and mask-dependent acceptance. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding

/-! Exact weighted row transfer and mask-dependent acceptance. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open scoped BigOperators

set_option warningAsError true

def index (p : Bool) (a b : Fin 6) : ℕ := 36 * p.toNat + 6 * a.val + b.val

private def masks : Array Nat := #[
  270217008436777545, 128071114403398412, 54900814598112142,
  164703062273556495, 3431300914245632, 62534724628672,
  516508834544903919713, 2877703053061436623140, 10005562255212934,
  9436085025243143, 2656341440558788669440, 442721884569625311424,
  224819693604493593713, 2622896423032116481072, 58799221054950605970,
  218874804961283, 3541775076595169492992, 1348918240792654384320,
  674621210400081051705, 2473611102592629211192, 57375859278872576024,
  1026824641867677705, 4132070676395226038272, 1798557548836783652864,
  899494946375469334528, 2698494972289949614080, 56218434179000434688,
  1024568928316162048, 4427235466228163297280, 2098317138385279582208,
  16393102643634996736, 7027304268558354176, 21081991971015231360,
  439206517023440896, 8004444752470016, 34587777079907525760,
  270217008436777545, 516508834544903919713, 224819693604493593713,
  674621210400081051705, 899494946375469334528, 16393102643634996736,
  128071114403398412, 2877703053061436623140, 2622896423032116481072,
  2473611102592629211192, 2698494972289949614080, 7027304268558354176,
  54900814598112142, 10005562255212934, 58799221054950605970,
  57375859278872576024, 56218434179000434688, 21081991971015231360,
  164703062273556495, 9436085025243143, 218874804961283,
  1026824641867677705, 1024568928316162048, 439206517023440896,
  3431300914245632, 2656341440558788669440, 3541775076595169492992,
  4132070676395226038272, 4427235466228163297280, 8004444752470016,
  62534724628672, 442721884569625311424, 1348918240792654384320,
  1798557548836783652864, 2098317138385279582208, 34587777079907525760]

private def rowMask (p : Bool) (a b : Fin 6) : ℕ := masks[index p a b]!

private theorem index_lt (q : Bool) (c d : Fin 6) : index q c d < 72 := by
  cases q <;> simp [index, Bool.toNat] <;> omega

set_option maxHeartbeats 0 in
-- Kernel reduction checks each pair of the 72 row and column edge types.
set_option maxRecDepth 50000 in
private theorem rowMask_spec (p q : Bool) (a b c d : Fin 6) :
    (rowMask p a b).testBit (index q c d) = decide (Cross p.toNat q.toNat a b c d) := by
  revert p q a b c d
  decide +kernel


def par (n : ℕ) : Bool := decide (n % 2 = 1)

private lemma par_toNat (n : ℕ) : (par n).toNat = n % 2 := by
  by_cases h : n % 2 = 1
  · simp [par, h]
  · simp [par, h]
    omega

lemma par_succ (n : ℕ) : par (n + 1) = !(par n) := by
  have inj : Function.Injective Bool.toNat := by
    intro a b hab
    cases a <;> cases b <;> first | rfl | contradiction
  have flip (a : Bool) : (!a).toNat = 1 - a.toNat := by cases a <;> rfl
  apply inj
  rw [flip, par_toNat, par_toNat, next_parity]

structure State where
  parity : Bool
  last : Fin 6
  mask : ℕ
  deriving DecidableEq

private def fullMask : ℕ := 2 ^ 72 - 1
private def start (a : Fin 6) : State := ⟨false, a, fullMask⟩
private def extend (s : State) (a : Fin 6) : State :=
  ⟨!s.parity, a, s.mask &&& rowMask s.parity s.last a⟩

private def Live (s : State) : Prop :=
  ∃ a : Fin 6, s.mask.testBit (index false 0 a) = true

private instance (s : State) : Decidable (Live s) := by
  unfold Live
  infer_instance

private lemma live_prev {s : State} {a : Fin 6} (h : Live (extend s a)) : Live s := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simpa [extend, Nat.testBit_and] using
    ((Bool.and_eq_true_iff.mp (by simpa only [extend, Nat.testBit_and] using hb)).1 :
      s.mask.testBit (index false 0 b) = true)⟩

abbrev Hist (α : Type) := List (α × ℤ)

def evalHist {α : Type} (xs : Hist α) (f : α → ℤ) : ℤ :=
  (xs.map fun (s, x) => x * f s).sum

@[simp] lemma eval_nil {α : Type} (f : α → ℤ) : evalHist [] f = 0 := rfl

@[simp] private lemma eval_cons {α : Type} (xs : Hist α) (f : α → ℤ) (s : α) (x : ℤ) :
    evalHist ((s, x)::xs) f = x * f s + evalHist xs f := rfl

@[simp] lemma eval_append {α : Type} (xs ys : Hist α) (f : α → ℤ) :
    evalHist (xs ++ ys) f = evalHist xs f + evalHist ys f := by
  simp [evalHist]

def scaleHist {α : Type} (c : ℤ) (xs : Hist α) : Hist α :=
  xs.map fun (s, x) => (s, c * x)

@[simp] lemma eval_scale {α : Type} (xs : Hist α) (f : α → ℤ) (c : ℤ) :
    evalHist (scaleHist c xs) f = c * evalHist xs f := by
  induction xs with
  | nil => simp [scaleHist]
  | cons pair tail ih =>
    obtain ⟨s, x⟩ := pair
    change (c * x) * f s + evalHist (scaleHist c tail) f =
      c * (x * f s + evalHist tail f)
    rw [ih]
    ring

private def mergeHead {α : Type} [DecidableEq α] (s : α) (x : ℤ) :
    Hist α → Hist α
  | [] => if x = 0 then [] else [(s, x)]
  | (t, y)::ys =>
    if s = t then
      if x + y = 0 then ys else (t, x + y)::ys
    else
      if x = 0 then (t, y)::ys else (s, x)::(t, y)::ys

private lemma eval_mergeHead {α : Type} [DecidableEq α] (s : α) (x : ℤ)
    (xs : Hist α) (f : α → ℤ) :
    evalHist (mergeHead s x xs) f = x * f s + evalHist xs f := by
  cases xs with
  | nil =>
    simp [mergeHead]
    split <;> simp_all
  | cons pair tail =>
    obtain ⟨t, y⟩ := pair
    simp only [mergeHead]
    split
    · subst t
      split
      · rename_i hh
        simp only [eval_cons]
        linear_combination -(congrArg (fun z : ℤ => z * f s) hh)
      · simp only [eval_cons]
        ring
    · split <;> simp_all

private def squash {α : Type} [DecidableEq α] (xs : Hist α) : Hist α :=
  xs.foldr (fun (s, x) ds => mergeHead s x ds) []

private lemma eval_squash {α : Type} [DecidableEq α] (xs : Hist α) (f : α → ℤ) :
    evalHist (squash xs) f = evalHist xs f := by
  induction xs with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨s, x⟩ := pair
    change evalHist (mergeHead s x (squash tail)) f = _
    simp [eval_mergeHead, ih]

private def mergeRows {α : Type} (key : α → ℕ) : ℕ → Hist α → Hist α → Hist α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x::xs, [] => x::xs
  | fuel + 1, x::xs, y::ys =>
    if key x.1 ≤ key y.1 then x :: mergeRows key fuel xs (y::ys)
    else y :: mergeRows key fuel (x::xs) ys

private lemma eval_mergeRows {α : Type} (key : α → ℕ) (fuel : ℕ)
    (xs ys : Hist α) (f : α → ℤ) :
    evalHist (mergeRows key fuel xs ys) f = evalHist xs f + evalHist ys f := by
  induction fuel generalizing xs ys with
  | zero => exact eval_append _ _ _
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeRows]
    | cons pair xs =>
      cases ys with
      | nil => simp [mergeRows]
      | cons pair' ys =>
        obtain ⟨x, a⟩ := pair
        obtain ⟨y, b⟩ := pair'
        simp only [mergeRows]
        split <;> simp only [eval_cons, ih] <;> ring

private def pairRuns {α : Type} (key : α → ℕ) : List (Hist α) → List (Hist α)
  | xs::ys::rest => mergeRows key (xs.length + ys.length) xs ys :: pairRuns key rest
  | rest => rest

private lemma eval_pairRuns {α : Type} (key : α → ℕ) (runs : List (Hist α)) (f : α → ℤ) :
    evalHist (pairRuns key runs).flatten f = evalHist runs.flatten f := by
  match runs with
  | [] => rfl
  | [_] => rfl
  | xs::ys::rest =>
    simp only [pairRuns, List.flatten_cons, eval_append, eval_mergeRows,
      eval_pairRuns key rest f, add_assoc]

private def finishRuns {α : Type} (key : α → ℕ) :
    ℕ → List (Hist α) → Hist α
  | 0, runs => runs.flatten
  | _ + 1, [] => []
  | _ + 1, [xs] => xs
  | n + 1, xs::ys::rest => finishRuns key n (pairRuns key (xs::ys::rest))

private lemma eval_finishRuns {α : Type} (key : α → ℕ) (fuel : ℕ)
    (runs : List (Hist α)) (f : α → ℤ) :
    evalHist (finishRuns key fuel runs) f = evalHist runs.flatten f := by
  induction fuel generalizing runs with
  | zero => rfl
  | succ fuel ih =>
    cases runs with
    | nil => rfl
    | cons xs rest =>
      cases rest with
      | nil => simp [finishRuns]
      | cons ys rest => exact (ih _).trans (eval_pairRuns _ _ _)

def normalize {α : Type} [DecidableEq α] (key : α → ℕ) (xs : Hist α) : Hist α :=
  squash (finishRuns key xs.length (xs.map fun x => [x]))

@[simp] lemma eval_normalize {α : Type} [DecidableEq α] (key : α → ℕ)
    (xs : Hist α) (f : α → ℤ) : evalHist (normalize key xs) f = evalHist xs f := by
  rw [normalize, eval_squash, eval_finishRuns]
  have hs : (xs.map fun x => [x]).flatten = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  rw [hs]

def stateKey (s : State) : ℕ := s.mask * 12 + s.parity.toNat * 6 + s.last.val

private def initHist : Hist State := List.ofFn fun a : Fin 6 => (start a, 1)

private def out (s : State) (x : ℤ) : Hist State :=
  (List.ofFn (fun a : Fin 6 => extend s a)).filterMap
    (fun t => if Live t then some (t, x) else none)

def stepHist (xs : Hist State) : Hist State :=
  normalize stateKey (xs.flatMap fun (s, x) => out s x)

noncomputable def action (f : State → ℤ) (s : State) : ℤ :=
  ∑ a : Fin 6, if Live (extend s a) then f (extend s a) else 0

private lemma eval_out (s : State) (x : ℤ) (f : State → ℤ) :
    evalHist (out s x) f = x * action f s := by
  have aux (ts : List State) :
      evalHist (ts.filterMap (fun t => if Live t then some (t, x) else none)) f =
        (ts.map fun t => x * (if Live t then f t else 0)).sum := by
    induction ts with
    | nil => rfl
    | cons t ts ih => by_cases h : Live t <;> simp [h, ih]
  rw [out, aux, List.map_ofFn]
  rw [List.sum_ofFn, action, Finset.mul_sum]
  rfl

private lemma eval_step (xs : Hist State) (f : State → ℤ) :
    evalHist (stepHist xs) f = evalHist xs (action f) := by
  rw [stepHist, eval_normalize]
  induction xs with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨s, x⟩ := pair
    rw [List.flatMap_cons, eval_append, eval_cons, eval_out, ih]

def path : ℕ → Hist State
  | 0 => initHist
  | n + 1 => stepHist (path n)

def coefficients (v : ℕ → Hist State) : Hist State :=
  scaleHist 1 (v 10) ++ scaleHist (-3) (v 9) ++ scaleHist (-17) (v 8) ++
  scaleHist 57 (v 7) ++ scaleHist 86 (v 6) ++ scaleHist (-372) (v 5) ++
  scaleHist (-76) (v 4) ++ scaleHist 972 (v 3) ++ scaleHist (-360) (v 2) ++
  scaleHist (-864) (v 1) ++ scaleHist 576 (v 0)

def residualHist (h : ℕ) : Hist State :=
  normalize stateKey (coefficients (fun i => path (h + i + 1)))

def groupMask (xs : Hist State) : Hist ℕ :=
  normalize id (xs.map fun (s, x) => (s.mask, x))

lemma eval_group (xs : Hist State) (f : ℕ → ℤ) :
    evalHist (groupMask xs) f = evalHist xs (fun s => f s.mask) := by
  rw [groupMask, eval_normalize]
  simp [evalHist, List.map_map, Function.comp_def]

lemma eval_residual_succ (h : ℕ) (f : State → ℤ) :
    evalHist (residualHist (h + 1)) f = evalHist (residualHist h) (action f) := by
  simp only [residualHist, eval_normalize, coefficients, eval_append, eval_scale]
  have hs (i : ℕ) : evalHist (path (h + 1 + i + 1)) f = evalHist (path (h + i + 1)) (action f) := by
    rw [show h + 1 + i + 1 = (h + i + 1) + 1 by omega, path, eval_step]
  simp only [hs 0, hs 1, hs 2, hs 3, hs 4, hs 5, hs 6, hs 7, hs 8, hs 9, hs 10]


private def run : (h : ℕ) → Word h → State
  | 0, r => start (r 0)
  | h + 1, r => extend (run h (Fin.init r)) (r (Fin.last (h + 1)))

@[simp] private theorem run_parity (h : ℕ) (r : Word h) : (run h r).parity = par h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [run, extend, ih, par_succ]

@[simp] private theorem run_last (h : ℕ) (r : Word h) : (run h r).last = r (Fin.last h) := by
  cases h
  · rfl
  · rfl

private theorem run_mask (h : ℕ) (r : Word h) (q : Bool) (c d : Fin 6) :
    (run h r).mask.testBit (index q c d) = true ↔
      ∀ i : Fin h, Cross (par i.val).toNat q.toNat (r i.castSucc) (r i.succ) c d := by
  induction h with
  | zero =>
    change (2 ^ 72 - 1 : ℕ).testBit (index q c d) = true ↔ ∀ i : Fin 0, _
    rw [Nat.testBit_two_pow_sub_one]
    simp [index_lt]
  | succ h ih =>
    simp only [run, extend, Nat.testBit_and, Bool.and_eq_true, ih, run_parity,
      run_last, rowMask_spec, decide_eq_true_eq]
    constructor
    · rintro ⟨older, latest⟩ i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa [Fin.init] using latest
      · have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
        simpa [Fin.init, he] using older i
    · intro good
      constructor
      · intro i
        have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
        simpa [Fin.init, he] using good i.castSucc
      · simpa [Fin.init] using good (Fin.last h)

noncomputable def value (w : ℕ) (m : ℕ) : ℤ := by
  classical
  exact ∑ c : Word w,
    if c 0 = 0 ∧
      (∀ j : Fin w, m.testBit (index (par j.val) (c j.castSucc) (c j.succ)) = true)
    then 1 else 0

private lemma value_dead {w : ℕ} (hw : 0 < w) (s : State) (hs : ¬ Live s) :
    value w s.mask = 0 := by
  classical
  unfold value
  apply Finset.sum_eq_zero
  intro c hc
  split
  · rename_i hc
    have hbit := hc.2 ⟨0, hw⟩
    have z : (⟨0, hw⟩ : Fin w).castSucc = 0 := Fin.ext rfl
    simp only [z, hc.1, show par 0 = false by rfl] at hbit
    exact (hs ⟨_, hbit⟩).elim
  · rfl

private theorem sum_run (h : ℕ) (f : State → ℤ)
    (hf : ∀ s, ¬ Live s → f s = 0) :
    evalHist (path h) f = ∑ r : Word h, f (run h r) := by
  classical
  induction h generalizing f with
  | zero =>
    let e : Fin 6 ≃ Word 0 :=
      ⟨fun a _ => a, fun r => r 0, fun _ => rfl, fun r => by
        funext i
        have z : i = 0 := Fin.ext (by have hi := i.isLt; omega)
        rw [z]⟩
    have he := Fintype.sum_equiv e
      (fun a => f (start a)) (fun r => f (run 0 r)) (fun _ => rfl)
    rw [path, initHist, evalHist, List.map_ofFn, List.sum_ofFn]
    simpa only [Function.comp_apply, one_mul] using he
  | succ h ih =>
    have hh (s : State) (hs : ¬ Live s) : action f s = 0 := by
      unfold action
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun hx => hs (live_prev hx))
    rw [path, eval_step, ih _ hh]
    let e : Word h × Fin 6 ≃ Word (h + 1) :=
      (Equiv.prodComm (Word h) (Fin 6)).trans (Fin.snocEquiv (fun _ => Fin 6))
    have hsum := Fintype.sum_equiv e
      (fun p => f (extend (run h p.1) p.2)) (fun r => f (run (h + 1) r)) (by
        intro p
        simp [e, run, Fin.snocEquiv])
    rw [Fintype.sum_prod_type] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro r _
    unfold action
    apply Finset.sum_congr rfl
    intro a _
    split
    · rfl
    · rename_i hs
      exact (hf _ hs).symm

theorem count_transfer (h w : ℕ) (hh : 0 < h) (hw : 0 < w) :
    (C 3 3 h w : ℤ) = evalHist (path h) (fun s => value w s.mask) := by
  classical
  rw [sum_run _ _ (fun s => value_dead hw s)]
  rw [count_codes h w hh hw, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, ← Finset.sum_boole]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  unfold value
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [CodeOK, run_mask, par_toNat]
  apply propext
  constructor
  · exact fun ⟨hz, hcross⟩ => ⟨hz, fun j i => hcross i j⟩
  · exact fun ⟨hz, hcross⟩ => ⟨hz, fun i j => hcross j i⟩

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
