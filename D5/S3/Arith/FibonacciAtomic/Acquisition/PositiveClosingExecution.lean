/- GID: D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution
   mirror-E: none(waiver:unbounded-symbolic-construction)
   anchors: []
   utility: none
   digest: Positive chronological closing realizes the common-direction scheduler. -/

import D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution

open TerminalGcdAcquisitionCost (replace graft step runWord quantity terminalGcd residueSource costBound)
open SourceCoordinates.PositiveProbeCompiler (direction compile graftBound)
open SourceCoordinates.CommonDirectionScheduler
open ContinuousAcquisitionTransport (Controller Instruction Event Run paidReads)

/-- The public two-by-two residue matrix, including the singleton ring. -/
def matrix (H : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod H) := !![0, 1; 1, 1]

private def matrixUnit (H : ℕ) : (Matrix (Fin 2) (Fin 2) (ZMod H))ˣ where
  val := matrix H
  inv := !![-1, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem small_period (H : ℕ) (hH : 0 < H) :
    ∃ k, 1 ≤ k ∧ k ≤ H ^ 4 ∧ matrix H ^ k = 1 := by
  letI : NeZero H := ⟨hH.ne'⟩
  classical
  refine ⟨orderOf (matrixUnit H), orderOf_pos _, ?_, ?_⟩
  · have hc := Fintype.card_le_of_injective
      (Units.val : (Matrix (Fin 2) (Fin 2) (ZMod H))ˣ → Matrix (Fin 2) (Fin 2) (ZMod H))
      Units.val_injective
    have ho := orderOf_le_card_univ (x := matrixUnit H)
    have hm : Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod H)) = H ^ 4 := by
      change Fintype.card (Fin 2 → Fin 2 → ZMod H) = H ^ 4
      rw [Fintype.card_fun, Fintype.card_fun]
      simp [ZMod.card, ← pow_mul]
    exact ho.trans (hm ▸ hc)
  · exact congrArg Units.val (pow_orderOf_eq_one (matrixUnit H))

/-- Effective least positive matrix period; zero is a public unused convention. -/
def period (H : ℕ) : ℕ :=
  if h : 0 < H then Nat.find (show ∃ k, 1 ≤ k ∧ matrix H ^ k = 1 from by
    obtain ⟨k, hk, _, hm⟩ := small_period H h
    exact ⟨k, hk, hm⟩) else 1

private theorem period_spec (H : ℕ) (hH : 0 < H) :
    1 ≤ period H ∧ period H ≤ H ^ 4 ∧ matrix H ^ period H = 1 ∧
    ∀ k, 1 ≤ k → matrix H ^ k = 1 → period H ≤ k := by
  have hs : ∃ k, 1 ≤ k ∧ matrix H ^ k = 1 := by
    obtain ⟨k, hk, _, hm⟩ := small_period H hH
    exact ⟨k, hk, hm⟩
  have hp : period H = Nat.find hs := by simp only [period, dif_pos hH]
  rw [hp]
  obtain ⟨k, hk, hb, hm⟩ := small_period H hH
  exact ⟨(Nat.find_spec hs).1, (Nat.find_min' hs ⟨hk, hm⟩).trans hb,
    (Nat.find_spec hs).2, fun j hj hm => Nat.find_min' hs ⟨hj, hm⟩⟩

/-- Replace each reversed letter by its actual positive repetition. -/
def closeLetter (H : ℕ) (b : Bool) : List Bool :=
  if b then List.replicate (period H - 1) true else List.replicate (H - 1) false

def closing (H : ℕ) (w : List Bool) : List Bool := w.reverse.flatMap (closeLetter H)

def cycleWord (H : ℕ) (w : List Bool) : List Bool := w ++ closing H w

private theorem run_fold (w : List Bool) (v : ℕ × ℕ) :
    runWord w v = w.foldl (fun x b => step b x) v := by
  induction w generalizing v with
  | nil => rfl
  | cons b w ih => exact ih (step b v)

theorem residue_run (H : ℕ) (w : List Bool) (v : ℕ × ℕ) :
    residueSource H (runWord w v) =
      GraftAffineClosure.run (1, 0) (w.map Bool.not) (residueSource H v) := by
  rw [run_fold, GraftAffineClosure.run, List.foldl_map]
  exact (List.foldl_hom (residueSource H)
    (g₁ := fun u b => step b u)
    (g₂ := fun u b => if b.not then u + (1, 0) else GraftAffineClosure.step u)
    (by intro u b; cases b <;> ext <;> simp [step, replace, graft, residueSource,
      GraftAffineClosure.step])).symm

private theorem residue_congr (H : ℕ) (w : List Bool) (u v : ℕ × ℕ)
    (h : residueSource H u = residueSource H v) :
    residueSource H (runWord w u) = residueSource H (runWord w v) := by
  rw [residue_run, residue_run, h]

private theorem cast_replacements (H k : ℕ) (v : ℕ × ℕ) :
    residueSource H (replace^[k] v) = GraftAffineClosure.step^[k] (residueSource H v) := by
  have h : Function.Semiconj (residueSource H) replace GraftAffineClosure.step := by
    intro x; ext <;> simp [residueSource, replace, GraftAffineClosure.step]
  exact h.iterate_right k v

private theorem same_reply (H : ℕ) (w : List Bool) (u v : ℕ × ℕ)
    (h : residueSource H u = residueSource H v) : terminalGcd H w u = terminalGcd H w v := by
  have hr := residue_congr H w u v h
  have hq := congrArg (fun x : ZMod H × ZMod H => 2 * x.1 + 3 * x.2) hr
  have hm : Nat.ModEq H (quantity (runWord w u)) (quantity (runWord w v)) :=
    (ZMod.natCast_eq_natCast_iff _ _ H).mp (by simpa [quantity, residueSource] using hq)
  exact hm.gcd_eq

private theorem matrix_action (H k : ℕ) (v : ZMod H × ZMod H) :
    (matrix H ^ k).mulVec ![v.1, v.2] =
      ![(GraftAffineClosure.step^[k] v).1, (GraftAffineClosure.step^[k] v).2] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    ext i; fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Function.iterate_succ_apply', GraftAffineClosure.step]

private theorem closing_letter (H : ℕ) (hH : 0 < H) (b : Bool) (v : ℕ × ℕ) :
    residueSource H (runWord (b :: closeLetter H b) v) = residueSource H v := by
  cases b
  · have hg (j : ℕ) (v : ℕ × ℕ) :
        runWord (List.replicate j false) v = (v.1 + j, v.2) := by
      induction j generalizing v with
      | zero => simp [runWord]
      | succ j ih => simp [List.replicate_succ, runWord, step, graft, ih] <;> omega
    simp only [closeLetter, Bool.false_eq_true, ↓reduceIte, runWord, step]
    rw [hg]
    have heq : v.1 + 1 + (H - 1) = v.1 + H := by omega
    change (((v.1 + 1 + (H - 1) : ℕ) : ZMod H), (v.2 : ZMod H)) = _
    rw [heq]
    ext <;> simp [residueSource]
  · have he := (period_spec H hH).2.2.1
    have hv := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod H) =>
      m.mulVec ![(residueSource H v).1, (residueSource H v).2]) he
    rw [matrix_action] at hv
    have hp : GraftAffineClosure.step^[period H] (residueSource H v) = residueSource H v := by
      apply Prod.ext
      · simpa using congrFun hv 0
      · simpa using congrFun hv 1
    have hn : true :: closeLetter H true = List.replicate (period H) true := by
      simp only [closeLetter, ↓reduceIte]
      rw [← List.replicate_succ]
      congr 1
      have := (period_spec H hH).1
      omega
    rw [hn, SourceCoordinates.PositiveProbeCompiler.run_replacements]
    change residueSource H (replace^[period H] v) = residueSource H v
    rw [cast_replacements]
    exact hp

private theorem closing_restores (H : ℕ) (hH : 0 < H) (w : List Bool) (v : ℕ × ℕ) :
    residueSource H (runWord (cycleWord H w) v) = residueSource H v := by
  induction w generalizing v with
  | nil => rfl
  | cons b w ih =>
    have hc : closing H (b :: w) = closing H w ++ closeLetter H b := by
      simp [closing, List.flatMap_append]
    change residueSource H (runWord ((b :: w) ++ closing H (b :: w)) v) = _
    rw [hc]
    have he : runWord ((b :: w) ++ (closing H w ++ closeLetter H b)) v =
        runWord (closeLetter H b) (runWord (cycleWord H w) (step b v)) := by
      simp only [List.cons_append, runWord, SourceCoordinates.PositiveProbeCompiler.run_append, cycleWord]
    rw [he]
    calc
      _ = residueSource H (runWord (closeLetter H b) (step b v)) :=
        residue_congr H (closeLetter H b) _ _ (ih (step b v))
      _ = residueSource H v := closing_letter H hH b v


private theorem cycle_counts (H : ℕ) (hH : 0 < H) (w : List Bool) :
    (cycleWord H w).count true = period H * w.count true ∧
    (cycleWord H w).count false = H * w.count false := by
  have hc (b : Bool) : (closing H w).count b =
      (if b then period H - 1 else H - 1) * w.count b := by
    induction w with
    | nil => simp [closing]
    | cons a w ih =>
      have hs : closing H (a :: w) = closing H w ++ closeLetter H a := by
        simp [closing, List.flatMap_append]
      rw [hs, List.count_append, ih]
      cases a <;> cases b <;> simp [closeLetter, List.count_replicate, Nat.mul_add]
  have hp := (period_spec H hH).1
  constructor
  · simp only [cycleWord, List.count_append, hc, ↓reduceIte]
    calc
      _ = ((period H - 1) + 1) * w.count true := by ring
      _ = _ := by rw [Nat.sub_add_cancel hp]
  · simp only [cycleWord, List.count_append, hc, Bool.false_eq_true, ↓reduceIte]
    calc
      _ = ((H - 1) + 1) * w.count false := by ring
      _ = _ := by rw [Nat.sub_add_cancel (show 1 ≤ H by omega)]

/-- Public program configurations. Source coordinates are absent from every constructor. -/
inductive Phase (H : ℕ) where
  | stage : Bool → ℕ → Joint H → ZMod H → Phase H
  | forward : List Bool → List Bool → Bool → ℕ → Joint H → ZMod H → Phase H
  | reading : List Bool → Bool → ℕ → Joint H → ZMod H → Phase H
  | close : List Bool → Bool → ℕ → Joint H → ZMod H → Phase H

def stageDirection (H : ℕ) (s : Bool) : ℕ := if s then direction H + 1 else direction H

/-- Fixed source-blind instructions. Each action constructor is completed with its
fixed acknowledgement under the imported operational semantics. -/
def code (H : ℕ) : Phase H → Instruction (Phase H) (ZMod H × ZMod H)
  | .stage s 0 a y => if s then .halt (decode H (y, recover H a)) else
      .compute (.stage true (costBound H) (fun _ => initialAxis) (recover H a))
  | .stage s (j + 1) a y =>
      let w := compile H (stageDirection H s) (shift H a)
      .compute (.forward w w s j a y)
  | .forward [] w s j a y => .compute (.reading w s j a y)
  | .forward (b :: todo) w s j a y => .action b (.forward todo w s j a y)
  | .reading w s j a y => .read (fun g => .close (closing H w) s j (advanceAll H a g) y)
  | .close [] s j a y => .compute (.stage s j a y)
  | .close (b :: todo) s j a y => .action b (.close todo s j a y)

/-- The H=1 branch issues neither a read nor a closing call. -/
def controller (H : ℕ) : Controller (Phase H) (ZMod H × ZMod H) where
  code := code H
  initial := if H = 1 then .stage true 0 (fun _ => initialAxis) 0 else
    .stage false (costBound H) (fun _ => initialAxis) 0
  fallback := (0, 0)

/-- One complete test has one full reply strictly between its two action words. -/
def testEvents (H : ℕ) (w : List Bool) (g : ℕ) : List Event :=
  [.compute] ++ w.map Event.action ++ [.compute, .reply g] ++
    (closing H w).map Event.action ++ [.compute]

def events (H k : ℕ) (tape : List (ℕ × ℕ)) : List Event :=
  tape.flatMap (fun t => testEvents H (compile H k t.1) t.2)

def actions (H k : ℕ) (tape : List (ℕ × ℕ)) : List Bool :=
  tape.flatMap (fun t => cycleWord H (compile H k t.1))

private theorem forward_run (H : ℕ) (todo w : List Bool) (s : Bool) (j : ℕ)
    (a : Joint H) (y : ZMod H) (v : ℕ × ℕ) (es : List Event)
    (t : Phase H) (out : ℕ × ℕ) (l : ZMod H × ZMod H)
    (hr : Run (controller H) H (.reading w s j a y) (runWord todo v) es t out l) :
    Run (controller H) H (.forward todo w s j a y) v
      (todo.map Event.action ++ .compute :: es) t out l := by
  induction todo generalizing v with
  | nil => exact .compute rfl hr
  | cons b todo ih => exact .action rfl (ih (step b v) hr)

private theorem close_run (H : ℕ) (todo : List Bool) (s : Bool) (j : ℕ)
    (a : Joint H) (y : ZMod H) (v : ℕ × ℕ) (es : List Event)
    (t : Phase H) (out : ℕ × ℕ) (l : ZMod H × ZMod H)
    (hr : Run (controller H) H (.stage s j a y) (runWord todo v) es t out l) :
    Run (controller H) H (.close todo s j a y) v
      (todo.map Event.action ++ .compute :: es) t out l := by
  induction todo generalizing v with
  | nil => exact .compute rfl hr
  | cons b todo ih => exact .action rfl (ih (step b v) hr)

private theorem actions_restore (H k : ℕ) (hH : 0 < H) (tape : List (ℕ × ℕ))
    (v : ℕ × ℕ) : residueSource H (runWord (actions H k tape) v) = residueSource H v := by
  induction tape generalizing v with
  | nil => rfl
  | cons t tape ih =>
    change residueSource H
      (runWord (cycleWord H (compile H k t.1) ++ actions H k tape) v) = _
    rw [SourceCoordinates.PositiveProbeCompiler.run_append]
    rw [ih, closing_restores H hH]

private theorem rounds_run (H : ℕ) (hH : 0 < H) (entry : ℕ × ℕ) (s : Bool)
    (j : ℕ) (a : Joint H) (y : ZMod H) :
    let r := rounds H (compiledReply H entry (stageDirection H s)) j a
    ∀ current, residueSource H current = residueSource H entry →
    ∀ es t out l,
      Run (controller H) H (.stage s 0 r.1 y)
        (runWord (actions H (stageDirection H s) r.2) current) es t out l →
      Run (controller H) H (.stage s j a y) current
        (events H (stageDirection H s) r.2 ++ es) t out l := by
  dsimp only
  induction j generalizing a with
  | zero => intro current hc es t out l hr; exact hr
  | succ j ih =>
    intro current hc es t out l hr
    let k := stageDirection H s
    let c := shift H a
    let w := compile H k c
    let g := compiledReply H entry k c
    let next := advanceAll H a g
    have hg : Nat.gcd (quantity (runWord w current)) H = g :=
      same_reply H w current entry hc
    have hn : residueSource H (runWord (cycleWord H w) current) = residueSource H entry :=
      (closing_restores H hH w current).trans hc
    have ht := ih next (runWord (cycleWord H w) current) hn es t out l
      (by simpa only [rounds, actions, List.flatMap_cons, SourceCoordinates.PositiveProbeCompiler.run_append] using hr)
    have hclose := close_run H (closing H w) s j next y (runWord w current)
      _ t out l (by simpa only [cycleWord, SourceCoordinates.PositiveProbeCompiler.run_append] using ht)
    have hread : Run (controller H) H (.reading w s j a y) (runWord w current)
        (.reply g :: ((closing H w).map Event.action ++ .compute ::
          (events H k (rounds H (compiledReply H entry k) j next).2 ++ es))) t out l := by
      rw [← hg]
      exact .read rfl (by simpa only [hg] using hclose)
    have hf := forward_run H w w s j a y current _ t out l hread
    have hs := Run.compute (P := controller H) (H := H) (s := Phase.stage s (j + 1) a y) rfl hf
    simpa only [rounds, events, List.flatMap_cons, testEvents, k, c, w, g, next,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hs

private theorem paid_append (x y : List Event) : paidReads (x ++ y) = paidReads x + paidReads y := by
  induction x with
  | nil => simp [paidReads]
  | cons e x ih => cases e <;> simp [paidReads, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem read_count (H k : ℕ) (tape : List (ℕ × ℕ)) :
    paidReads (events H k tape) = tape.length := by
  have action (w : List Bool) : paidReads (w.map Event.action) = 0 := by
    induction w with
    | nil => rfl
    | cons b w ih => exact ih
  induction tape with
  | nil => rfl
  | cons t tape ih =>
    change paidReads (testEvents H (compile H k t.1) t.2 ++ events H k tape) = _
    simp [paid_append, testEvents, action, paidReads, ih]


/-- Number of replacements strictly after each actual graft, in graft order. -/
def graftSuffixes : List Bool → List ℕ
  | [] => []
  | true :: w => graftSuffixes w
  | false :: w => w.count true :: graftSuffixes w

private theorem replace_add (x y : ℕ × ℕ) : replace (x + y) = replace x + replace y := by
  ext <;> simp [replace] <;> omega

private theorem iterate_add (k : ℕ) (x y : ℕ × ℕ) :
    replace^[k] (x + y) = replace^[k] x + replace^[k] y := by
  exact Function.Semiconj₂.iterate replace_add k x y

private theorem affine_suffix (w : List Bool) (v : ℕ × ℕ) :
    runWord w v = replace^[w.count true] v +
      ((graftSuffixes w).map (fun r => replace^[r] (1, 0))).sum := by
  induction w generalizing v with
  | nil => simp [runWord, graftSuffixes]
  | cons b w ih =>
    cases b
    · rw [runWord, ih]
      have hg : step false v = v + (1, 0) := by ext <;> simp [step, graft]
      rw [hg, iterate_add]
      simp [graftSuffixes, List.count_cons, add_assoc]
    · simpa [runWord, graftSuffixes, List.count_cons, step, Function.iterate_succ_apply,
        Nat.add_comm] using ih (replace v)

private theorem step_growth (b : Bool) (v : ℕ × ℕ) :
    quantity v ≤ quantity (step b v) ∧
    (if b then quantity (step b v) ≤ 2 * quantity v
      else quantity (step b v) = quantity v + 2) := by
  cases b <;> simp [step, replace, graft, quantity] <;> omega

private theorem word_growth (w : List Bool) (v : ℕ × ℕ) :
    quantity v ≤ quantity (runWord w v) ∧
    quantity (runWord w v) ≤ 2 ^ w.count true * (quantity v + 2 * w.count false) := by
  induction w generalizing v with
  | nil => simp [runWord]
  | cons b w ih =>
    have ht := ih (step b v)
    have hs := step_growth b v
    refine ⟨hs.1.trans ht.1, ?_⟩
    cases b
    · have hg : quantity (step false v) = quantity v + 2 := hs.2
      simpa [runWord, List.count_cons, hg, Nat.mul_add, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.2
    · simp [runWord, List.count_cons, pow_succ]
      simp only [↓reduceIte] at hs
      nlinarith [Nat.mul_le_mul_left (2 ^ w.count true) hs.2,
        Nat.zero_le (2 ^ w.count true * w.count false)]

private theorem prefix_growth (w pre post : List Bool) (v : ℕ × ℕ) (hw : w = pre ++ post) :
    quantity (runWord pre v) ≤ quantity (runWord w v) := by
  rw [hw, SourceCoordinates.PositiveProbeCompiler.run_append]
  exact (word_growth post (runWord pre v)).1

/-- Semantic run data; the controller itself has no entry argument. -/
def stageData (H : ℕ) (v : ℕ × ℕ) (s : Bool) : Joint H × List (ℕ × ℕ) :=
  rounds H (compiledReply H v (stageDirection H s)) (costBound H) (fun _ => initialAxis)

def executionWord (H : ℕ) (v : ℕ × ℕ) : List Bool :=
  if H = 1 then [] else
    actions H (direction H) (stageData H v false).2 ++
    actions H (direction H + 1) (stageData H v true).2

def executionEvents (H : ℕ) (v : ℕ × ℕ) : List Event :=
  if H = 1 then [] else
    events H (direction H) (stageData H v false).2 ++ .compute ::
    events H (direction H + 1) (stageData H v true).2

def tests (H : ℕ) (v : ℕ × ℕ) (s : Bool) : ℕ :=
  if H = 1 then 0 else (stageData H v s).2.length

/-- The sum is over the selected forward words, once per actual paid test. -/
def graftSum (H : ℕ) (v : ℕ × ℕ) : ℕ :=
  (((schedule H (compiledReply H v)).2).map (fun t => (compile H t.1 t.2.1).count false)).sum

private theorem rounds_length (H : ℕ) (answer : ℕ → ℕ) (j : ℕ) (a : Joint H) :
    (rounds H answer j a).2.length = j := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih => simpa only [rounds, List.length_cons] using congrArg Nat.succ (ih _)

private theorem actions_counts (H k : ℕ) (hH : 0 < H) (tape : List (ℕ × ℕ)) :
    (actions H k tape).count true = period H *
      (tape.map (fun t => (compile H k t.1).count true)).sum ∧
    (actions H k tape).count false = H *
      (tape.map (fun t => (compile H k t.1).count false)).sum := by
  induction tape with
  | nil => simp [actions]
  | cons t tape ih =>
    change (cycleWord H (compile H k t.1) ++ actions H k tape).count true = _ ∧
      (cycleWord H (compile H k t.1) ++ actions H k tape).count false = _
    constructor <;> simp only [List.count_append, List.map_cons, List.sum_cons,
      (cycle_counts H hH (compile H k t.1)).1, (cycle_counts H hH (compile H k t.1)).2,
      ih.1, ih.2, Nat.mul_add]

private theorem actual_run (H : ℕ) (hH : 1 ≤ H) (v : ℕ × ℕ) :
    ∃ t, Run (controller H) H (controller H).initial v (executionEvents H v) t
      (runWord (executionWord H v) v) (residueSource H v) := by
  by_cases h1 : H = 1
  · subst H
    have hl : decode 1 (0, recover 1 (fun _ => initialAxis)) = residueSource 1 v :=
      Subsingleton.elim _ _
    refine ⟨.stage true 0 (fun _ => initialAxis) 0, ?_⟩
    simp only [executionEvents, executionWord, if_pos rfl, runWord, controller]
    exact .halt (by simpa only [code, ↓reduceIte] using congrArg Instruction.halt hl)
  have hpos : 0 < H := by omega
  let r := stageData H v false
  let t := stageData H v true
  let w := actions H (direction H) r.2
  let z := actions H (direction H + 1) t.2
  let y := recover H r.1
  have out : decode H (y, recover H t.1) = residueSource H v := by
    simpa only [schedule, stage, if_neg h1, r, t, stageData, stageDirection, Bool.false_eq_true,
      ↓reduceIte, y] using (effective_scheduler H hH v).1
  have halt : Run (controller H) H (.stage true 0 t.1 y)
      (runWord z (runWord w v)) [] (.stage true 0 t.1 y)
      (runWord z (runWord w v)) (residueSource H v) :=
    .halt (by simpa only [controller, code, ↓reduceIte] using congrArg Instruction.halt out)
  have second := rounds_run H hpos v true (costBound H) (fun _ => initialAxis) y
    (runWord w v) (actions_restore H (direction H) hpos r.2 v) [] _ _ _ halt
  have bridge : Run (controller H) H (.stage false 0 r.1 0) (runWord w v)
      (.compute :: events H (direction H + 1) t.2) (.stage true 0 t.1 y)
      (runWord z (runWord w v)) (residueSource H v) := by
    exact .compute rfl (by simpa only [stageDirection, ↓reduceIte, stageData, t, y,
      List.append_nil] using second)
  have first := rounds_run H hpos v false (costBound H) (fun _ => initialAxis) 0
    v rfl _ _ _ _ bridge
  refine ⟨.stage true 0 t.1 y, ?_⟩
  simpa only [controller, if_neg h1, executionEvents, executionWord, SourceCoordinates.PositiveProbeCompiler.run_append,
    stageDirection, Bool.false_eq_true, ↓reduceIte, stageData, r, t, w, z, y] using first

private theorem execution_counts (H : ℕ) (hH : 1 ≤ H) (v : ℕ × ℕ) :
    paidReads (executionEvents H v) = tests H v false + tests H v true ∧
    tests H v false = (if H = 1 then 0 else costBound H) ∧
    tests H v true = (if H = 1 then 0 else costBound H) ∧
    (executionWord H v).count true = period H *
      (direction H * tests H v false + (direction H + 1) * tests H v true) ∧
    (executionWord H v).count false = H * graftSum H v ∧
    (executionWord H v).count false ≤ 2 * H * graftBound H * costBound H := by
  by_cases h1 : H = 1
  · subst H
    simp [executionWord, executionEvents, tests, graftSum, schedule, stage, paidReads]
  have hh : 1 < H := by omega
  have compiler := SourceCoordinates.PositiveProbeCompiler.effective_short_compiler H hh
  have sumR (k : ℕ) (hk : k = direction H ∨ k = direction H + 1) (ts : List (ℕ × ℕ)) :
      (ts.map (fun t => (compile H k t.1).count true)).sum = k * ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, (compiler.2.2.2 k t.1 hk).2.2.2.1, ih,
        List.length_cons]
      ring
  have count0 := actions_counts H (direction H) (by omega) (stageData H v false).2
  have count1 := actions_counts H (direction H + 1) (by omega) (stageData H v true).2
  have hs : (executionWord H v).count false = H * graftSum H v := by
    rw [executionWord, if_neg h1, List.count_append, count0.2, count1.2]
    simp [graftSum, schedule, stage, h1, stageData, stageDirection,
      Function.comp_def, Nat.mul_add]
  refine ⟨?_, ?_, ?_, ?_, hs, ?_⟩
  · simp [executionEvents, h1, paid_append, paidReads, read_count, tests]
  · simp [tests, h1, stageData, rounds_length]
  · simp [tests, h1, stageData, rounds_length]
  · simp only [executionWord, if_neg h1, List.count_append, count0.1, count1.1,
      sumR _ (Or.inl rfl), sumR _ (Or.inr rfl), tests, if_neg h1, Nat.mul_add]
  · have bound : graftSum H v ≤ graftBound H * (schedule H (compiledReply H v)).2.length := by
      have hb := List.sum_le_length_nsmul
        ((schedule H (compiledReply H v)).2.map (fun t => (compile H t.1 t.2.1).count false))
        (graftBound H) (by
          intro x hx
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
          exact ((effective_scheduler H hH v).2.2.2 t ht).2.2.2.1)
      simpa [graftSum, List.length_map, nsmul_eq_mul, Nat.mul_comm] using hb
    have len := (effective_scheduler H hH v).2.2.1
    rw [if_neg h1] at len
    rw [hs]
    calc
      H * graftSum H v ≤ H * (graftBound H * (2 * costBound H)) :=
        Nat.mul_le_mul_left H (by simpa only [len] using bound)
      _ = _ := by ring

private def letters : List Event → List Bool
  | [] => []
  | .action b :: es => b :: letters es
  | _ :: es => letters es

private theorem letters_append (es fs : List Event) : letters (es ++ fs) = letters es ++ letters fs := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [letters, ih]

private theorem letters_actions (w : List Bool) : letters (w.map Event.action) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [letters] using congrArg (List.cons b) ih

private theorem letters_events (H k : ℕ) (ts : List (ℕ × ℕ)) :
    letters (events H k ts) = actions H k ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change letters (testEvents H (compile H k t.1) t.2 ++ events H k ts) =
      cycleWord H (compile H k t.1) ++ actions H k ts
    rw [letters_append, ih]
    simp [testEvents, letters_append, letters_actions, letters, cycleWord]

private theorem final_word (H : ℕ) (v : ℕ × ℕ) :
    ContinuousAcquisitionTransport.finalWord [] (executionEvents H v) = executionWord H v := by
  have hf (es : List Event) (A : List Bool) :
      ContinuousAcquisitionTransport.finalWord A es = A ++ letters es := by
    induction es generalizing A with
    | nil => simp [ContinuousAcquisitionTransport.finalWord, letters]
    | cons e es ih => cases e <;> simp [ContinuousAcquisitionTransport.finalWord,
        letters, ih, List.append_assoc]
  rw [hf]
  by_cases h1 : H = 1
  · simp [executionWord, executionEvents, h1, letters]
  · simp [executionWord, executionEvents, h1, letters_append, letters, letters_events]

private theorem suffix_length (w : List Bool) : (graftSuffixes w).length = w.count false := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [graftSuffixes, ih, List.count_cons, Nat.add_comm]

/-- The actual operational execution earns the required cut and all one-run
letter counts. The endpoint and prefix inequalities concern that very word. -/
theorem positive_execution (H : ℕ) (hH : 1 ≤ H) (v : ℕ × ℕ) :
    let w := executionWord H v
    let es := executionEvents H v
    (∃ t, Run (controller H) H (controller H).initial v es t (runWord w v) (residueSource H v)) ∧
    ContinuousAcquisitionTransport.finalWord [] es = w ∧
    residueSource H (runWord w v) = residueSource H v ∧
    1 ≤ period H ∧ period H ≤ H ^ 4 ∧ matrix H ^ period H = 1 ∧
    (∀ k, 1 ≤ k → matrix H ^ k = 1 → period H ≤ k) ∧
    paidReads es = tests H v false + tests H v true ∧
    paidReads es = (if H = 1 then 0 else 2 * costBound H) ∧
    (w.count true = period H * (direction H * tests H v false +
      (direction H + 1) * tests H v true)) ∧
    w.count false = H * graftSum H v ∧
    w.count true ≤ period H * (2 * direction H + 1) * costBound H ∧
    w.count false ≤ 2 * H * graftBound H * costBound H ∧
    (graftSuffixes w).length = w.count false ∧
    runWord w v = replace^[w.count true] v +
      ((graftSuffixes w).map (fun r => replace^[r] (1, 0))).sum ∧
    (∀ pre post, w = pre ++ post → quantity (runWord pre v) ≤ quantity (runWord w v)) ∧
    quantity (runWord w v) ≤ 2 ^ w.count true * (quantity v + 2 * w.count false) ∧
    (H = 1 → w = [] ∧ es = []) := by
  dsimp only
  have hp := period_spec H (by omega)
  have hc := execution_counts H hH v
  have hr : residueSource H (runWord (executionWord H v) v) = residueSource H v := by
    by_cases h1 : H = 1
    · simp [executionWord, h1, runWord]
    · simp only [executionWord, if_neg h1, SourceCoordinates.PositiveProbeCompiler.run_append]
      rw [actions_restore H _ (by omega), actions_restore H _ (by omega)]
  have reads : paidReads (executionEvents H v) = (if H = 1 then 0 else 2 * costBound H) := by
    rw [hc.1, hc.2.1, hc.2.2.1]
    split_ifs <;> omega
  have nr : (executionWord H v).count true ≤ period H * (2 * direction H + 1) * costBound H := by
    rw [hc.2.2.2.1, hc.2.1, hc.2.2.1]
    split_ifs
    · simp
    · exact le_of_eq (by ring)
  exact ⟨actual_run H hH v, final_word H v, hr, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
    hc.1, reads, hc.2.2.2.1, hc.2.2.2.2.1, nr, hc.2.2.2.2.2,
    suffix_length _, affine_suffix _ v, fun pre post hw => prefix_growth _ pre post v hw,
    (word_growth _ v).2, fun h1 => by simp [executionWord, executionEvents, h1]⟩

#print axioms period
#print axioms controller
#print axioms positive_execution

end D5.S3.Arith.FibonacciAtomic.Acquisition.PositiveClosingExecution
