/- GID: D5/S3/Combinatorics/Golomb/Replay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Golomb/Replay
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: [mathlib/module/Mathlib.Basic.Real.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikMinimizers.result; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: Separated real distances justify the orientation and every row of a checked bound tree. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Golomb.Replay

open scoped BigOperators

/-- The one-based rank of each entry bounds it from below after sorting. -/
private theorem rank_le_sorted {n : ℕ} (d : Fin n → ℝ)
    (hmin : ∀ i, 1 ≤ d i)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |d i - d j|) (i : Fin n) :
    (i.val : ℝ) + 1 ≤ d (Tuple.sort d i) := by
  let p := Tuple.sort d
  have hm : Monotone (d ∘ p) := Tuple.monotone_sort d
  have rank (k : ℕ) (hk : k < n) : (k : ℝ) + 1 ≤ d (p ⟨k, hk⟩) := by
    induction k with
    | zero => simpa using hmin (p ⟨0, hk⟩)
    | succ k ih =>
        have hk' : k < n := Nat.lt_of_succ_lt hk
        let a : Fin n := ⟨k, hk'⟩
        let b : Fin n := ⟨k + 1, hk⟩
        have hab : a < b := Nat.lt_succ_self k
        have hord : d (p a) ≤ d (p b) := hm hab.le
        have hgap : 1 ≤ d (p b) - d (p a) := by
          simpa only [abs_of_nonneg (sub_nonneg.mpr hord)] using
            hsep (p b) (p a) (fun h => hab.ne (p.injective h).symm)
        have hprev : (k : ℝ) + 1 ≤ d (p a) := ih hk'
        change ((k + 1 : ℕ) : ℝ) + 1 ≤ d (p b)
        push_cast
        linarith
  exact rank i.val i.isLt

private theorem sum_ranks (n : ℕ) :
    (∑ i : Fin n, ((i.val : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (k : ℝ) + 1)]
  have h := Finset.sum_range_id_mul_two (n + 1)
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.add_sub_cancel] at h
  have h' := congrArg (fun k : ℕ => (k : ℝ)) h
  push_cast at h'
  push_cast
  linarith

/-- A separated tuple has at least triangular total, with equality precisely
when its sorted entries are the one-based ranks. -/
private theorem packing_bound_and_saturation {n : ℕ} (d : Fin n → ℝ)
    (hmin : ∀ i, 1 ≤ d i)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |d i - d j|) :
    (n : ℝ) * ((n : ℝ) + 1) / 2 ≤ ∑ i, d i ∧
    ((∑ i, d i) = (n : ℝ) * ((n : ℝ) + 1) / 2 ↔
      ∀ i, d (Tuple.sort d i) = (i.val : ℝ) + 1) := by
  rw [← sum_ranks n, ← Equiv.sum_comp (Tuple.sort d) d]
  have hle (i : Fin n) (_ : i ∈ Finset.univ) :
      (i.val : ℝ) + 1 ≤ d (Tuple.sort d i) := rank_le_sorted d hmin hsep i
  constructor
  · exact Finset.sum_le_sum hle
  · rw [eq_comm, Finset.sum_eq_sum_iff_of_le hle]
    exact ⟨fun h i => (h i (Finset.mem_univ i)).symm, fun h i _ => (h i).symm⟩

/-- In the original slot order, a saturated tuple is a permutation of the ranks. -/
theorem packing_slots_of_saturation {n : ℕ} (d : Fin n → ℝ)
    (hmin : ∀ i, 1 ≤ d i)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |d i - d j|)
    (hsum : (∑ i, d i) = (n : ℝ) * ((n : ℝ) + 1) / 2) :
    ∃ p : Equiv.Perm (Fin n), ∀ i, d i = ((p i).val : ℝ) + 1 := by
  have hr := (packing_bound_and_saturation d hmin hsep).2.mp hsum
  refine ⟨(Tuple.sort d).symm, fun i => ?_⟩
  simpa only [Equiv.apply_symm_apply] using hr ((Tuple.sort d).symm i)



structure Row (n : ℕ) where
  normal : Fin n → ℤ
  rhs : ℤ

def eval {n : ℕ} (a : Fin n → ℤ) (g : Fin n → ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * g i

def Row.Holds {n : ℕ} (g : Fin n → ℝ) (r : Row n) : Prop :=
  (r.rhs : ℝ) ≤ eval r.normal g

def Row.zero (n : ℕ) : Row n := ⟨fun _ => 0, 0⟩

def Row.addScaled {n : ℕ} (r : Row n) (w : ℤ) (s : Row n) : Row n :=
  ⟨fun i => w * r.normal i + s.normal i, w * r.rhs + s.rhs⟩

theorem eval_add {n : ℕ} (a b : Fin n → ℤ) (g : Fin n → ℝ) :
    eval (fun i => a i + b i) g = eval a g + eval b g := by
  simp only [eval, Int.cast_add, add_mul, Finset.sum_add_distrib]

theorem eval_sub {n : ℕ} (a b : Fin n → ℤ) (g : Fin n → ℝ) :
    eval (fun i => a i - b i) g = eval a g - eval b g := by
  simp only [eval, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem eval_scale {n : ℕ} (w : ℤ) (a : Fin n → ℤ) (g : Fin n → ℝ) :
    eval (fun i => w * a i) g = (w : ℝ) * eval a g := by
  simp only [eval, Int.cast_mul, mul_assoc, Finset.mul_sum]

private theorem Row.addScaled_holds {n : ℕ} {r s : Row n} {w : ℤ} {g : Fin n → ℝ}
    (hw : 0 ≤ w) (hr : r.Holds g) (hs : s.Holds g) : (r.addScaled w s).Holds g := by
  change ((w * r.rhs + s.rhs : ℤ) : ℝ) ≤ eval (fun i => w * r.normal i + s.normal i) g
  rw [Int.cast_add, Int.cast_mul, eval_add, eval_scale]
  exact add_le_add (mul_le_mul_of_nonneg_left hr (by exact_mod_cast hw)) hs

inductive Ref where
  | static (index : ℕ)
  | branch (depth : ℕ)

def lookup {n : ℕ} (rows : Array (Row n)) (path : List (Row n)) : Ref → Option (Row n)
  | .static i => rows[i]?
  | .branch i => path[i]?

def Valid {α : Type*} {n : ℕ} (rows : α → Option (Row n)) (g : Fin n → ℝ) : Prop :=
  ∀ i r, rows i = some r → r.Holds g

def PathHolds {n : ℕ} (path : List (Row n)) (g : Fin n → ℝ) : Prop :=
  ∀ r ∈ path, r.Holds g

theorem lookup_valid {n : ℕ} {rows : Array (Row n)} {path : List (Row n)} {g : Fin n → ℝ}
    (hs : Valid (fun i : ℕ => rows[i]?) g) (hp : PathHolds path g) :
    Valid (lookup rows path) g := by
  intro ref r h
  cases ref with
  | static i => exact hs i r h
  | branch i => exact hp r (List.mem_of_getElem? (show path[i]? = some r from h))

abbrev Weights := List (Ref × ℤ)

/-- Multipliers are integers after multiplying every rational weight by the same
positive denominator. Every reference, including a zero-weight one, must resolve. -/
def aggregate {n : ℕ} (get : Ref → Option (Row n)) : Weights → Option (Row n)
  | [] => some (.zero n)
  | (ref, w) :: rest => do
    if w < 0 then none else
      let r ← get ref
      let s ← aggregate get rest
      pure (r.addScaled w s)

private theorem aggregate_holds {n : ℕ} {get : Ref → Option (Row n)} {g : Fin n → ℝ}
    (hg : Valid get g) {weights : Weights} {total : Row n}
    (h : aggregate get weights = some total) : total.Holds g := by
  induction weights generalizing total with
  | nil =>
    have he : Row.zero n = total := Option.some.inj h
    subst total
    simp [Row.Holds, Row.zero, eval]
  | cons item rest ih =>
    obtain ⟨ref, w⟩ := item
    by_cases hw : w < 0
    · simp [aggregate, hw] at h
    cases hr : get ref with
    | none => simp [aggregate, hw, hr] at h
    | some r =>
      cases hs : aggregate get rest with
      | none => simp [aggregate, hw, hr, hs] at h
      | some s =>
        have he : r.addScaled w s = total := by simpa [aggregate, hw, hr, hs] using h
        subst total
        exact Row.addScaled_holds (le_of_not_gt hw) (hg ref r hr) (ih hs)

def supportTight {n : ℕ} (get : Ref → Option (Row n)) (weights : Weights)
    (g : Fin n → ℝ) : Prop :=
  ∀ ref w, (ref, w) ∈ weights → 0 < w → ∀ r, get ref = some r →
    eval r.normal g = (r.rhs : ℝ)

private theorem aggregate_tight {n : ℕ} {get : Ref → Option (Row n)} {g : Fin n → ℝ}
    (hg : Valid get g) {weights : Weights} {total : Row n}
    (h : aggregate get weights = some total)
    (heq : eval total.normal g = (total.rhs : ℝ)) : supportTight get weights g := by
  induction weights generalizing total with
  | nil => simp [supportTight]
  | cons item rest ih =>
    obtain ⟨ref, w⟩ := item
    by_cases hw : w < 0
    · simp [aggregate, hw] at h
    cases hr : get ref with
    | none => simp [aggregate, hw, hr] at h
    | some r =>
      cases hs : aggregate get rest with
      | none => simp [aggregate, hw, hr, hs] at h
      | some s =>
        have he : r.addScaled w s = total := by simpa [aggregate, hw, hr, hs] using h
        subst total
        change eval (fun i => w * r.normal i + s.normal i) g =
          ((w * r.rhs + s.rhs : ℤ) : ℝ) at heq
        rw [eval_add, eval_scale, Int.cast_add, Int.cast_mul] at heq
        have hrle : (r.rhs : ℝ) ≤ eval r.normal g := hg ref r hr
        have hsle : (s.rhs : ℝ) ≤ eval s.normal g := aggregate_holds hg hs
        have hwle : 0 ≤ (w : ℝ) := by exact_mod_cast le_of_not_gt hw
        have hweighted := mul_le_mul_of_nonneg_left hrle hwle
        have hstight : eval s.normal g = (s.rhs : ℝ) := by linarith
        intro key coefficient hmem hpos row hrow
        rcases List.mem_cons.mp hmem with head | tail
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj head
          have hrow' : row = r := Option.some.inj (hrow.symm.trans hr)
          subst row
          have hweightedEq : (coefficient : ℝ) * eval r.normal g = (coefficient : ℝ) * (r.rhs : ℝ) := by
            linarith
          exact mul_left_cancel₀ (ne_of_gt (by exact_mod_cast hpos)) hweightedEq
        · exact ih hs hstight key coefficient tail hpos row hrow

/-- Path hypotheses are formed from this normal, in the archive's ≥ convention. -/
def branchRow {n : ℕ} (positive : Bool) (a : Fin n → ℤ) : Row n :=
  ⟨fun i => (if positive then 1 else -1) * a i, 1⟩

theorem eval_neg {n : ℕ} (a : Fin n → ℤ) (g : Fin n → ℝ) :
    eval (fun i => -a i) g = -eval a g := by
  simp only [eval, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem branch_cover {n : ℕ} {a : Fin n → ℤ} {g : Fin n → ℝ}
    (h : 1 ≤ |eval a g|) : (branchRow false a).Holds g ∨ (branchRow true a).Holds g := by
  rcases le_abs.mp h with hp | hn
  · right
    simpa [branchRow, Row.Holds] using hp
  · left
    simpa [branchRow, Row.Holds, eval_neg] using hn

theorem pathHolds_append {n : ℕ} {g : Fin n → ℝ} {path : List (Row n)} {r : Row n}
    (hp : PathHolds path g) (hr : r.Holds g) : PathHolds (path ++ [r]) g := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hp s h
  · simpa using (List.mem_singleton.mp h ▸ hr : s.Holds g)

def length {n : ℕ} (g : Fin n → ℝ) : ℝ := ∑ i, g i

inductive Tree where
  | bound (id : ℕ) (scale : ℕ) (weights : Weights)
  | farkas (id : ℕ) (weights : Weights)
  | branch (id relation : ℕ) (negative positive : Tree)

/-- The local check is separate so acceptance can be proved in bounded chunks. -/
def checkBound {n : ℕ} (target : ℤ) (scale : ℕ) (total : Row n) : Bool :=
  decide (0 < scale) && (List.finRange n).all (fun i => total.normal i == (scale : ℤ)) &&
    decide ((scale : ℤ) * target ≤ total.rhs)

def checkFarkas {n : ℕ} (total : Row n) : Bool :=
  (List.finRange n).all (fun i => total.normal i == 0) && decide (0 < total.rhs)

def Tree.check {n : ℕ} (target : ℤ) (rows : Array (Row n))
    (relations : Array (Fin n → ℤ)) (path : List (Row n)) : Tree → Bool
  | .bound _ scale weights =>
    match aggregate (lookup rows path) weights with
    | none => false
    | some total => checkBound target scale total
  | .farkas _ weights =>
    match aggregate (lookup rows path) weights with
    | none => false
    | some total => checkFarkas total
  | .branch _ rel negative positive =>
    match relations[rel]? with
    | none => false
    | some a =>
      negative.check target rows relations (path ++ [branchRow false a]) &&
      positive.check target rows relations (path ++ [branchRow true a])

def RelationsValid {n : ℕ} (relations : Array (Fin n → ℤ)) (g : Fin n → ℝ) : Prop :=
  ∀ (i : ℕ) a, relations[i]? = some a → 1 ≤ |eval a g|

private theorem checked_bound {n : ℕ} {target : ℤ} {scale : ℕ} {total : Row n} {g : Fin n → ℝ}
    (hc : checkBound target scale total = true) (ht : total.Holds g) :
    (target : ℝ) ≤ length g ∧
    (length g = (target : ℝ) →
      total.rhs = (scale : ℤ) * target ∧ eval total.normal g = (total.rhs : ℝ)) := by
  simp only [checkBound, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hc
  obtain ⟨⟨hs, ha⟩, hb⟩ := hc
  have heval : eval total.normal g = (scale : ℝ) * length g := by
    have hnormal : total.normal = fun _ => (scale : ℤ) := by
      funext i
      exact ha i (by simp)
    simp only [hnormal, eval, Int.cast_natCast, length, Finset.mul_sum]
  have hpos : (0 : ℝ) < scale := by exact_mod_cast hs
  have hbelow : (scale : ℝ) * (target : ℝ) ≤ (total.rhs : ℝ) := by exact_mod_cast hb
  have habove : (total.rhs : ℝ) ≤ (scale : ℝ) * length g := heval ▸ ht
  refine ⟨(mul_le_mul_iff_right₀ hpos).mp (hbelow.trans habove), fun hlen => ?_⟩
  rw [hlen] at habove heval
  have hsum := le_antisymm habove hbelow
  constructor
  · exact_mod_cast hsum
  · exact heval.trans hsum.symm

theorem checked_farkas {n : ℕ} {total : Row n} {g : Fin n → ℝ}
    (hc : checkFarkas total = true) (ht : total.Holds g) : False := by
  simp only [checkFarkas, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at hc
  have hn : total.normal = fun _ => 0 := by
    funext i
    exact hc.1 i (by simp)
  have hp : (0 : ℝ) < total.rhs := by exact_mod_cast hc.2
  have hz : (total.rhs : ℝ) ≤ 0 := by simpa [Row.Holds, hn, eval] using ht
  exact (not_lt_of_ge hz) hp

/-- At equality, routing returns a bound leaf of the actual syntax tree, along
with its resolved rows and the tight equations of its positive support. -/
inductive Tree.Routes {n : ℕ} (relations : Array (Fin n → ℤ)) (g : Fin n → ℝ) :
    List (Row n) → Tree → List (Row n) → Tree → Prop where
  | stop (path : List (Row n)) (id scale : ℕ) (weights : Weights) :
    Routes relations g path (.bound id scale weights) path (.bound id scale weights)
  | negative {path leafPath : List (Row n)} {leaf neg pos : Tree} {id rel : ℕ}
      {a : Fin n → ℤ} (ha : relations[rel]? = some a) (h : (branchRow false a).Holds g)
      (tail : Routes relations g (path ++ [branchRow false a]) neg leafPath leaf) :
      Routes relations g path (.branch id rel neg pos) leafPath leaf
  | positive {path leafPath : List (Row n)} {leaf neg pos : Tree} {id rel : ℕ}
      {a : Fin n → ℤ} (ha : relations[rel]? = some a) (h : (branchRow true a).Holds g)
      (tail : Routes relations g (path ++ [branchRow true a]) pos leafPath leaf) :
      Routes relations g path (.branch id rel neg pos) leafPath leaf

def EqualityTerminal {n : ℕ} (target : ℤ) (rows : Array (Row n))
    (relations : Array (Fin n → ℤ)) (path : List (Row n)) (tree : Tree)
    (g : Fin n → ℝ) : Prop :=
  ∃ leafPath id scale weights total,
    tree.Routes relations g path leafPath (.bound id scale weights) ∧
    PathHolds leafPath g ∧
    aggregate (lookup rows leafPath) weights = some total ∧
    checkBound target scale total = true ∧
    total.rhs = (scale : ℤ) * target ∧
    supportTight (lookup rows leafPath) weights g

theorem Tree.check_sound {n : ℕ} {target : ℤ} {rows : Array (Row n)}
    {relations : Array (Fin n → ℤ)} {tree : Tree} {path : List (Row n)} {g : Fin n → ℝ}
    (hc : tree.check target rows relations path = true)
    (hs : Valid (fun i : ℕ => rows[i]?) g) (hr : RelationsValid relations g)
    (hp : PathHolds path g) :
    (target : ℝ) ≤ length g ∧
      (length g = (target : ℝ) → EqualityTerminal target rows relations path tree g) := by
  induction tree generalizing path with
  | bound id scale weights =>
    cases he : aggregate (lookup rows path) weights with
    | none => simp [Tree.check, he] at hc
    | some total =>
      have hb : checkBound target scale total = true := by simpa [Tree.check, he] using hc
      have hv := lookup_valid hs hp
      obtain ⟨hl, ht⟩ := checked_bound hb (aggregate_holds hv he)
      refine ⟨hl, fun hlen => ?_⟩
      obtain ⟨hrhs, htight⟩ := ht hlen
      exact ⟨path, id, scale, weights, total, .stop path id scale weights, hp, he, hb,
        hrhs, aggregate_tight hv he htight⟩
  | farkas id weights =>
    cases he : aggregate (lookup rows path) weights with
    | none => simp [Tree.check, he] at hc
    | some total =>
      have hf : checkFarkas total = true := by simpa [Tree.check, he] using hc
      exact False.elim (checked_farkas hf (aggregate_holds (lookup_valid hs hp) he))
  | branch id rel neg pos ihneg ihpos =>
    cases ha : relations[rel]? with
    | none => simp [Tree.check, ha] at hc
    | some a =>
      simp only [Tree.check, ha, Bool.and_eq_true] at hc
      rcases branch_cover (hr rel a ha) with hn | hp'
      · obtain ⟨hl, ht⟩ := ihneg hc.1 (pathHolds_append hp hn)
        refine ⟨hl, fun hlen => ?_⟩
        obtain ⟨p, i, s, w, t, hroute, hpath, hag, hb, he, hst⟩ := ht hlen
        exact ⟨p, i, s, w, t, .negative ha hn hroute, hpath, hag, hb, he, hst⟩
      · obtain ⟨hl, ht⟩ := ihpos hc.2 (pathHolds_append hp hp')
        refine ⟨hl, fun hlen => ?_⟩
        obtain ⟨p, i, s, w, t, hroute, hpath, hag, hb, he, hst⟩ := ht hlen
        exact ⟨p, i, s, w, t, .positive ha hp' hroute, hpath, hag, hb, he, hst⟩

abbrev Marks (n : ℕ) := Fin (n + 1) → ℝ

/-- Marks are ordered because every positive index difference has length at least one. -/
structure RealGolomb {n : ℕ} (x : Marks n) : Prop where
  minDistance : ∀ i j, i < j → 1 ≤ x j - x i
  pairSeparation : ∀ i j k l, i < j → k < l → (i, j) ≠ (k, l) →
    1 ≤ |(x j - x i) - (x l - x k)|

structure Span (n : ℕ) where
  lo : Fin (n + 1)
  hi : Fin (n + 1)
  increasing : lo < hi
deriving DecidableEq

def Span.size {n : ℕ} (q : Span n) : ℕ := q.hi.val - q.lo.val

def Span.normal {n : ℕ} (q : Span n) (i : Fin n) : ℤ :=
  if q.lo.val ≤ i.val ∧ i.val < q.hi.val then 1 else 0

def Span.dist {n : ℕ} (q : Span n) (x : Marks n) : ℝ := x q.hi - x q.lo

def gaps {n : ℕ} (x : Marks n) (i : Fin n) : ℝ := x i.succ - x i.castSucc

def endLength {n : ℕ} (x : Marks n) : ℝ := x (Fin.last n) - x 0

def positions {n : ℕ} (g : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  eval (fun i => if i.val < j.val then 1 else 0) g

private theorem prefix_succ {n : ℕ} (g : Fin n → ℝ) (i : Fin n) :
    positions g i.succ = positions g i.castSucc + g i := by
  have hnormal : (fun j : Fin n => if j.val < i.succ.val then (1 : ℤ) else 0) =
      fun j => (if j.val < i.castSucc.val then 1 else 0) + (if j = i then 1 else 0) := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · have hne : j.val ≠ i.val := fun he => h (Fin.ext he)
      have he : j.val < i.succ.val ↔ j.val < i.castSucc.val := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      simp only [he, if_neg h, add_zero]
  unfold positions
  rw [hnormal, eval_add]
  congr 1
  rw [eval, Finset.sum_eq_single i]
  · simp
  · intro j _ hne
    simp [hne]
  · simp

theorem prefix_gaps {n : ℕ} (x : Marks n) (j : Fin (n + 1)) :
    positions (gaps x) j = x j - x 0 := by
  induction j using Fin.induction with
  | zero => simp [positions, eval]
  | succ i ih =>
    rw [prefix_succ, ih, gaps]
    ring

private theorem span_eval_prefix {n : ℕ} (q : Span n) (g : Fin n → ℝ) :
    eval q.normal g = positions g q.hi - positions g q.lo := by
  unfold positions
  rw [← eval_sub]
  congr 1
  funext i
  have h := q.increasing
  change q.lo.val < q.hi.val at h
  by_cases hlo : i.val < q.lo.val
  · have hhi := hlo.trans h
    simp [Span.normal, hlo, hhi, not_le_of_gt hlo]
  · simp [Span.normal, hlo, le_of_not_gt hlo]

private theorem span_eval_gaps {n : ℕ} (q : Span n) (x : Marks n) :
    eval q.normal (gaps x) = q.dist x := by
  rw [span_eval_prefix, prefix_gaps, prefix_gaps, Span.dist]
  ring

theorem length_gaps {n : ℕ} (x : Marks n) : length (gaps x) = endLength x := by
  unfold endLength
  rw [← prefix_gaps x (Fin.last n)]
  simp [length, positions, eval, Fin.isLt]

def Separated {n : ℕ} (g : Fin n → ℝ) : Prop := RealGolomb (positions g)

theorem separated_gaps {n : ℕ} {x : Marks n} (hx : RealGolomb x) : Separated (gaps x) := by
  constructor
  · intro i j h
    have h' := hx.minDistance i j h
    rw [prefix_gaps, prefix_gaps]
    linarith
  · intro i j k l hij hkl hne
    have h' := hx.pairSeparation i j k l hij hkl hne
    convert h' using 2 <;> simp only [prefix_gaps] <;> ring

theorem span_min {n : ℕ} (q : Span n) {g : Fin n → ℝ} (hg : Separated g) :
    1 ≤ eval q.normal g := by
  rw [span_eval_prefix]
  exact hg.minDistance q.lo q.hi q.increasing

theorem span_separation {n : ℕ} {q r : Span n} {g : Fin n → ℝ}
    (hg : Separated g) (hqr : q ≠ r) : 1 ≤ |eval q.normal g - eval r.normal g| := by
  rw [span_eval_prefix, span_eval_prefix]
  apply hg.pairSeparation _ _ _ _ q.increasing r.increasing
  intro h
  apply hqr
  cases q
  cases r
  obtain ⟨hlo, hhi⟩ := Prod.mk.inj h
  subst_vars
  rfl

def Span.unit {n : ℕ} (i : Fin n) : Span n :=
  ⟨i.castSucc, i.succ, Nat.lt_succ_self i.val⟩

def Span.normalSum {n m : ℕ} (slots : Fin m → Span n) (i : Fin n) : ℤ :=
  ∑ s, (slots s).normal i

theorem eval_normalSum {n m : ℕ} (slots : Fin m → Span n) (g : Fin n → ℝ) :
    eval (Span.normalSum slots) g = ∑ s, eval (slots s).normal g := by
  simp only [eval, Span.normalSum, Int.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem packing_valid {n m : ℕ} (slots : Fin m → Span n) (hinj : Function.Injective slots)
    {g : Fin n → ℝ} (hg : Separated g) :
    (m : ℝ) * ((m : ℝ) + 1) / 2 ≤ eval (Span.normalSum slots) g := by
  rw [eval_normalSum]
  exact (packing_bound_and_saturation
    (fun s => eval (slots s).normal g) (fun i => span_min (slots i) hg)
    (fun i j hij => span_separation hg (fun h => hij (hinj h)))).1

/-- Relabel a contiguous window by its initial mark and the number of gaps. -/
def Span.embed {n : ℕ} (q : Span n) (i : Fin (q.size + 1)) : Fin (n + 1) :=
  ⟨q.lo.val + i.val, by
    have hi := q.hi.isLt
    have hq := q.increasing
    change q.lo.val < q.hi.val at hq
    have hsize := i.isLt
    unfold Span.size at hsize
    omega⟩

private theorem Span.embed_lt {n : ℕ} (q : Span n) {i j : Fin (q.size + 1)} :
    q.embed i < q.embed j ↔ i < j := by
  change q.lo.val + i.val < q.lo.val + j.val ↔ i.val < j.val
  omega

private theorem Span.embed_injective {n : ℕ} (q : Span n) : Function.Injective q.embed := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  change q.lo.val + i.val = q.lo.val + j.val at he
  omega

private theorem Span.embed_zero {n : ℕ} (q : Span n) : q.embed 0 = q.lo := by
  apply Fin.ext
  simp [Span.embed]

private theorem Span.embed_last {n : ℕ} (q : Span n) : q.embed (Fin.last q.size) = q.hi := by
  apply Fin.ext
  have h := q.increasing
  change q.lo.val < q.hi.val at h
  change q.lo.val + (q.hi.val - q.lo.val) = q.hi.val
  omega

private theorem contiguous_golomb {n : ℕ} {x : Marks n} (hx : RealGolomb x) (q : Span n) :
    RealGolomb (x ∘ q.embed) := by
  constructor
  · intro i j hij
    exact hx.minDistance _ _ (q.embed_lt.mpr hij)
  · intro i j k l hij hkl hne
    apply hx.pairSeparation _ _ _ _ (q.embed_lt.mpr hij) (q.embed_lt.mpr hkl)
    intro h
    obtain ⟨hl, hr⟩ := Prod.mk.inj h
    exact hne (Prod.ext (q.embed_injective hl) (q.embed_injective hr))

/-- The argument of the table is the number of gaps, one fewer than the number of marks. -/
def LowerBound (n : ℕ) (target : ℤ) : Prop :=
  ∀ x : Marks n, RealGolomb x → (target : ℝ) ≤ endLength x

private theorem subruler_valid {n : ℕ} (q : Span n) {target : ℤ} (h : LowerBound q.size target)
    {g : Fin n → ℝ} (hg : Separated g) :
    (target : ℝ) ≤ eval q.normal g := by
  have hb := h (positions g ∘ q.embed) (contiguous_golomb hg q)
  simpa [endLength, q.embed_zero, q.embed_last, span_eval_prefix] using hb

def reflect {n : ℕ} (x : Marks n) : Marks n :=
  fun i => x (Fin.last n) - x i.rev

theorem reflect_golomb {n : ℕ} {x : Marks n} (hx : RealGolomb x) :
    RealGolomb (reflect x) := by
  constructor
  · intro i j hij
    have h := hx.minDistance j.rev i.rev (Fin.rev_lt_rev.mpr hij)
    unfold reflect
    linarith
  · intro i j k l hij hkl hne
    have hne' : (j.rev, i.rev) ≠ (l.rev, k.rev) := by
      intro h
      obtain ⟨hl, hr⟩ := Prod.mk.inj h
      exact hne (Prod.ext (Fin.rev_injective hr) (Fin.rev_injective hl))
    have h := hx.pairSeparation _ _ _ _ (Fin.rev_lt_rev.mpr hij) (Fin.rev_lt_rev.mpr hkl) hne'
    convert h using 2 <;> unfold reflect <;> ring

theorem reflect_length {n : ℕ} (x : Marks n) : endLength (reflect x) = endLength x := by
  simp [endLength, reflect]



def mirrorNormal {n : ℕ} (i : Fin n) : ℤ :=
  (if i.val + 1 = n then 1 else 0) - (if i.val = 0 then 1 else 0)

def Oriented {n : ℕ} (g : Fin n → ℝ) : Prop := 1 ≤ eval mirrorNormal g

private theorem eval_mirror {n : ℕ} (g : Fin (n + 1) → ℝ) :
    eval mirrorNormal g = g (Fin.last n) - g 0 := by
  have hlast : (fun i : Fin (n + 1) => if i.val + 1 = n + 1 then (1 : ℤ) else 0) =
      fun i => if i = Fin.last n then 1 else 0 := by
    funext i
    have h : i.val + 1 = n + 1 ↔ i = Fin.last n := by
      rw [← Fin.val_inj]
      simp only [Fin.val_last, Nat.add_right_cancel_iff]
    simp only [h]
  have hzero : (fun i : Fin (n + 1) => if i.val = 0 then (1 : ℤ) else 0) =
      fun i => if i = 0 then 1 else 0 := by
    funext i
    have h : i.val = 0 ↔ i = 0 := by
      change i.val = (0 : Fin (n + 1)).val ↔ i = 0
      exact Fin.val_inj
    simp only [h]
  have hsingle (j : Fin (n + 1)) :
      eval (fun i => if i = j then 1 else 0) g = g j := by
    rw [eval, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  unfold mirrorNormal
  rw [eval_sub, hlast, hzero, hsingle, hsingle]

theorem reflect_gaps {n : ℕ} (x : Marks n) (i : Fin n) :
    gaps (reflect x) i = gaps x i.rev := by
  simp only [gaps, reflect, Fin.rev_succ, Fin.rev_castSucc]
  ring

theorem symmetry_coverage {k : ℕ} {x : Marks (k + 2)} (hx : RealGolomb x) :
    Oriented (gaps x) ∨ Oriented (gaps (reflect x)) := by
  have h := hx.pairSeparation (Fin.last (k + 1)).castSucc (Fin.last (k + 1)).succ
    (0 : Fin (k + 2)).castSucc (0 : Fin (k + 2)).succ
    (Nat.lt_succ_self _) (Nat.lt_succ_self _) (by
      intro h
      have hv := congrArg (fun q : Fin (k + 3) × Fin (k + 3) => q.1.val) h
      simp at hv)
  change 1 ≤ |gaps x (Fin.last (k + 1)) - gaps x 0| at h
  rcases le_abs.mp h with hp | hn
  · left
    simpa [Oriented, eval_mirror] using hp
  · right
    have he : gaps (reflect x) (Fin.last (k + 1)) - gaps (reflect x) 0 =
        -(gaps x (Fin.last (k + 1)) - gaps x 0) := by
      simp only [reflect_gaps, Fin.rev_last, Fin.rev_zero]
      ring
    simpa only [Oriented, eval_mirror, he] using hn

inductive RelationWitness (n : ℕ) where
  | distance (span : Span n)
  | difference (plus minus : Span n) (distinct : plus ≠ minus)

def RelationWitness.normal {n : ℕ} : RelationWitness n → Fin n → ℤ
  | .distance q => q.normal
  | .difference p q _ => fun i => p.normal i - q.normal i

private theorem RelationWitness.valid {n : ℕ} (w : RelationWitness n) {g : Fin n → ℝ}
    (hg : Separated g) : 1 ≤ |eval w.normal g| := by
  cases w with
  | distance q => exact (span_min q hg).trans (le_abs_self _)
  | difference p q hpq =>
    change 1 ≤ |eval (fun i => p.normal i - q.normal i) g|
    rw [eval_sub]
    exact span_separation hg hpq

def relationRows {n : ℕ} (witnesses : Array (RelationWitness n)) : Array (Fin n → ℤ) :=
  witnesses.map RelationWitness.normal

theorem relationRows_valid {n : ℕ} (witnesses : Array (RelationWitness n))
    {g : Fin n → ℝ} (hg : Separated g) : RelationsValid (relationRows witnesses) g := by
  intro i a ha
  rw [relationRows, Array.getElem?_map] at ha
  cases h : witnesses[i]? with
  | none => simp [h] at ha
  | some w =>
    have he : w.normal = a := by simpa [h] using ha
    subst a
    exact w.valid hg

inductive Static (n : ℕ) where
  | mirror
  | unit (i : Fin n)
  | sub (span : Span n) (rhs : ℤ)
  | pack (slots : List (Span n)) (rhs : ℤ)

def Static.row {n : ℕ} : Static n → Row n
  | .mirror => ⟨mirrorNormal, 1⟩
  | .unit i => ⟨(Span.unit i).normal, 1⟩
  | .sub q b => ⟨q.normal, b⟩
  | .pack qs b => ⟨Span.normalSum (fun i => qs.get i), b⟩

/-- The table gives certified lower bounds by gap count. The checker tests each
packing row against its actual set of interval slots and each subruler against
the corresponding size in the table. -/
def Static.check {n : ℕ} (bounds : ℕ → ℤ) : Static n → Bool
  | .mirror | .unit _ => true
  | .sub q b => decide (q.size < n) && decide (0 ≤ b) && decide (b ≤ bounds q.size)
  | .pack qs b =>
    decide qs.Nodup && decide (0 ≤ b) && decide (2 * b ≤ (qs.length : ℤ) * (qs.length + 1))

def SmallerBounds (n : ℕ) (bounds : ℕ → ℤ) : Prop :=
  ∀ k < n, LowerBound k (bounds k)

private theorem Static.valid {n : ℕ} (r : Static n) {bounds : ℕ → ℤ} (hb : SmallerBounds n bounds)
    (hc : r.check bounds = true) {g : Fin n → ℝ} (hg : Separated g) (hy : Oriented g) :
    r.row.Holds g := by
  cases r with
  | mirror => simpa [Static.row, Row.Holds, Oriented] using hy
  | unit i =>
    simpa [Static.row, Row.Holds] using span_min (Span.unit i) hg
  | sub q b =>
    simp only [Static.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hrs : (b : ℝ) ≤ (bounds q.size : ℝ) := by exact_mod_cast hc.2
    exact hrs.trans (subruler_valid q (hb q.size hc.1.1) hg)
  | pack qs b =>
    simp only [Static.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hb' : (2 : ℝ) * (b : ℝ) ≤ (qs.length : ℝ) * ((qs.length : ℝ) + 1) := by
      exact_mod_cast hc.2
    have htri : (b : ℝ) ≤ (qs.length : ℝ) * ((qs.length : ℝ) + 1) / 2 := by linarith
    exact htri.trans (packing_valid (fun i => qs.get i) (List.nodup_iff_injective_get.mp hc.1.1) hg)

def staticRows {n : ℕ} (data : Array (Static n)) : Array (Row n) := data.map Static.row

def checkStatic {n : ℕ} (data : Array (Static n)) (bounds : ℕ → ℤ) : Bool :=
  data.toList.all (Static.check bounds)

theorem staticRows_valid {n : ℕ} (data : Array (Static n)) {bounds : ℕ → ℤ}
    (hb : SmallerBounds n bounds) (hc : checkStatic data bounds = true)
    {g : Fin n → ℝ} (hg : Separated g) (hy : Oriented g) :
    Valid (fun i : ℕ => (staticRows data)[i]?) g := by
  intro i r hr
  change (staticRows data)[i]? = some r at hr
  rw [staticRows, Array.getElem?_map] at hr
  cases h : data[i]? with
  | none => simp [h] at hr
  | some s =>
    have he : s.row = r := by simpa [h] using hr
    subst r
    exact s.valid hb (List.all_eq_true.mp hc s (by simpa using Array.mem_of_getElem? h)) hg hy

/-- A kernel-checked archive tree proves a lower bound for all real rulers.
Reflection supplies the archive's symmetry row without restricting the conclusion. -/
theorem replay_marks {k : ℕ} {target : ℤ} {bounds : ℕ → ℤ}
    {data : Array (Static (k + 2))} {witnesses : Array (RelationWitness (k + 2))} {tree : Tree}
    (hb : SmallerBounds (k + 2) bounds) (hs : checkStatic data bounds = true)
    (ht : tree.check target (staticRows data) (relationRows witnesses) [] = true) :
    LowerBound (k + 2) target := by
  intro x hx
  have run (y : Marks (k + 2)) (hy : RealGolomb y) (ho : Oriented (gaps y)) :
      (target : ℝ) ≤ endLength y := by
    rw [← length_gaps]
    have hg := separated_gaps hy
    exact (Tree.check_sound ht (staticRows_valid data hb hs hg ho)
      (relationRows_valid witnesses hg) (by simp [PathHolds])).1
  rcases symmetry_coverage hx with h | h
  · exact run x hx h
  · simpa only [reflect_length] using run (reflect x) (reflect_golomb hx) h

private theorem span_le_length {n : ℕ} {x : Marks n} (hx : RealGolomb x) (q : Span n) :
    q.dist x ≤ endLength x := by
  have hm : Monotone x := by
    intro i j hij
    rcases hij.eq_or_lt with he | hlt
    · exact he ▸ le_rfl
    · have h := hx.minDistance i j hlt
      linarith
  have hlo := hm (Fin.zero_le q.lo)
  have hhi := hm (Fin.le_last q.hi)
  unfold Span.dist endLength
  linarith

private theorem lower_by_distinct_spans {n m : ℕ} (qs : Fin (m + 1) → Span n)
    (hinj : Function.Injective qs) {x : Marks n} (hx : RealGolomb x) :
    ((m + 1 : ℕ) : ℝ) ≤ endLength x := by
  let d : Fin (m + 1) → ℝ := fun i => (qs i).dist x
  have hmin (i : Fin (m + 1)) : 1 ≤ d i :=
    hx.minDistance _ _ (qs i).increasing
  have hsep (i j : Fin (m + 1)) (hij : i ≠ j) : 1 ≤ |d i - d j| := by
    simpa only [d, span_eval_gaps] using
      (span_separation (separated_gaps hx) (fun h : qs i = qs j => hij (hinj h)))
  have h := rank_le_sorted d hmin hsep (Fin.last m)
  have hup := span_le_length hx (qs (Tuple.sort d (Fin.last m)))
  exact (by simpa using h.trans hup)

private theorem lower_zero : LowerBound 0 0 := by
  intro x _
  have he : Fin.last 0 = (0 : Fin 1) := rfl
  simp [endLength, he]

private theorem lower_two_marks : LowerBound 1 1 := by
  intro x hx
  have h := hx.minDistance 0 (Fin.last 1) (by decide)
  simpa [endLength] using h

private def spans3 : Fin 3 → Span 2 :=
  ![⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨1, 2, by decide⟩]

private def spans4 : Fin 6 → Span 3 :=
  ![⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨0, 3, by decide⟩,
    ⟨1, 2, by decide⟩, ⟨1, 3, by decide⟩, ⟨2, 3, by decide⟩]

private theorem spans3_inj : ∀ i j, spans3 i = spans3 j → i = j := by decide +kernel
private theorem spans4_inj : ∀ i j, spans4 i = spans4 j → i = j := by decide +kernel

private theorem lower_three_marks : LowerBound 2 3 := by
  intro x hx
  exact_mod_cast lower_by_distinct_spans spans3 (fun _ _ => spans3_inj _ _) hx

private theorem lower_four_marks : LowerBound 3 6 := by
  intro x hx
  exact_mod_cast lower_by_distinct_spans spans4 (fun _ _ => spans4_inj _ _) hx

def archiveBounds : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 6
  | 4 => 11
  | 5 => 17
  | 6 => 25
  | 7 => 34
  | 8 => 44
  | 9 => 55
  | _ => 0

theorem smaller_extend {n : ℕ} {bounds : ℕ → ℤ}
    (h : SmallerBounds n bounds) (hn : LowerBound n (bounds n)) :
    SmallerBounds (n + 1) bounds := by
  intro k hk
  rcases (Nat.lt_succ_iff.mp hk).eq_or_lt with he | hl
  · subst k
    exact hn
  · exact h k hl

theorem base_bounds : SmallerBounds 4 archiveBounds := by
  intro k hk
  interval_cases k
  · exact lower_zero
  · exact lower_two_marks
  · exact lower_three_marks
  · exact lower_four_marks

end D5.S3.Combinatorics.Golomb.Replay
