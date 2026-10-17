/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Executable attained chart, occurrence-sensitive target, and exact finite three-reply menu minimax with attaining tree and universal lower bound. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax

open GenealogicalFiberTransport (Source substitution)
open ActualCutPartitionRecovery (LiteralRow CutSet CutPrefixFree canonicalRow rowAt holeAddresses)
open NativeCutFibers (Classes labels)
open NativeClassRootImage
open NativeClassRootPadding
open NativeClassRootSimulation (Chart RootTree rootRun rootDepth)
open NativeFullRootFeasibility

/-! A Boolean front end for the exact semantic chart predicate. -/

def litCode (θ : Nat → Option Bool) (b : Bool) : LiteralRow → Bool
  | .of (.inl c) => decide (c = b)
  | .of (.inr n) => decide (θ n = some b)
  | .mul _ _ => false

def imCode (θ : Nat → Option Bool) : LiteralRow → Bool
  | .of (.inl b) => decide (b = false)
  | .of (.inr n) => decide (θ n ≠ some true)
  | .mul l r =>
      (litCode θ false l && litCode θ true r) || (imCode θ l && imCode θ r)

def admissibleCode (C : LiteralRow) (θ : Classes C → Option Bool) : Bool :=
  imCode (typeExtend C θ) C &&
    decide ((Finset.univ.filter (fun d => θ d = some true)).card ≤ 1) &&
    decide ((Finset.univ.filter (fun d => θ d = some false)).card ≤ 1)

private theorem litCode_spec (θ : Nat → Option Bool) (b : Bool) (C : LiteralRow) :
    litCode θ b C = true ↔ lit θ b C := by
  induction C with
  | of c => cases c <;> simp [litCode, lit]
  | mul l r => simp [litCode, lit]

private theorem imCode_spec (θ : Nat → Option Bool) (C : LiteralRow) :
    imCode θ C = true ↔ im θ C := by
  induction C with
  | of c => cases c <;> simp [imCode, im]
  | mul l r =>
      simp [imCode, im, litCode_spec θ false, litCode_spec θ true, *]

theorem admissibleCode_spec (C : LiteralRow) (θ : Classes C → Option Bool) :
    admissibleCode C θ = true ↔ Admissible C θ := by
  unfold admissibleCode
  simp only [Bool.and_eq_true]
  rw [imCode_spec]
  constructor
  · rintro ⟨⟨hi, ha⟩, hb⟩
    exact ⟨hi, of_decide_eq_true ha, of_decide_eq_true hb⟩
  · rintro ⟨hi, ha, hb⟩
    exact ⟨⟨hi, decide_eq_true ha⟩, decide_eq_true hb⟩

def assignmentList (C : LiteralRow) : List (Classes C → Option Bool) :=
  ((NativeWholeRowService.classList C).pi (fun _ => [none, some false, some true])).map
    (fun f d => f d (NativeWholeRowService.class_complete C d))

private theorem assignmentList_complete (C : LiteralRow) (θ : Classes C → Option Bool) :
    θ ∈ assignmentList C := by
  apply List.mem_map.mpr
  refine ⟨fun d _ => θ d, ?_, rfl⟩
  apply (List.mem_pi _ _).mpr
  intro d hd
  cases θ d with
  | none => simp
  | some b => cases b <;> simp

def chartList (C : LiteralRow) : List (Chart C) :=
  ((assignmentList C).filter (fun θ => admissibleCode C θ)).dedup.attach.map (fun a =>
    ⟨a.1, (admissibleCode_spec C a.1).mp (List.mem_filter.mp (List.mem_dedup.mp a.2)).2⟩)

private theorem chartList_complete (C : LiteralRow) (θ : Chart C) :
    θ ∈ chartList C := by
  apply List.mem_map.mpr
  refine ⟨⟨θ.val, List.mem_dedup.mpr (List.mem_filter.mpr ⟨assignmentList_complete C θ.val,
    (admissibleCode_spec C θ.val).mpr θ.property⟩)⟩, by simp, rfl⟩

private theorem chartList_card (C : LiteralRow) :
    (chartList C).toFinset.card ≤ 3 ^ Fintype.card (Classes C) := by
  classical
  calc
    (chartList C).toFinset.card ≤ Fintype.card (Chart C) := Finset.card_le_univ _
    _ ≤ Fintype.card (Classes C → Option Bool) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 3 ^ Fintype.card (Classes C) := by simp

private theorem chartList_length_bound (C : LiteralRow) :
    (chartList C).length ≤ 3 ^ Fintype.card (Classes C) := by
  have hn : (chartList C).Nodup := by
    unfold chartList
    apply List.Nodup.map
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun x : Chart C => x.val) h
    · exact List.nodup_attach.mpr (List.nodup_dedup _)
  rw [← List.toFinset_card_of_nodup hn]
  exact chartList_card C

def visibleAlphaCode (C : LiteralRow) (θ : Classes C → Option Bool)
    (p : ActualTreeReadoutAcquisition.Address) : Bool :=
  match rowAt p C with
  | none => false
  | some e => litCode (typeExtend C θ) true e

private theorem visibleAlphaCode_spec (C : LiteralRow) (θ : Classes C → Option Bool)
    (p : ActualTreeReadoutAcquisition.Address) :
    visibleAlphaCode C θ p = true ↔ VisibleAlpha C θ p := by
  cases he : rowAt p C <;> simp [visibleAlphaCode, VisibleAlpha, he, litCode_spec]

def newbornCode (C : LiteralRow) (θ : Classes C → Option Bool)
    (p : ActualTreeReadoutAcquisition.Address) : Bool :=
  match p.reverse with
  | [] => false
  | _ :: qs => visibleAlphaCode C θ (qs.reverse ++ [true])

private theorem newbornCode_spec (C : LiteralRow) (θ : Classes C → Option Bool)
    (p : ActualTreeReadoutAcquisition.Address) :
    newbornCode C θ p = true ↔
      ∃ q d, p = q ++ [d] ∧ VisibleAlpha C θ (q ++ [true]) := by
  induction p using List.reverseRecOn with
  | nil => simp [newbornCode]
  | append_singleton q d ih =>
      simp only [newbornCode, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append,
        List.reverse_reverse]
      rw [visibleAlphaCode_spec]
      constructor
      · intro hv
        exact ⟨q,d,rfl,hv⟩
      · rintro ⟨t,e,heq,hv⟩
        have hrev : d :: q.reverse = e :: t.reverse := by
          simpa using congrArg List.reverse heq
        have hqt : q = t := List.reverse_injective (List.cons.inj hrev).2
        simpa [hqt] using hv

def computedOldMask (C : LiteralRow) (θ : Classes C → Option Bool) : CutSet :=
  (holeAddresses [] C).toFinset.filter (fun p => newbornCode C θ p = false)

private theorem computedOldMask_spec (C : LiteralRow) (θ : Classes C → Option Bool) :
    computedOldMask C θ = oldMask C θ := by
  classical
  ext p
  simp only [computedOldMask, oldMask, Finset.mem_filter]
  have hb := newbornCode_spec C θ p
  cases h : newbornCode C θ p <;> simp_all

def computedTarget (C : LiteralRow) (θ : Classes C → Option Bool) : LiteralRow :=
  (NativePredecessorRowRecovery.back C (computedOldMask C θ)).getD (.of (.inl true))

private theorem computedTarget_spec (C : LiteralRow) (θ : Classes C → Option Bool) :
    computedTarget C θ = target C θ := by
  rw [computedTarget, computedOldMask_spec]
  rfl

/-! The executable table stores the complete target and all three attained
root replies.  It has no origin, source-size, or word-length field. -/

structure TableRow (C : LiteralRow) where
  type : Classes C → Option Bool
  admissible : Admissible C type
  target : LiteralRow
  target_eq : target = computedTarget C type

def tableRows (C : LiteralRow) : List (TableRow C) :=
  (chartList C).map (fun θ =>
    let t := computedTarget C θ.val
    { type := θ.val, admissible := θ.property, target := t,
      target_eq := by
        change t = t
        exact rfl })

def replyCell {C : LiteralRow} (W : List (TableRow C))
    (d : Classes C) (y : Option Bool) : List (TableRow C) :=
  W.filter (fun row => row.type d = y)

def rowTargets {C : LiteralRow} (W : List (TableRow C)) : List LiteralRow :=
  W.map TableRow.target

def constantTarget {C : LiteralRow} (W : List (TableRow C)) : Bool :=
  match rowTargets W with
  | [] => true
  | x :: xs => xs.all (· = x)

/-! Unit-call minimax is a finite executable dynamic-programming front end on
 attained rows.  The retained tree type has exactly the actual class menu and
 three reached replies; the absent fourth native edge is supplied by install. -/

def menuList (C : LiteralRow) : List (Classes C) :=
  NativeWholeRowService.classList C

def splitCoordinate {C : LiteralRow} (W : List (TableRow C)) (d : Classes C) : Bool :=
  ((! (replyCell W d (some true)).isEmpty) &&
      (! (replyCell W d (some false)).isEmpty)) ||
    ((! (replyCell W d (some true)).isEmpty) &&
      (! (replyCell W d none).isEmpty)) ||
    ((! (replyCell W d (some false)).isEmpty) &&
      (! (replyCell W d none).isEmpty))

def splittingCoordinates (C : LiteralRow) (W : List (TableRow C)) : List (Classes C) :=
  (menuList C).filter (splitCoordinate W)

def targetsConstant {C : LiteralRow} (W : List (TableRow C)) : Prop :=
  ∀ ⦃a⦄, a ∈ W → ∀ ⦃b⦄, b ∈ W → a.target = b.target

private theorem constantTarget_true_iff {C : LiteralRow} (W : List (TableRow C)) :
    constantTarget W = true ↔ targetsConstant W := by
  cases W with
  | nil => simp [constantTarget, rowTargets, targetsConstant]
  | cons a W =>
      constructor
      · intro h x hx y hy
        have hall : ∀ z ∈ W, z.target = a.target := by
          intro z hz
          have hz' : z.target ∈ W.map TableRow.target :=
            List.mem_map.mpr ⟨z, hz, rfl⟩
          have hh : (W.map TableRow.target).all (· = a.target) = true := by
            simpa [constantTarget, rowTargets] using h
          exact of_decide_eq_true (List.all_eq_true.mp hh _ hz')
        rcases (List.mem_cons.mp hx) with rfl | hx'
        · rcases (List.mem_cons.mp hy) with rfl | hy'
          · rfl
          · exact (hall y hy').symm
        · rcases (List.mem_cons.mp hy) with rfl | hy'
          · exact hall x hx'
          · exact (hall x hx').trans (hall y hy').symm
      · intro h
        have hh : (W.map TableRow.target).all (· = a.target) = true := by
          apply List.all_eq_true.mpr
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          exact decide_eq_true (h (a := y) (by simp [hy]) (b := a) (by simp))
        simpa [constantTarget, rowTargets] using hh

private theorem target_eq_of_type_eq {C : LiteralRow} {a b : TableRow C}
    (h : a.type = b.type) : a.target = b.target := by
  rw [a.target_eq, b.target_eq, h]

private theorem menuList_complete (C : LiteralRow) (d : Classes C) : d ∈ menuList C :=
  NativeWholeRowService.class_complete C d

private theorem filter_length_lt_of_mem_not {α : Type}
    (p : α → Bool) (W : List α) {a : α} (ha : a ∈ W) (hnot : p a = false) :
    (W.filter p).length < W.length := by
  apply lt_of_le_of_ne (List.length_filter_le p W)
  intro heq
  have hall : ∀ x ∈ W, p x = true :=
    List.length_filter_eq_length_iff.mp heq
  exact Bool.noConfusion ((hall a ha).symm.trans hnot)

private theorem splitCoordinate_of_replies {C : LiteralRow}
    {W : List (TableRow C)} {a b : TableRow C} {d : Classes C}
    (ha : a ∈ W) (hb : b ∈ W) (hdiff : a.type d ≠ b.type d) :
    splitCoordinate W d = true := by
  have haCell : a ∈ replyCell W d (a.type d) := by simp [replyCell, ha]
  have hbCell : b ∈ replyCell W d (b.type d) := by simp [replyCell, hb]
  have haNe : replyCell W d (a.type d) ≠ [] := by
    intro hz
    rw [hz] at haCell
    simp at haCell
  have hbNe : replyCell W d (b.type d) ≠ [] := by
    intro hz
    rw [hz] at hbCell
    simp at hbCell
  cases hA : a.type d with
  | none =>
      cases hB : b.type d with
      | none => exact False.elim (hdiff (hA.trans hB.symm))
      | some vb =>
          cases vb with
          | false =>
              have haN : replyCell W d none ≠ [] := by simpa [hA] using haNe
              have hbN : replyCell W d (some false) ≠ [] := by simpa [hB] using hbNe
              simp [splitCoordinate, haN, hbN]
          | true =>
              have haN : replyCell W d none ≠ [] := by simpa [hA] using haNe
              have hbN : replyCell W d (some true) ≠ [] := by simpa [hB] using hbNe
              simp [splitCoordinate, haN, hbN]
  | some va =>
      cases hB : b.type d with
      | none =>
          cases va with
          | false =>
              have haN : replyCell W d (some false) ≠ [] := by simpa [hA] using haNe
              have hbN : replyCell W d none ≠ [] := by simpa [hB] using hbNe
              simp [splitCoordinate, haN, hbN]
          | true =>
              have haN : replyCell W d (some true) ≠ [] := by simpa [hA] using haNe
              have hbN : replyCell W d none ≠ [] := by simpa [hB] using hbNe
              simp [splitCoordinate, haN, hbN]
      | some vb =>
          have hne : va ≠ vb := by
            intro he
            exact hdiff (hA.trans ((congrArg some he).trans hB.symm))
          cases va with
          | false =>
              cases vb with
              | false => exact False.elim (hne rfl)
              | true =>
                  have haN : replyCell W d (some false) ≠ [] := by simpa [hA] using haNe
                  have hbN : replyCell W d (some true) ≠ [] := by simpa [hB] using hbNe
                  simp [splitCoordinate, haN, hbN]
          | true =>
              cases vb with
              | false =>
                  have haN : replyCell W d (some true) ≠ [] := by simpa [hA] using haNe
                  have hbN : replyCell W d (some false) ≠ [] := by simpa [hB] using hbNe
                  simp [splitCoordinate, haN, hbN]
              | true => exact False.elim (hne rfl)

private theorem splitCoordinate_of_distinct_types {C : LiteralRow}
    {W : List (TableRow C)} {a b : TableRow C} (ha : a ∈ W) (hb : b ∈ W)
    (hd : a.type ≠ b.type) : ∃ d : Classes C,
      d ∈ menuList C ∧ splitCoordinate W d = true := by
  classical
  have hfun : ¬ (∀ d : Classes C, a.type d = b.type d) := by
    intro heq
    exact hd (funext heq)
  obtain ⟨d, hdiff⟩ := Classical.not_forall.mp hfun
  have hsplit := splitCoordinate_of_replies ha hb hdiff
  exact ⟨d, menuList_complete C d, hsplit⟩

private theorem splittingCoordinates_nonempty_of_nonconstant {C : LiteralRow}
    {W : List (TableRow C)} (h : constantTarget W = false) :
    ∃ d, d ∈ splittingCoordinates C W := by
  classical
  have hnot : ¬ targetsConstant W := by
    intro hc
    have ht := (constantTarget_true_iff W).mpr hc
    exact Bool.noConfusion (ht.symm.trans h)
  have hpairs : ∃ a ∈ W, ∃ b ∈ W, a.target ≠ b.target := by
    by_contra hn
    apply hnot
    intro a ha b hb
    by_contra hab
    exact hn ⟨a,ha,b,hb,hab⟩
  obtain ⟨a,ha,b,hb,hab⟩ := hpairs
  have htypes : a.type ≠ b.type := by
    intro heq
    apply hab
    exact target_eq_of_type_eq heq
  obtain ⟨d, hd, hs⟩ := splitCoordinate_of_distinct_types ha hb htypes
  exact ⟨d, List.mem_filter.mpr ⟨hd, hs⟩⟩

private theorem replyCell_length_lt_of_split {C : LiteralRow}
    {W : List (TableRow C)} {d : Classes C}
    (hs : splitCoordinate W d = true) (y : Option Bool)
    (hy : replyCell W d y ≠ []) :
    (replyCell W d y).length < W.length := by
  classical
  have lt_of_other (z : Option Bool) (hz : replyCell W d z ≠ [])
      (hne : z ≠ y) : (replyCell W d y).length < W.length := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hz
    have hxz : x.type d = z := by
      have := (List.mem_filter.mp hx).2
      exact of_decide_eq_true this
    have hnot : decide (x.type d = y) = false := by
      rw [decide_eq_false_iff_not]
      intro hxy
      exact hne (hxz.symm.trans hxy)
    have hh := filter_length_lt_of_mem_not
      (fun x : TableRow C => decide (x.type d = y)) W (List.mem_filter.mp hx |>.1) hnot
    simpa [replyCell] using hh
  have hs' :
      ((replyCell W d (some true) ≠ [] ∧ replyCell W d (some false) ≠ []) ∨
      (replyCell W d (some true) ≠ [] ∧ replyCell W d none ≠ [])) ∨
      (replyCell W d (some false) ≠ [] ∧ replyCell W d none ≠ []) := by
    simpa [splitCoordinate] using hs
  rcases hs' with (htf | htn) | hfn
  · cases y with
    | none => exact lt_of_other (some true) htf.1 (by simp)
    | some b => cases b with
      | true => exact lt_of_other (some false) htf.2 (by simp)
      | false => exact lt_of_other (some true) htf.1 (by simp)
  · cases y with
    | none => exact lt_of_other (some true) htn.1 (by simp)
    | some b => cases b with
      | true => exact lt_of_other none htn.2 (by simp)
      | false => exact lt_of_other (some true) htn.1 (by simp)
  · cases y with
    | none => exact lt_of_other (some false) hfn.1 (by simp)
    | some b => cases b with
      | true => exact lt_of_other (some false) hfn.1 (by simp)
      | false => exact lt_of_other none hfn.2 (by simp)

def scoreFor {C : LiteralRow} (W : List (TableRow C)) (d : Classes C)
    (v : List (TableRow C) → Nat) : Nat :=
  1 + max (max
      (if _h : (replyCell W d (some true)).isEmpty then 0
       else v (replyCell W d (some true)))
      (if _h : (replyCell W d (some false)).isEmpty then 0
       else v (replyCell W d (some false))))
      (if _h : (replyCell W d none).isEmpty then 0
       else v (replyCell W d none))

def scorePairs (C : LiteralRow) (W : List (TableRow C))
    (v : List (TableRow C) → Nat) : List (Classes C × Nat) :=
  (splittingCoordinates C W).map (fun d => (d, scoreFor W d v))

def scoreMinimum (C : LiteralRow) (W : List (TableRow C))
    (v : List (TableRow C) → Nat) : Nat :=
  match List.argmin (fun p : Classes C × Nat => p.2) (scorePairs C W v) with
  | none => 0
  | some p => p.2

def minimaxValueFuel (C : LiteralRow) : Nat → List (TableRow C) → Nat
  | 0, _ => 0
  | n + 1, W =>
      if constantTarget W then 0
      else scoreMinimum C W (minimaxValueFuel C n)

def minimaxValue (C : LiteralRow) (W : List (TableRow C)) : Nat :=
  minimaxValueFuel C W.length W

def minimaxTreeFuel (C : LiteralRow) (fallback : LiteralRow) :
    Nat → List (TableRow C) → RootTree C LiteralRow
  | 0, _ => .stop fallback
  | n + 1, W =>
      if constantTarget W then
        match W with
        | [] => .stop fallback
        | row :: _ => .stop row.target
      else
        match List.argmin (fun p : Classes C × Nat => p.2)
            (scorePairs C W (minimaxValueFuel C n)) with
        | none => .stop fallback
        | some p => .ask p.1
            (minimaxTreeFuel C fallback n (replyCell W p.1 (some true)))
            (minimaxTreeFuel C fallback n (replyCell W p.1 (some false)))
            (minimaxTreeFuel C fallback n (replyCell W p.1 none))

def minimaxTree (C : LiteralRow) (fallback : LiteralRow)
    (W : List (TableRow C)) : RootTree C LiteralRow :=
  minimaxTreeFuel C fallback W.length W

private theorem minimaxValueFuel_constant {C : LiteralRow}
    (W : List (TableRow C)) (h : constantTarget W = true) :
    ∀ n, minimaxValueFuel C n W = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [minimaxValueFuel, h]

private theorem minimaxValueFuel_stable_len {C : LiteralRow} (m : Nat) :
    ∀ (W : List (TableRow C)) (n : Nat), W.length = m → m ≤ n →
      minimaxValueFuel C n W = minimaxValue C W := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro W n hlen hmn
      cases W with
      | nil =>
          simp at hlen
          subst m
          cases n <;> rfl
      | cons row rows =>
          have hmlen : m = rows.length + 1 := hlen.symm.trans (by simp)
          subst m
          cases n with
          | zero => omega
          | succ n =>
              by_cases hc : constantTarget (row :: rows) = true
              · have hv := minimaxValueFuel_constant (row :: rows) hc
                simp [minimaxValueFuel, minimaxValue, hc, hv]
              · have hrows : rows.length ≤ n := by omega
                have hscore (k : Nat) (hk : rows.length ≤ k) :
                    scorePairs C (row :: rows) (minimaxValueFuel C k) =
                      scorePairs C (row :: rows) (minimaxValue C) := by
                  apply List.map_congr_left
                  intro d hd
                  have hsplit : splitCoordinate (row :: rows) d = true :=
                    (List.mem_filter.mp hd).2
                  have hcell (y : Option Bool) :
                      (if _h : (replyCell (row :: rows) d y).isEmpty then 0
                       else minimaxValueFuel C k (replyCell (row :: rows) d y)) =
                        (if _h : (replyCell (row :: rows) d y).isEmpty then 0
                         else minimaxValue C (replyCell (row :: rows) d y)) := by
                    by_cases he : replyCell (row :: rows) d y = []
                    · simp [he]
                    · have hlt := replyCell_length_lt_of_split hsplit y he
                      have hle : (replyCell (row :: rows) d y).length ≤ rows.length :=
                        Nat.le_of_lt_succ (by simpa using hlt)
                      have hltm : (replyCell (row :: rows) d y).length < (row :: rows).length :=
                        replyCell_length_lt_of_split hsplit y he
                      have hi := ih _ hltm (replyCell (row :: rows) d y) k rfl
                        (Nat.le_trans hle hk)
                      simp [he, hi]
                  unfold scoreFor
                  rw [hcell (some true), hcell (some false), hcell none]
                have hleft : minimaxValueFuel C (n + 1) (row :: rows) =
                    scoreMinimum C (row :: rows) (minimaxValueFuel C n) := by
                  simp [minimaxValueFuel, hc]
                have hright : minimaxValue C (row :: rows) =
                    scoreMinimum C (row :: rows) (minimaxValue C) := by
                  have hscoreMin (k : Nat) (hk : rows.length ≤ k) :
                      scoreMinimum C (row :: rows) (minimaxValueFuel C k) =
                        scoreMinimum C (row :: rows) (minimaxValue C) := by
                    simp only [scoreMinimum]
                    rw [hscore k hk]
                  unfold minimaxValue
                  simp [minimaxValueFuel, hc]
                  exact hscoreMin rows.length (Nat.le_refl _)
                have hscoreMin (k : Nat) (hk : rows.length ≤ k) :
                    scoreMinimum C (row :: rows) (minimaxValueFuel C k) =
                      scoreMinimum C (row :: rows) (minimaxValue C) := by
                  simp only [scoreMinimum]
                  rw [hscore k hk]
                rw [hleft, hscoreMin n hrows, ← hright]

private theorem minimaxValueFuel_stable {C : LiteralRow}
    (n : Nat) (W : List (TableRow C)) (hW : W.length ≤ n) :
    minimaxValueFuel C n W = minimaxValue C W :=
  minimaxValueFuel_stable_len W.length W n rfl hW

private theorem scorePairs_stable {C : LiteralRow} (W : List (TableRow C)) :
    scorePairs C W (minimaxValueFuel C W.length) = scorePairs C W (minimaxValue C) := by
  classical
  apply List.map_congr_left
  intro d hd
  have hcell (y : Option Bool) :
      (if _h : (replyCell W d y).isEmpty then 0
       else minimaxValueFuel C W.length (replyCell W d y)) =
        (if _h : (replyCell W d y).isEmpty then 0
         else minimaxValue C (replyCell W d y)) := by
    by_cases he : replyCell W d y = []
    · simp [he]
    · have hi := minimaxValueFuel_stable W.length (replyCell W d y)
        (List.length_filter_le _ _)
      simp [he, hi]
  unfold scoreFor
  rw [hcell (some true), hcell (some false), hcell none]

private theorem minimax_recurrence (C : LiteralRow) (W : List (TableRow C)) :
    if constantTarget W = true then minimaxValue C W = 0
    else minimaxValue C W = scoreMinimum C W (minimaxValue C) := by
  by_cases h : constantTarget W = true
  · rw [if_pos h]
    exact minimaxValueFuel_constant W h W.length
  · have hs := minimaxValueFuel_stable (n := W.length + 1) W (Nat.le_succ _)
    have hp := scorePairs_stable W
    rw [if_neg h]
    rw [minimaxValue] at hs ⊢
    simp [minimaxValueFuel, h] at hs
    have hpm : scoreMinimum C W (minimaxValueFuel C W.length) =
        scoreMinimum C W (minimaxValue C) := by
      unfold scoreMinimum
      rw [hp]
    exact hs.symm.trans hpm

private theorem minimax_constant_target (C : LiteralRow) (W : List (TableRow C))
    (h : constantTarget W = true) : minimaxValue C W = 0 := by
  exact minimaxValueFuel_constant W h W.length

private theorem minimaxValueFuel_nil (C : LiteralRow) (n : Nat) :
    minimaxValueFuel C n [] = 0 := by cases n <;> rfl

private theorem scoreFor_fuel {C : LiteralRow} (W : List (TableRow C))
    (d : Classes C) (n : Nat) :
    scoreFor W d (minimaxValueFuel C n) =
      1 + max (max (minimaxValueFuel C n (replyCell W d (some true)))
        (minimaxValueFuel C n (replyCell W d (some false))))
        (minimaxValueFuel C n (replyCell W d none)) := by
  have hc (y : Option Bool) :
      (if _h : (replyCell W d y).isEmpty then 0
       else minimaxValueFuel C n (replyCell W d y)) =
      minimaxValueFuel C n (replyCell W d y) := by
    by_cases he : replyCell W d y = []
    · simp [he, minimaxValueFuel_nil]
    · simp [he]
  unfold scoreFor
  rw [hc (some true), hc (some false), hc none]

private theorem selected_score {C : LiteralRow} {W : List (TableRow C)}
    {v : List (TableRow C) → Nat} {p : Classes C × Nat}
    (hp : List.argmin (fun p : Classes C × Nat => p.2) (scorePairs C W v) = some p) :
    p.1 ∈ splittingCoordinates C W ∧ p.2 = scoreFor W p.1 v := by
  have hm : p ∈ scorePairs C W v := List.argmin_mem (f := fun p : Classes C × Nat => p.2) (by simp [hp])
  obtain ⟨d, hd, heq⟩ := List.mem_map.mp hm
  cases heq
  exact ⟨hd, rfl⟩

private theorem selected_exists {C : LiteralRow} {W : List (TableRow C)}
    (v : List (TableRow C) → Nat) (h : constantTarget W = false) :
    ∃ p, List.argmin (fun p : Classes C × Nat => p.2) (scorePairs C W v) = some p := by
  obtain ⟨d, hd⟩ := splittingCoordinates_nonempty_of_nonconstant h
  have hmem : (d, scoreFor W d v) ∈ scorePairs C W v := List.mem_map.mpr ⟨d, hd, rfl⟩
  cases he : List.argmin (fun p : Classes C × Nat => p.2) (scorePairs C W v) with
  | none =>
      have hn := List.argmin_eq_none.mp he
      rw [hn] at hmem
      simp at hmem
  | some p => exact ⟨p, rfl⟩

private theorem minimax_fuel_attains (C : LiteralRow) (fallback : LiteralRow)
    (n : Nat) (W : List (TableRow C)) (hW : W.length ≤ n) :
    (∀ row ∈ W, (rootRun row.type (minimaxTreeFuel C fallback n W)).1 = row.target) ∧
      rootDepth (minimaxTreeFuel C fallback n W) = minimaxValueFuel C n W := by
  induction n generalizing W with
  | zero =>
      have hw : W = [] := by cases W <;> simp_all
      subst W
      exact ⟨by simp, rfl⟩
  | succ n ih =>
      by_cases hc : constantTarget W = true
      · cases W with
        | nil => exact ⟨by simp, rfl⟩
        | cons row rows =>
            refine ⟨?_, ?_⟩
            · intro x hx
              have ht := (constantTarget_true_iff _).mp hc hx (List.mem_cons_self)
              simpa [minimaxTreeFuel, hc, rootRun] using ht.symm
            · simp [minimaxTreeFuel, minimaxValueFuel, hc, rootDepth]
      · have hcf : constantTarget W = false := by cases hcb : constantTarget W <;> simp_all
        obtain ⟨p,hp⟩ := selected_exists (minimaxValueFuel C n) hcf
        have sel := selected_score hp
        have hs : splitCoordinate W p.1 = true := (List.mem_filter.mp sel.1).2
        have hchild (y : Option Bool) : (replyCell W p.1 y).length ≤ n := by
          by_cases he : replyCell W p.1 y = []
          · simp [he]
          · have hlt := replyCell_length_lt_of_split hs y he
            omega
        have ht := ih (replyCell W p.1 (some true)) (hchild (some true))
        have hf := ih (replyCell W p.1 (some false)) (hchild (some false))
        have hn := ih (replyCell W p.1 none) (hchild none)
        refine ⟨?_, ?_⟩
        · intro x hx
          have hxcell (y : Option Bool) (hy : x.type p.1 = y) :
              x ∈ replyCell W p.1 y := by simp [replyCell, hx, hy]
          simp only [minimaxTreeFuel, if_neg hc, hp, rootRun]
          cases hy : x.type p.1 with
          | none => exact hn.1 x (hxcell none hy)
          | some b => cases b with
            | true => exact ht.1 x (hxcell (some true) hy)
            | false => exact hf.1 x (hxcell (some false) hy)
        · simp only [minimaxTreeFuel, minimaxValueFuel, if_neg hc, hp,
            scoreMinimum, rootDepth, ht.2, hf.2, hn.2]
          rw [sel.2, scoreFor_fuel]
          omega

private theorem minimax_attains (C : LiteralRow) (fallback : LiteralRow)
    (W : List (TableRow C)) :
    (∀ row ∈ W, (rootRun row.type (minimaxTree C fallback W)).1 = row.target) ∧
      rootDepth (minimaxTree C fallback W) = minimaxValue C W :=
  minimax_fuel_attains C fallback W.length W (Nat.le_refl _)

private theorem scoreMinimum_le {C : LiteralRow} {W : List (TableRow C)}
    (v : List (TableRow C) → Nat) (d : Classes C)
    (h : constantTarget W = false) (hd : d ∈ splittingCoordinates C W) :
    scoreMinimum C W v ≤ scoreFor W d v := by
  obtain ⟨p,hp⟩ := selected_exists v h
  have hm : (d, scoreFor W d v) ∈ scorePairs C W v := List.mem_map.mpr ⟨d,hd,rfl⟩
  have ho : p ∈ List.argmin (fun p : Classes C × Nat => p.2) (scorePairs C W v) := by
    simp [hp]
  have hl := List.le_of_mem_argmin hm ho
  simpa [scoreMinimum,hp] using hl

private theorem minimaxValue_nil (C : LiteralRow) :
    minimaxValue C [] = 0 := rfl

private theorem scoreFor_value {C : LiteralRow} (W : List (TableRow C)) (d : Classes C) :
    scoreFor W d (minimaxValue C) =
      1 + max (max (minimaxValue C (replyCell W d (some true)))
        (minimaxValue C (replyCell W d (some false))))
        (minimaxValue C (replyCell W d none)) := by
  have hc (y : Option Bool) :
      (if _h : (replyCell W d y).isEmpty then 0
       else minimaxValue C (replyCell W d y)) = minimaxValue C (replyCell W d y) := by
    by_cases he : replyCell W d y = []
    · simp [he, minimaxValue_nil]
    · simp [he]
  unfold scoreFor
  rw [hc (some true), hc (some false), hc none]

private theorem replyCell_eq_of_nonsplit {C : LiteralRow} {W : List (TableRow C)}
    {a : TableRow C} (ha : a ∈ W) {d : Classes C} (hs : splitCoordinate W d = false) :
    replyCell W d (a.type d) = W := by
  apply List.filter_eq_self.mpr
  intro x hx
  apply decide_eq_true
  by_contra hdiff
  have ht := splitCoordinate_of_replies hx ha hdiff
  exact Bool.noConfusion (ht.symm.trans hs)

/-- The comparison includes arbitrary repetitions and questions constant on the surviving table. -/
private theorem minimax_lower_bound (C : LiteralRow) (W : List (TableRow C))
    (T : RootTree C LiteralRow)
    (correct : ∀ row ∈ W, (rootRun row.type T).1 = row.target) :
    minimaxValue C W ≤ rootDepth T := by
  induction T generalizing W with
  | stop o =>
      have hc : constantTarget W = true := by
        apply (constantTarget_true_iff W).mpr
        intro a ha b hb
        exact (correct a ha).symm.trans (correct b hb)
      rw [minimax_constant_target C W hc]
      exact Nat.zero_le _
  | ask d A B E ihA ihB ihE =>
      by_cases hc : constantTarget W = true
      · rw [minimax_constant_target C W hc]
        exact Nat.zero_le _
      · have hcf : constantTarget W = false := by cases hcb : constantTarget W <;> simp_all
        have ca : ∀ row ∈ replyCell W d (some true), (rootRun row.type A).1 = row.target := by
          intro row hr
          have hr' := List.mem_filter.mp hr
          have he := of_decide_eq_true hr'.2
          simpa [rootRun, he] using correct row hr'.1
        have cb : ∀ row ∈ replyCell W d (some false), (rootRun row.type B).1 = row.target := by
          intro row hr
          have hr' := List.mem_filter.mp hr
          have he := of_decide_eq_true hr'.2
          simpa [rootRun, he] using correct row hr'.1
        have ce : ∀ row ∈ replyCell W d none, (rootRun row.type E).1 = row.target := by
          intro row hr
          have hr' := List.mem_filter.mp hr
          have he := of_decide_eq_true hr'.2
          simpa [rootRun, he] using correct row hr'.1
        have la := ihA _ ca
        have lb := ihB _ cb
        have le := ihE _ ce
        by_cases hs : splitCoordinate W d = true
        · have hd : d ∈ splittingCoordinates C W :=
            List.mem_filter.mpr ⟨menuList_complete C d, hs⟩
          have hv := minimax_recurrence C W
          rw [if_neg hc] at hv
          rw [hv]
          have hl := scoreMinimum_le (minimaxValue C) d hcf hd
          rw [scoreFor_value] at hl
          simp only [rootDepth]
          omega
        · have hsf : splitCoordinate W d = false := by cases hsb : splitCoordinate W d <;> simp_all
          cases W with
          | nil => simp [constantTarget, rowTargets] at hcf
          | cons a rows =>
              have hw := replyCell_eq_of_nonsplit (List.mem_cons_self (a := a) (l := rows)) hsf
              cases hy : a.type d with
              | none =>
                  rw [hy] at hw
                  rw [hw] at le
                  simp only [rootDepth]
                  omega
              | some b => cases b with
                | true =>
                    rw [hy] at hw
                    rw [hw] at la
                    simp only [rootDepth]
                    omega
                | false =>
                    rw [hy] at hw
                    rw [hw] at lb
                    simp only [rootDepth]
                    omega

/-- Exact actual-menu recurrence, with empty reply cells contributing zero. -/
theorem finite_root_minimax (C : LiteralRow) (W : List (TableRow C)) :
    (if constantTarget W = true then minimaxValue C W = 0
     else minimaxValue C W = scoreMinimum C W (minimaxValue C)) ∧
    (∀ fallback, (∀ row ∈ W, (rootRun row.type (minimaxTree C fallback W)).1 = row.target) ∧
      rootDepth (minimaxTree C fallback W) = minimaxValue C W) ∧
    (∀ T, (∀ row ∈ W, (rootRun row.type T).1 = row.target) → minimaxValue C W ≤ rootDepth T) ∧
    (chartList C).length ≤ 3 ^ Fintype.card (Classes C) ∧
    (∀ θ : Chart C, θ ∈ chartList C) ∧
    (∀ θ, computedTarget C θ = target C θ) :=
  ⟨minimax_recurrence C W, (fun fallback => minimax_attains C fallback W),
    minimax_lower_bound C W, chartList_length_bound C,
    chartList_complete C, computedTarget_spec C⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
