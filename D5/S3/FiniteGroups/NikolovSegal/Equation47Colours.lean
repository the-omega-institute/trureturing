/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47Colours
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47Colours
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueLinks

set_option autoImplicit false

/-! Colour accounting for the literal ordered surgeries of Part I pp219-225.
Negative equal-colour runs alone are compressed.  A numerical increasing-block
rank is proved equivalent to the printed subsequence condition tau <= L_n.
-/
namespace NikolovSegal.Equation47Colours
open NikolovSegal.Equation47ValueNormalization List

abbrev Colour (m : ℕ) := Fin m × Bool

def colourBound (m n : ℕ) : List (Fin m) :=
  (List.replicate n (List.ofFn (fun j : Fin m => j))).flatten

/-- Number of fresh increasing blocks needed, given the next allowed colour
in the current block.  Starting at m means there is no initial free block. -/
def ascendingRank {m : ℕ} : ℕ → List (Fin m) → ℕ
  | _, [] => 0
  | k, j::W => (if j.val < k then 1 else 0) + ascendingRank (j.val+1) W

private def finish {m : ℕ} : ℕ → List (Fin m) → ℕ
  | k, [] => k
  | _, j::W => finish (j.val+1) W

private theorem rank_append {m : ℕ} (A B : List (Fin m)) (k : ℕ) :
    ascendingRank k (A++B) = ascendingRank k A + ascendingRank (finish k A) B := by
  induction A generalizing k with
  | nil => simp [ascendingRank,finish]
  | cons j A ih => simp only [List.cons_append,ascendingRank,finish,ih]; omega

private theorem rank_state_mono {m : ℕ} (W : List (Fin m)) {k l : ℕ} (h : k ≤ l) :
    ascendingRank k W ≤ ascendingRank l W := by
  cases W with
  | nil => exact Nat.le_refl _
  | cons j W => simp only [ascendingRank]; split_ifs <;> omega

private theorem rank_state_bound {m : ℕ} (W : List (Fin m)) (k l : ℕ) :
    ascendingRank k W ≤ 1 + ascendingRank l W := by
  cases W with
  | nil => simp [ascendingRank]
  | cons j W => simp only [ascendingRank]; split_ifs <;> omega

private theorem rank_skip {m : ℕ} (W : List (Fin m)) (k : ℕ) (a : Fin m) :
    ascendingRank k W ≤ (if a.val < k then 1 else 0) + ascendingRank (a.val+1) W := by
  by_cases ha : a.val < k
  · simpa only [if_pos ha] using rank_state_bound W k (a.val+1)
  · simpa only [if_neg ha,Nat.zero_add] using
      rank_state_mono W (by omega : k ≤ a.val+1)

private theorem rank_sublist {m : ℕ} {A B : List (Fin m)} (h : A <+ B) (k : ℕ) :
    ascendingRank k A ≤ ascendingRank k B := by
  induction h generalizing k with
  | slnil => exact Nat.le_refl _
  | @cons A B a h ih =>
    exact (ih k).trans (rank_skip B k a)
  | @cons_cons A B a h ih =>
    simpa only [ascendingRank] using Nat.add_le_add_left (ih (a.val+1)) _

private theorem rank_chain_zero {m : ℕ} (W : List (Fin m)) (k : ℕ)
    (hchain : W.Pairwise (fun a b => a < b)) (hstart : ∀ a ∈ W, k ≤ a.val) :
    ascendingRank k W = 0 := by
  induction W generalizing k with
  | nil => rfl
  | cons a W ih =>
    have hs : ¬ a.val < k := Nat.not_lt.mpr (hstart a (by simp))
    rw [ascendingRank,if_neg hs,Nat.zero_add]
    apply ih _ hchain.of_cons
    intro b hb
    have hh := (List.pairwise_cons.mp hchain).1 b hb
    omega

private theorem rank_chain_bound {m : ℕ} (W : List (Fin m)) (k : ℕ)
    (hchain : W.Pairwise (fun a b => a < b)) : ascendingRank k W ≤ 1 := by
  cases W with
  | nil => simp [ascendingRank]
  | cons a W =>
    rw [ascendingRank,rank_chain_zero W (a.val+1) hchain.of_cons (by
      intro b hb
      have hh := (List.pairwise_cons.mp hchain).1 b hb
      omega),Nat.add_zero]
    split_ifs <;> omega

private theorem bound_rank (m n k : ℕ) : ascendingRank k (colourBound m n) ≤ n := by
  induction n generalizing k with
  | zero => simp [colourBound,ascendingRank]
  | succ n ih =>
    rw [colourBound,List.replicate_succ,List.flatten_cons,rank_append]
    have h := rank_chain_bound (List.ofFn (fun j : Fin m => j)) k
      (List.pairwise_ofFn.mpr (fun _ _ h => h))
    have hh := ih (finish k (List.ofFn (fun j : Fin m => j)))
    change _ + ascendingRank _ (colourBound m n) ≤ n+1
    omega

private theorem block_drop (m : ℕ) (j : Fin m) :
    (List.ofFn (fun i : Fin m => i)).drop j.val =
      j :: (List.ofFn (fun i : Fin m => i)).drop (j.val+1) := by
  rw [List.drop_eq_getElem_cons (by simpa using j.isLt)]
  simp

private theorem rank_embeds {m : ℕ} (W : List (Fin m)) (k n : ℕ)
    (h : ascendingRank k W ≤ n) :
    W <+ (List.ofFn (fun j : Fin m => j)).drop k ++ colourBound m n := by
  induction W generalizing k n with
  | nil => exact List.nil_sublist _
  | cons j W ih =>
    simp only [ascendingRank] at h
    by_cases hj : j.val < k
    · have hn : 0 < n := by rw [if_pos hj] at h; omega
      have ht : ascendingRank (j.val+1) W ≤ n-1 := by rw [if_pos hj] at h; omega
      have htail := ih (j.val+1) (n-1) ht
      have hcons := List.Sublist.cons_cons j htail
      rw [← List.cons_append,← block_drop m j] at hcons
      have hB : (List.ofFn (fun i : Fin m => i)).drop j.val <+
          List.ofFn (fun i : Fin m => i) := List.drop_sublist _ _
      have hs := hcons.trans (hB.append (List.Sublist.refl _))
      have heq : colourBound m n = List.ofFn (fun i : Fin m => i) ++ colourBound m (n-1) := by
        nth_rw 1 [show n = (n-1)+1 by omega]
        simp only [colourBound,List.replicate_succ,List.flatten_cons]
      rw [← heq] at hs
      exact hs.trans (List.sublist_append_right _ _)
    · have ht : ascendingRank (j.val+1) W ≤ n := by rw [if_neg hj,Nat.zero_add] at h; exact h
      have htail := ih (j.val+1) n ht
      have hcons := List.Sublist.cons_cons j htail
      rw [← List.cons_append,← block_drop m j] at hcons
      have hB : (List.ofFn (fun i : Fin m => i)).drop j.val <+
          (List.ofFn (fun i : Fin m => i)).drop k := by
        exact List.drop_sublist_drop_left _ (by omega)
      exact hcons.trans (hB.append (List.Sublist.refl _))

/-- Exact numerical characterization of the printed L_n subsequence bound. -/
theorem ascendingRank_iff {m n : ℕ} (W : List (Fin m)) :
    ascendingRank m W ≤ n ↔ W <+ colourBound m n := by
  constructor
  · intro h
    have hdrop : (List.ofFn (fun j : Fin m => j)).drop m = [] := by
      apply List.drop_eq_nil_iff.mpr
      simp
    simpa only [hdrop,List.nil_append] using rank_embeds W m n h
  · intro h
    exact (rank_sublist h m).trans (bound_rank m n m)

/-- A new increasing block is needed unless colours increase or both
letters belong to one equal negative run. -/
def cost {m : ℕ} (a b : Colour m) : ℕ :=
  if a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 = true ∧ b.2 = true) then 0 else 1

private theorem cost_le_one {m : ℕ} (a b : Colour m) : cost a b ≤ 1 := by
  unfold cost; split_ifs <;> omega

private theorem opposite_connection {m : ℕ} (a b : Colour m) (i : Fin m) (s : Bool) :
    cost a b ≤ cost a (i,s) + cost (i,!s) b := by
  rcases a with ⟨a,sa⟩
  rcases b with ⟨b,sb⟩
  cases s <;> cases sa <;> cases sb <;>
    simp only [cost,Prod.fst,Prod.snd,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,true_and,and_true,false_and,and_false,or_false] <;>
    split_ifs <;> (try simp_all only [not_or,not_and]) <;> omega

private def signedRankFrom {m : ℕ} : Option (Colour m) → List (Colour m) → ℕ
  | _, [] => 0
  | p, b::W => (match p with | none => 1 | some a => cost a b) +
      signedRankFrom (some b) W

def signedRank {m : ℕ} (W : List (Colour m)) : ℕ := signedRankFrom none W

private def threshold {m : ℕ} : Option (Colour m) → ℕ
  | none => m
  | some a => a.1.val+1

private def negativeState {m : ℕ} : Option (Colour m) → Option (Fin m)
  | none => none
  | some a => if a.2 then some a.1 else none

private theorem rankFrom_colour {m : ℕ} (W : List (Colour m)) (p : Option (Colour m)) :
    signedRankFrom p W = ascendingRank (threshold p) (colourTypeFrom (negativeState p) W) := by
  induction W generalizing p with
  | nil => rfl
  | cons b W ih =>
    rcases b with ⟨b,sb⟩
    cases p with
    | none =>
      cases sb <;>
        simp [signedRankFrom,threshold,negativeState,colourTypeFrom,ascendingRank,ih,b.isLt]
    | some a =>
      rcases a with ⟨a,sa⟩
      by_cases hab : a = b
      all_goals cases sa <;> cases sb <;>
        simp only [hab,signedRankFrom,threshold,negativeState,colourTypeFrom,ascendingRank,ih,
          Bool.false_eq_true,Bool.true_eq_false,Bool.false_and,Bool.true_and,↓reduceIte,
          decide_eq_true_eq,Option.some.injEq,Option.noConfusion,Prod.fst,Prod.snd,cost,
          false_and,and_false,true_and,and_true,or_false] <;>
        split_ifs <;> (try subst b) <;> (try simp only [ascendingRank]) <;>
        (try split_ifs) <;> (try simp_all only [not_or,not_and]) <;> (try subst a) <;> first | omega | simp_all

/-- Numerical rank equals the rank of the literal compressed colour type. -/
theorem signedRank_colourType {m : ℕ} (W : List (Colour m)) :
    signedRank W = ascendingRank m (colourType W) := rankFrom_colour W none

theorem signedRank_iff {m n : ℕ} (W : List (Colour m)) :
    signedRank W ≤ n ↔ colourType W <+ colourBound m n := by
  rw [signedRank_colourType,ascendingRank_iff]

private def lastState {m : ℕ} : Option (Colour m) → List (Colour m) → Option (Colour m)
  | p, [] => p
  | _, b::W => lastState (some b) W

private theorem from_append {m : ℕ} (A B : List (Colour m)) (p : Option (Colour m)) :
    signedRankFrom p (A++B) = signedRankFrom p A + signedRankFrom (lastState p A) B := by
  induction A generalizing p with
  | nil => simp [signedRankFrom,lastState]
  | cons a A ih => simp only [List.cons_append,signedRankFrom,lastState,ih]; omega

private theorem lastState_eq {m : ℕ} (W : List (Colour m)) (p : Option (Colour m)) :
    lastState p W = W.getLast?.or p := by
  induction W generalizing p with
  | nil => rfl
  | cons a W ih =>
    cases W with
    | nil => rfl
    | cons b W => simpa [lastState,List.getLast?_cons] using ih (some a)

private def bridge {m : ℕ} : Option (Colour m) → Option (Colour m) → ℤ
  | some a, some b => (cost a b : ℤ)-1
  | _, _ => 0

private theorem from_bridge {m : ℕ} (W : List (Colour m)) (p : Option (Colour m)) :
    (signedRankFrom p W : ℤ) = signedRank W + bridge p W.head? := by
  cases W with
  | nil => cases p <;> rfl
  | cons b W => cases p <;> simp [signedRankFrom,signedRank,bridge] <;> omega

private theorem signedRank_append {m : ℕ} (A B : List (Colour m)) :
    (signedRank (A++B) : ℤ) = signedRank A + signedRank B + bridge A.getLast? B.head? := by
  change (signedRankFrom none (A++B) : ℤ) = _
  rw [from_append,Nat.cast_add,lastState_eq,Option.or_none]
  simp only [from_bridge]
  have hz : bridge (none : Option (Colour m)) A.head? = 0 := by cases A.head? <;> rfl
  rw [hz]
  omega


@[simp] private theorem signedRank_nil {m : ℕ} : signedRank ([] : List (Colour m)) = 0 := rfl
@[simp] private theorem signedRank_singleton {m : ℕ} (a : Colour m) : signedRank [a] = 1 := rfl

/-- Literal DC linked surgery.  The weights of both already-contracted
subtrees add; no untouched-equation or growing-root assumption is needed. -/
theorem signedRank_link {m : ℕ} (A B C D : List (Colour m)) (i : Fin m) (s : Bool) :
    signedRank (A++D++C++B) ≤
      signedRank (A++[(i,s)]++B) + signedRank (C++[(i,!s)]++D) := by
  have hAA := opposite_connection (A.getLast?.getD (i,s)) (A.head?.getD (i,s)) i s
  have kAA := opposite_connection (A.getLast?.getD (i,s)) (A.head?.getD (i,s)) i (!s)
  have cAA := cost_le_one (A.getLast?.getD (i,s)) (A.head?.getD (i,s))
  have hAB := opposite_connection (A.getLast?.getD (i,s)) (B.head?.getD (i,s)) i s
  have kAB := opposite_connection (A.getLast?.getD (i,s)) (B.head?.getD (i,s)) i (!s)
  have cAB := cost_le_one (A.getLast?.getD (i,s)) (B.head?.getD (i,s))
  have hAC := opposite_connection (A.getLast?.getD (i,s)) (C.head?.getD (i,s)) i s
  have kAC := opposite_connection (A.getLast?.getD (i,s)) (C.head?.getD (i,s)) i (!s)
  have cAC := cost_le_one (A.getLast?.getD (i,s)) (C.head?.getD (i,s))
  have hAD := opposite_connection (A.getLast?.getD (i,s)) (D.head?.getD (i,s)) i s
  have kAD := opposite_connection (A.getLast?.getD (i,s)) (D.head?.getD (i,s)) i (!s)
  have cAD := cost_le_one (A.getLast?.getD (i,s)) (D.head?.getD (i,s))
  have hBA := opposite_connection (B.getLast?.getD (i,s)) (A.head?.getD (i,s)) i s
  have kBA := opposite_connection (B.getLast?.getD (i,s)) (A.head?.getD (i,s)) i (!s)
  have cBA := cost_le_one (B.getLast?.getD (i,s)) (A.head?.getD (i,s))
  have hBB := opposite_connection (B.getLast?.getD (i,s)) (B.head?.getD (i,s)) i s
  have kBB := opposite_connection (B.getLast?.getD (i,s)) (B.head?.getD (i,s)) i (!s)
  have cBB := cost_le_one (B.getLast?.getD (i,s)) (B.head?.getD (i,s))
  have hBC := opposite_connection (B.getLast?.getD (i,s)) (C.head?.getD (i,s)) i s
  have kBC := opposite_connection (B.getLast?.getD (i,s)) (C.head?.getD (i,s)) i (!s)
  have cBC := cost_le_one (B.getLast?.getD (i,s)) (C.head?.getD (i,s))
  have hBD := opposite_connection (B.getLast?.getD (i,s)) (D.head?.getD (i,s)) i s
  have kBD := opposite_connection (B.getLast?.getD (i,s)) (D.head?.getD (i,s)) i (!s)
  have cBD := cost_le_one (B.getLast?.getD (i,s)) (D.head?.getD (i,s))
  have hCA := opposite_connection (C.getLast?.getD (i,s)) (A.head?.getD (i,s)) i s
  have kCA := opposite_connection (C.getLast?.getD (i,s)) (A.head?.getD (i,s)) i (!s)
  have cCA := cost_le_one (C.getLast?.getD (i,s)) (A.head?.getD (i,s))
  have hCB := opposite_connection (C.getLast?.getD (i,s)) (B.head?.getD (i,s)) i s
  have kCB := opposite_connection (C.getLast?.getD (i,s)) (B.head?.getD (i,s)) i (!s)
  have cCB := cost_le_one (C.getLast?.getD (i,s)) (B.head?.getD (i,s))
  have hCC := opposite_connection (C.getLast?.getD (i,s)) (C.head?.getD (i,s)) i s
  have kCC := opposite_connection (C.getLast?.getD (i,s)) (C.head?.getD (i,s)) i (!s)
  have cCC := cost_le_one (C.getLast?.getD (i,s)) (C.head?.getD (i,s))
  have hCD := opposite_connection (C.getLast?.getD (i,s)) (D.head?.getD (i,s)) i s
  have kCD := opposite_connection (C.getLast?.getD (i,s)) (D.head?.getD (i,s)) i (!s)
  have cCD := cost_le_one (C.getLast?.getD (i,s)) (D.head?.getD (i,s))
  have hDA := opposite_connection (D.getLast?.getD (i,s)) (A.head?.getD (i,s)) i s
  have kDA := opposite_connection (D.getLast?.getD (i,s)) (A.head?.getD (i,s)) i (!s)
  have cDA := cost_le_one (D.getLast?.getD (i,s)) (A.head?.getD (i,s))
  have hDB := opposite_connection (D.getLast?.getD (i,s)) (B.head?.getD (i,s)) i s
  have kDB := opposite_connection (D.getLast?.getD (i,s)) (B.head?.getD (i,s)) i (!s)
  have cDB := cost_le_one (D.getLast?.getD (i,s)) (B.head?.getD (i,s))
  have hDC := opposite_connection (D.getLast?.getD (i,s)) (C.head?.getD (i,s)) i s
  have kDC := opposite_connection (D.getLast?.getD (i,s)) (C.head?.getD (i,s)) i (!s)
  have cDC := cost_le_one (D.getLast?.getD (i,s)) (C.head?.getD (i,s))
  have hDD := opposite_connection (D.getLast?.getD (i,s)) (D.head?.getD (i,s)) i s
  have kDD := opposite_connection (D.getLast?.getD (i,s)) (D.head?.getD (i,s)) i (!s)
  have cDD := cost_le_one (D.getLast?.getD (i,s)) (D.head?.getD (i,s))
  have hz := (show (signedRank (A++D++C++B) : ℤ) ≤
      signedRank (A++[(i,s)]++B) + signedRank (C++[(i,!s)]++D) from by
    cases A <;> cases B <;> cases C <;> cases D <;>
      simp_all only [signedRank_append,signedRank_nil,signedRank_singleton,
        List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
        List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
        Option.or_none,Option.getD_some,Option.getD_none,bridge,
        Nat.cast_zero,Nat.cast_one,Bool.not_not] <;> omega)
  exact_mod_cast hz


/-- Opposite occurrences always consume one increasing-block break. -/
private theorem opposite_cost {m : ℕ} (i : Fin m) (s : Bool) :
    cost (i,s) (i,!s) = 1 := by cases s <;> simp [cost]

/-- The cancellation step used in Lemma8.3 decreases colour rank by at
least one, including joins of equal negative runs. -/
theorem signedRank_cancel {m : ℕ} (A B : List (Colour m)) (i : Fin m) (s : Bool) :
    signedRank (A++B)+1 ≤ signedRank (A++[(i,s),(i,!s)]++B) := by
  have h := opposite_connection (A.getLast?.getD (i,s)) (B.head?.getD (i,s)) i s
  have hz : (signedRank (A++B) : ℤ)+1 ≤ signedRank (A++[(i,s),(i,!s)]++B) := by
    have hp : [(i,s),(i,!s)] = [(i,s)]++[(i,!s)] := rfl
    rw [hp]
    cases A <;> cases B <;>
      simp_all only [signedRank_append,signedRank_nil,signedRank_singleton,
        List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
        List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
        Option.or_none,Option.getD_some,Option.getD_none,bridge,
        Nat.cast_zero,Nat.cast_one,opposite_cost] <;> omega
  exact_mod_cast hz

/-- The exact ADCBE surgery of Proposition8.2 preserves colour rank.
For each newly joined pair of retained chunks, follow its original boundary
arcs and jump from each crossing occurrence to its opposite.  The paths
use disjoint original boundary arcs, so their costs add without commutation. -/
theorem signedRank_crossing {m : ℕ} (A B C D E : List (Colour m))
    (i j : Fin m) (sx sy : Bool) :
    signedRank (A++D++C++B++E) ≤
      signedRank (A++[(i,!sx)]++B++[(j,!sy)]++C++[(i,sx)]++D++[(j,sy)]++E) := by
  have hz : (signedRank (A++D++C++B++E) : ℤ) ≤
      signedRank (A++[(i,!sx)]++B++[(j,!sy)]++C++[(i,sx)]++D++[(j,sy)]++E) := by
    cases A with
    | nil =>
      cases B with
      | nil =>
        cases C with
        | nil =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (D.getLast?.getD d) e j sy
              have h1 := opposite_connection ((j,(!sy))) e i sx
              have h2 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
        | cons c C =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (C.getLast?.getD c) e i sx
              have h1 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (D.getLast?.getD d) c j sy
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (D.getLast?.getD d) c j sy
              have h1 := opposite_connection (C.getLast?.getD c) e i sx
              have h2 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
      | cons b B =>
        cases C with
        | nil =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (D.getLast?.getD d) b j sy
              have h1 := opposite_connection ((j,(!sy))) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (D.getLast?.getD d) b j sy
              have h1 := opposite_connection ((j,(!sy))) b i sx
              have h2 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
        | cons c C =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              have h0 := opposite_connection (C.getLast?.getD c) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (C.getLast?.getD c) b i sx
              have h1 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (D.getLast?.getD d) c j sy
              have h1 := opposite_connection (C.getLast?.getD c) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (D.getLast?.getD d) c j sy
              have h1 := opposite_connection (C.getLast?.getD c) b i sx
              have h2 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
    | cons a A =>
      cases B with
      | nil =>
        cases C with
        | nil =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) e i (!sx)
              have h1 := opposite_connection ((i,sx)) e j sy
              have h2 := opposite_connection ((j,(!sy))) e i sx
              have h3 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) e j sy
              have h2 := opposite_connection ((j,(!sy))) e i sx
              have h3 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
        | cons c C =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) c i (!sx)
              have h1 := opposite_connection ((i,sx)) c j sy
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) c i (!sx)
              have h1 := opposite_connection ((i,sx)) c j sy
              have h2 := opposite_connection (C.getLast?.getD c) e i sx
              have h3 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) c j sy
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) c j sy
              have h2 := opposite_connection (C.getLast?.getD c) e i sx
              have h3 := opposite_connection ((i,(!sx))) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
      | cons b B =>
        cases C with
        | nil =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) b i (!sx)
              have h1 := opposite_connection ((i,sx)) b j sy
              have h2 := opposite_connection ((j,(!sy))) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) b i (!sx)
              have h1 := opposite_connection ((i,sx)) b j sy
              have h2 := opposite_connection ((j,(!sy))) b i sx
              have h3 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) b j sy
              have h2 := opposite_connection ((j,(!sy))) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) b j sy
              have h2 := opposite_connection ((j,(!sy))) b i sx
              have h3 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
        | cons c C =>
          cases D with
          | nil =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) c i (!sx)
              have h1 := opposite_connection ((i,sx)) c j sy
              have h2 := opposite_connection (C.getLast?.getD c) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) c i (!sx)
              have h1 := opposite_connection ((i,sx)) c j sy
              have h2 := opposite_connection (C.getLast?.getD c) b i sx
              have h3 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
          | cons d D =>
            cases E with
            | nil =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) c j sy
              have h2 := opposite_connection (C.getLast?.getD c) b i sx
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
            | cons e E =>
              have h0 := opposite_connection (A.getLast?.getD a) d i (!sx)
              have h1 := opposite_connection (D.getLast?.getD d) c j sy
              have h2 := opposite_connection (C.getLast?.getD c) b i sx
              have h3 := opposite_connection (B.getLast?.getD b) e j (!sy)
              simp only [signedRank_append,signedRank_nil,signedRank_singleton,
                List.head?_append,List.getLast?_append,List.head?_nil,List.head?_cons,
                List.getLast?_nil,List.getLast?_cons,Option.none_or,Option.some_or,
                Option.or_none,Option.getD_none,Option.getD_some,Bool.not_not,
                bridge,Nat.cast_zero,Nat.cast_one] at *
              omega
  exact_mod_cast hz

end NikolovSegal.Equation47Colours
