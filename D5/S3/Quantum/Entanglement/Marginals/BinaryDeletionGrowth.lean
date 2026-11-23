/- GID: D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Four-site windows give an exact kernel-dimension recurrence and exponential lower bounds. -/

import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth

namespace FourWindowGrowth

inductive AgePair
  | age01 | age02 | age03 | age12 | age13 | age23
  deriving DecidableEq

open AgePair

def successors : AgePair → List AgePair
  | age01 => [age02, age01, age12]
  | age02 => [age03, age01, age13]
  | age03 => [age01]
  | age12 => [age03, age02, age23]
  | age13 => [age02]
  | age23 => [age03]

def weight : AgePair → ℚ
  | age01 => 100
  | age02 => 75
  | age03 => 43
  | age12 => 58
  | age13 => 32
  | age23 => 18

def extensions : ℕ → AgePair → ℚ
  | 0, _ => 1
  | k + 1, state => ((successors state).map (extensions k)).sum

private theorem weight_le_sum (state : AgePair) :
    (100 / 43 : ℚ) * weight state ≤ ((successors state).map weight).sum := by
  cases state <;> norm_num [weight, successors, extensions, List.sum_cons]

private theorem weighted_lower (k : ℕ) (state : AgePair) :
    (100 / 43 : ℚ) ^ k * weight state ≤ 100 * extensions k state := by
  induction k generalizing state with
  | zero => cases state <;> norm_num [weight, successors, extensions, List.sum_cons]
  | succ k ih =>
    have h := mul_le_mul_of_nonneg_left (weight_le_sum state)
      (pow_nonneg (by norm_num : (0 : ℚ) ≤ 100 / 43) k)
    rw [pow_succ, mul_assoc]
    refine h.trans ?_
    change (100 / 43 : ℚ) ^ k * ((successors state).map weight).sum ≤
      100 * ((successors state).map (extensions k)).sum
    have addBounds (l : List AgePair) :
        (100 / 43 : ℚ) ^ k * (l.map weight).sum ≤ 100 * (l.map (extensions k)).sum := by
      induction l with
      | nil => simp
      | cons a l ihl =>
        simp only [List.map_cons, List.sum_cons, mul_add]
        exact add_le_add (ih a) ihl
    exact addBounds (successors state)

private theorem lower_from_opposite_pair (k : ℕ) :
    (100 / 43 : ℚ) ^ k ≤ extensions k age01 := by
  have h := weighted_lower k age01
  norm_num [weight] at h
  linarith


abbrev Letter := Option Bool

def ages : AgePair → Nat × Nat
  | age01 => (0,1)
  | age02 => (0,2)
  | age03 => (0,3)
  | age12 => (1,2)
  | age13 => (1,3)
  | age23 => (2,3)

def repeatRecent : AgePair → Option AgePair
  | age01 => some age02
  | age02 | age12 => some age03
  | _ => none

def emitOlder : AgePair → AgePair
  | age01 | age02 | age03 => age01
  | age12 | age13 => age02
  | age23 => age03

def agree : AgePair → Option AgePair
  | age01 => some age12
  | age02 => some age13
  | age12 => some age23
  | _ => none

def translate (recent : Bool) (move : Letter) : Letter :=
  move.map fun m => if m then !recent else recent

def nextState (s : AgePair) (move : Letter) : Option AgePair :=
  match move with
  | none => agree s
  | some false => repeatRecent s
  | some true => some (emitOlder s)

def nextOrientation (recent : Bool) (move : Letter) : Bool :=
  if move = some true then !recent else recent

def represents (s : AgePair) (recent : Bool) (history : List Letter) : Prop :=
  some recent ∈ history ∧ some (!recent) ∈ history ∧
  history.idxOf (some recent) = (ages s).1 ∧
  history.idxOf (some (!recent)) = (ages s).2

private theorem newest_window (s : AgePair) (recent : Bool) (history : List Letter)
    (h : represents s recent history) :
    ∀ b : Bool, some b ∈ history.take 4 := by
  obtain ⟨hr, ho, hra, hoa⟩ := h
  have a : (ages s).1 < 4 := by cases s <;> decide
  have b : (ages s).2 < 4 := by cases s <;> decide
  intro bit
  cases recent <;> cases bit
  all_goals
    first
    | exact (List.mem_take_iff_idxOf_lt hr).mpr (hra ▸ a)
    | exact (List.mem_take_iff_idxOf_lt ho).mpr (hoa ▸ b)

private theorem represents_step (s t : AgePair) (recent : Bool) (history : List Letter)
    (move : Letter) (h : represents s recent history) (step : nextState s move = some t) :
    represents t (nextOrientation recent move) (translate recent move :: history) := by
  obtain ⟨hr, ho, ha, hb⟩ := h
  cases move with
  | none =>
    cases s <;> simp [nextState, agree] at step
    all_goals
      subst t
      exact ⟨List.mem_cons_of_mem _ hr, List.mem_cons_of_mem _ ho,
        by simp [translate, nextOrientation, ages, ha],
        by simp [translate, nextOrientation, ages, hb]⟩
  | some move =>
    cases move
    · cases s <;> simp [nextState, repeatRecent] at step
      all_goals
        subst t
        cases recent <;>
          simp_all [represents, translate, nextOrientation, ages]
    · cases s <;> simp [nextState, emitOlder] at step
      all_goals
        subst t
        cases recent <;>
          simp_all [represents, translate, nextOrientation, ages]


/-- Short suffixes need no condition until four letters are present. -/
def validWindows : List Letter → Prop
  | [] => True
  | m :: rest =>
    (4 ≤ (m :: rest).length → ∀ bit : Bool, some bit ∈ (m :: rest).take 4) ∧
      validWindows rest

def runWord (recent : Bool) : List Letter → List Letter
  | [] => []
  | m :: rest => translate recent m :: runWord (nextOrientation recent m) rest

def follows (s : AgePair) : List Letter → Prop
  | [] => True
  | m :: rest => ∃ t, nextState s m = some t ∧ follows t rest

private theorem valid_after_run (moves : List Letter) {s : AgePair} {recent : Bool}
    {history : List Letter} (h : represents s recent history) (hvalid : validWindows history)
    (run : follows s moves) :
    validWindows ((runWord recent moves).reverse ++ history) := by
  induction moves generalizing s recent history with
  | nil => simpa [runWord] using hvalid
  | cons move moves ih =>
    rcases run with ⟨t, step, tail⟩
    have next := represents_step s t recent history move h step
    have valid : validWindows (translate recent move :: history) :=
      ⟨fun _ => newest_window t (nextOrientation recent move) _ next, hvalid⟩
    simpa only [runWord, List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih next valid tail

private theorem translate_inj (recent : Bool) : Function.Injective (translate recent) := by
  intro x y h
  cases recent <;> cases x <;> cases y <;> simp [translate] at h ⊢
  all_goals
    rename_i a b
    cases a <;> cases b <;> simp_all

private theorem runWord_inj (recent : Bool) : Function.Injective (runWord recent) := by
  intro u
  induction u generalizing recent with
  | nil => intro v h; cases v <;> simp_all [runWord]
  | cons m rest ih =>
    intro v h
    cases v with
    | nil => simp [runWord] at h
    | cons n tail =>
      simp only [runWord, List.cons.injEq] at h
      obtain rfl := translate_inj recent h.1
      exact congrArg (List.cons m) (ih (nextOrientation recent m) h.2)


open scoped BigOperators Classical

private def legalMoves (s : AgePair) : {k : ℕ} → (Fin k → Letter) → Prop
  | 0, _ => True
  | _ + 1, w =>
    match nextState s (w 0) with
    | none => False
    | some t => legalMoves t (Fin.tail w)

private abbrev Available (s : AgePair) := {m : Letter // (nextState s m).isSome}

private def target (s : AgePair) (m : Available s) : AgePair :=
  (nextState s m.1).get m.2

private theorem next_eq_some_target (s : AgePair) (m : Available s) :
    nextState s m.1 = some (target s m) := by
  unfold target
  exact (Option.some_get m.2).symm

private def splitMoves (s : AgePair) (k : ℕ) :
    {w : Fin (k + 1) → Letter // legalMoves s w} ≃
      Σ m : Available s, {w : Fin k → Letter // legalMoves (target s m) w} where
  toFun w := by
    have accepted : (nextState s (w.1 0)).isSome := by
      have h := w.2
      unfold legalMoves at h
      split at h <;> simp_all
    let m : Available s := ⟨w.1 0, accepted⟩
    exact ⟨m, Fin.tail w.1, by
      have hm : nextState s (w.1 0) = some (target s m) := next_eq_some_target s m
      simpa [legalMoves, hm] using w.2⟩
  invFun := fun ⟨m, w⟩ => ⟨Fin.cons m.1 w.1, by
    simpa [legalMoves, next_eq_some_target s m] using w.2⟩
  left_inv w := Subtype.ext (Fin.cons_self_tail w.1)
  right_inv := by
    rintro ⟨m, w⟩
    simp
    cases w
    rfl

private theorem transition_sum (s : AgePair) (f : AgePair → ℚ) :
    (∑ m : Available s, f (target s m)) = ((successors s).map f).sum := by
  let contribution (m : Letter) : ℚ := (nextState s m).elim 0 f
  have hfilter (m : Letter) :
      m ∈ Finset.univ.filter (fun m => (nextState s m).isSome) ↔
      (nextState s m).isSome := by simp
  calc
    (∑ m : Available s, f (target s m)) = ∑ m : Available s, contribution m.1 := by
      apply Finset.sum_congr rfl
      intro m _
      simp [contribution, next_eq_some_target s m]
    _ = ∑ m ∈ Finset.univ.filter (fun m => (nextState s m).isSome), contribution m :=
      (Finset.sum_subtype _ hfilter contribution).symm
    _ = ((successors s).map f).sum := by
      rw [Finset.sum_filter, Fintype.sum_option, Fintype.sum_bool]
      cases s <;> simp [contribution, nextState, repeatRecent, emitOlder, agree, successors,
        add_comm, add_left_comm]

private theorem card_legalMoves (s : AgePair) (k : ℕ) :
    (Fintype.card {w : Fin k → Letter // legalMoves s w} : ℚ) = extensions k s := by
  induction k generalizing s with
  | zero =>
    have : Unique {w : Fin 0 → Letter // legalMoves s w} :=
      ⟨⟨⟨Fin.elim0, trivial⟩⟩, fun w => Subtype.ext (funext fun i => i.elim0)⟩
    simp [extensions]
  | succ k ih =>
    rw [Fintype.card_congr (splitMoves s k), Fintype.card_sigma, Nat.cast_sum]
    simp_rw [ih]
    exact transition_sum s (extensions k)


private theorem follows_of_legalMoves {k : ℕ} (s : AgePair) (w : Fin k → Letter)
    (h : legalMoves s w) : follows s (List.ofFn w) := by
  induction k generalizing s with
  | zero => simp [follows]
  | succ k ih =>
    rw [List.ofFn_succ]
    cases step : nextState s (w 0) with
    | none => simp [legalMoves, step] at h
    | some t =>
      have ht : legalMoves t (Fin.tail w) := by simpa [legalMoves, step] using h
      exact ⟨t, step, ih t (Fin.tail w) ht⟩

private theorem runWord_length (recent : Bool) (moves : List Letter) :
    (runWord recent moves).length = moves.length := by
  induction moves generalizing recent with
  | nil => rfl
  | cons m rest ih => simp [runWord, ih]

private def encoded {k : ℕ} (w : Fin k → Letter) : List Letter :=
  (runWord true (List.ofFn w)).reverse ++ [some true, some false]

private theorem encoded_length {k : ℕ} (w : Fin k → Letter) :
    (encoded w).length = k + 2 := by
  simp [encoded, runWord_length]

private theorem encoded_valid {k : ℕ} (w : Fin k → Letter) (h : legalMoves age01 w) :
    validWindows (encoded w) := by
  apply valid_after_run (s := age01) (recent := true)
  · simp [represents, ages]
  · simp [validWindows]
  · exact follows_of_legalMoves age01 w h

private theorem encoded_inj {k : ℕ} : Function.Injective (encoded (k := k)) := by
  intro w z h
  unfold encoded at h
  exact List.ofFn_injective (runWord_inj true (List.reverse_inj.mp (List.append_cancel_right h)))

private def listWord {k : ℕ} {l : List Letter} (h : l.length = k) (i : Fin k) : Letter :=
  l.get (Fin.cast h.symm i)

private theorem ofFn_listWord {k : ℕ} {l : List Letter} (h : l.length = k) :
    List.ofFn (listWord h) = l := by
  subst k
  exact List.ofFn_get l

private theorem validPatterns_lower (k : ℕ) :
    (100 / 43 : ℚ) ^ k ≤
      (Fintype.card {w : Fin (k + 2) → Letter // validWindows (List.ofFn w)} : ℚ) := by
  let embed (w : {w : Fin k → Letter // legalMoves age01 w}) :
      {w : Fin (k + 2) → Letter // validWindows (List.ofFn w)} :=
    ⟨listWord (encoded_length w.1), by rw [ofFn_listWord]; exact encoded_valid w.1 w.2⟩
  have inj : Function.Injective embed := by
    intro w z h
    apply Subtype.ext
    apply encoded_inj
    have hl := congrArg (fun x => List.ofFn x.1) h
    simpa only [embed, ofFn_listWord] using hl
  have cardle := Fintype.card_le_of_injective embed inj
  refine (lower_from_opposite_pair k).trans ?_
  rw [← card_legalMoves]
  exact_mod_cast cardle


private theorem validWindows_at {l : List Letter} (h : validWindows l) (i : ℕ)
    (bound : i + 4 ≤ l.length) (bit : Bool) :
    some bit ∈ (l.drop i).take 4 := by
  induction l generalizing i with
  | nil => simp at bound
  | cons a rest ih =>
    cases i with
    | zero => exact h.1 bound bit
    | succ i => exact ih h.2 i (by simpa using bound)

private theorem all_windows_contain_orientations {n : ℕ} (w : Fin n → Letter)
    (h : validWindows (List.ofFn w)) {i : ℕ} (hi : i + 4 ≤ n) (bit : Bool) :
    ∃ j : Fin n, i ≤ j.val ∧ j.val < i + 4 ∧ w j = some bit := by
  have hmem := validWindows_at h i (by simpa using hi) bit
  obtain ⟨s, hlen, read⟩ := List.mem_iff_getElem.mp hmem
  have hs : s < 4 := by
    rw [List.length_take] at hlen
    exact hlen.trans_le (min_le_left _ _)
  have hindex : i + s < n := by omega
  refine ⟨⟨i + s, hindex⟩, by change i ≤ i + s; omega, by change i + s < i + 4; omega, ?_⟩
  simpa [List.getElem_take, List.getElem_drop, Nat.add_comm] using read

private theorem translate_translate (recent : Bool) (move : Letter) :
    translate recent (translate recent move) = move := by
  cases move with
  | none => rfl
  | some bit => cases recent <;> cases bit <;> rfl

private theorem accepted_from_window (state : AgePair) (recent : Bool) (history : List Letter)
    (move : Letter) (h : represents state recent history)
    (window : ∀ bit : Bool, some bit ∈ (translate recent move :: history).take 4) :
    ∃ t, nextState state move = some t := by
  obtain ⟨hr, ho, hra, hoa⟩ := h
  have indexRecent :=
    (List.mem_take_iff_idxOf_lt (List.mem_cons_of_mem (translate recent move) hr)).mp
      (window recent)
  have indexOlder :=
    (List.mem_take_iff_idxOf_lt (List.mem_cons_of_mem (translate recent move) ho)).mp
      (window (!recent))
  cases state <;> cases recent <;> cases move <;>
    simp_all [nextState, agree, ages, translate, List.idxOf_cons]
  all_goals
    rename_i choice
    cases choice <;> simp_all [repeatRecent, emitOlder]


private def decodeMoves (recent : Bool) : List Letter → List Letter
  | [] => []
  | symbol :: suffix =>
    let move := translate recent symbol
    move :: decodeMoves (nextOrientation recent move) suffix

private theorem run_decode (recent : Bool) (word : List Letter) :
    runWord recent (decodeMoves recent word) = word := by
  induction word generalizing recent with
  | nil => rfl
  | cons s w ih => simp [decodeMoves, runWord, translate_translate, ih]

private theorem validWindows_suffix (preludeWord tail : List Letter)
    (valid : validWindows (preludeWord ++ tail)) : validWindows tail := by
  induction preludeWord with
  | nil => exact valid
  | cons p pre ih => exact ih valid.2

private theorem follows_decode (word : List Letter) {state : AgePair} {recent : Bool}
    {history : List Letter} (h : represents state recent history) (hlen : 4 ≤ history.length)
    (valid : validWindows (word.reverse ++ history)) :
    follows state (decodeMoves recent word) := by
  induction word generalizing state recent history with
  | nil => exact trivial
  | cons symbol tail ih =>
    have newestValid : validWindows (tail.reverse ++ symbol :: history) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid
    have current := validWindows_suffix _ _ newestValid
    have window := current.1 (by simp; omega)
    have echo := translate_translate recent symbol
    let move := translate recent symbol
    obtain ⟨t, ht⟩ := accepted_from_window state recent history move h
      (by simpa only [move, echo] using window)
    have hrep := represents_step state t recent history move h ht
    change represents t (nextOrientation recent move)
      (translate recent (translate recent symbol) :: history) at hrep
    rw [echo] at hrep
    exact ⟨t, ht, ih hrep (by simp; omega) newestValid⟩

private theorem legalMoves_of_follows {k : ℕ} (state : AgePair) (w : Fin k → Letter)
    (run : follows state (List.ofFn w)) : legalMoves state w := by
  induction k generalizing state with
  | zero => exact trivial
  | succ k ih =>
    rw [List.ofFn_succ, follows] at run
    obtain ⟨t, ht, run⟩ := run
    simpa only [legalMoves, ht] using ih t (Fin.tail w) run

private theorem length_decode (recent : Bool) (word : List Letter) :
    (decodeMoves recent word).length = word.length := by
  induction word generalizing recent with
  | nil => rfl
  | cons a w ih => simp [decodeMoves, ih]

private def validExtensionsEquiv (state : AgePair) (recent : Bool) (history : List Letter)
    (h : represents state recent history) (hlen : 4 ≤ history.length)
    (hvalid : validWindows history) (k : ℕ) :
    {w : Fin k → Letter // legalMoves state w} ≃
      {w : Fin k → Letter // validWindows (List.ofFn w ++ history)} where
  toFun w := by
    have len : (runWord recent (List.ofFn w.1)).reverse.length = k := by
      simp [runWord_length]
    refine ⟨listWord len, ?_⟩
    rw [ofFn_listWord]
    exact valid_after_run (List.ofFn w.1) h hvalid (follows_of_legalMoves state w.1 w.2)
  invFun w := by
    have len : (decodeMoves recent (List.ofFn w.1).reverse).length = k := by
      simp [length_decode]
    refine ⟨listWord len, legalMoves_of_follows state _ ?_⟩
    rw [ofFn_listWord]
    exact follows_decode (List.ofFn w.1).reverse h hlen (by simpa only [List.reverse_reverse] using w.2)
  left_inv w := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_listWord, ofFn_listWord, List.reverse_reverse]
    apply runWord_inj recent
    exact run_decode recent _
  right_inv w := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_listWord, ofFn_listWord, run_decode, List.reverse_reverse]

private theorem validWindows_of_at {word : List Letter}
    (h : ∀ i, i + 4 ≤ word.length → ∀ bit : Bool,
      some bit ∈ (word.drop i).take 4) : validWindows word := by
  induction word with
  | nil => exact trivial
  | cons head rest ih =>
    refine ⟨fun bound bit => h 0 bound bit, ih ?_⟩
    intro i hi bit
    have lifted := h (i + 1) (by simp; omega) bit
    simpa only [List.drop_succ_cons] using lifted

private theorem validWindows_ofFn_iff {n : ℕ} (w : Fin n → Letter) :
    validWindows (List.ofFn w) ↔
      ∀ i, i + 4 ≤ n → ∀ bit : Bool,
        ∃ j : Fin n, i ≤ j.val ∧ j.val < i + 4 ∧ w j = some bit := by
  constructor
  · intro h i hi bit
    exact all_windows_contain_orientations w h hi bit
  · intro h
    apply validWindows_of_at
    intro i hi bit
    have hin : i + 4 ≤ n := by simpa using hi
    obtain ⟨j, hj₁, hj₂, read⟩ := h i hin bit
    let k := j.val - i
    have hidx : i + k = j.val := Nat.add_sub_of_le hj₁
    have klt : k < ((List.ofFn w).drop i |>.take 4).length := by
      simp only [List.length_take, List.length_drop, List.length_ofFn, Nat.lt_min]
      omega
    rw [List.mem_iff_getElem]
    refine ⟨k, klt, ?_⟩
    simpa only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, hidx] using read


private abbrev Seed := {w : Fin 4 → Letter // ∀ bit : Bool, some bit ∈ List.ofFn w}

private def seedOrientation (w : Fin 4 → Letter) : Bool :=
  decide ((List.ofFn w).idxOf (some true) < (List.ofFn w).idxOf (some false))

private def seedState (w : Fin 4 → Letter) : AgePair :=
  let history := List.ofFn w
  let t := history.idxOf (some true)
  let f := history.idxOf (some false)
  match (min t f, max t f) with
  | (0, 1) => age01
  | (0, 2) => age02
  | (0, 3) => age03
  | (1, 2) => age12
  | (1, 3) => age13
  | _ => age23

private theorem seed_represents : ∀ w : Seed,
    represents (seedState w.1) (seedOrientation w.1) (List.ofFn w.1) := by
  intro w
  obtain ⟨w, hw⟩ := w
  let target (w : Fin 4 → Letter) :=
    represents (seedState w) (seedOrientation w) (List.ofFn w)
  have h : ∀ w : Fin 4 → Letter, (∀ bit : Bool, some bit ∈ List.ofFn w) → target w := by
    dsimp [target, represents]
    decide
  exact h w hw

private theorem seed_valid (w : Seed) : validWindows (List.ofFn w.1) := by
  rw [validWindows_ofFn_iff]
  intro i hi bit
  have hz : i = 0 := by omega
  subst i
  obtain ⟨j, hj, read⟩ := List.mem_iff_getElem.mp (w.2 bit)
  have hj4 : j < 4 := by simpa using hj
  exact ⟨⟨j, hj4⟩, Nat.zero_le _, hj4, by simpa only [List.getElem_ofFn] using read⟩

private def splitSeeds (k : ℕ) :
    {w : Fin (k + 4) → Letter // validWindows (List.ofFn w)} ≃
      Σ seed : Seed,
        {w : Fin k → Letter // validWindows (List.ofFn w ++ List.ofFn seed.1)} where
  toFun w := by
    let left i := w.1 (Fin.castAdd 4 i)
    let right i := w.1 (Fin.natAdd k i)
    have full : List.ofFn w.1 = List.ofFn left ++ List.ofFn right := by
      rw [List.ofFn_add]
      rfl
    have ok : validWindows (List.ofFn left ++ List.ofFn right) := full ▸ w.2
    have rightValid := validWindows_suffix (List.ofFn left) (List.ofFn right) ok
    have seen (bit : Bool) : some bit ∈ List.ofFn right := by
      simpa using validWindows_at rightValid 0 (by simp) bit
    exact ⟨⟨right, seen⟩, ⟨left, ok⟩⟩
  invFun w :=
    ⟨Fin.append w.2.1 w.1.1, by
      rw [List.ofFn_fin_append]
      exact w.2.2⟩
  left_inv w := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [List.ofFn_fin_append, List.ofFn_add]
    rfl
  right_inv w := by
    have extensionality (a b : Σ seed : Seed,
        {w : Fin k → Letter // validWindows (List.ofFn w ++ List.ofFn seed.1)})
        (seeds : a.1.1 = b.1.1) (words : a.2.1 = b.2.1) : a = b := by
      rcases a with ⟨⟨seed₁, h₁⟩, word₁, hword₁⟩
      rcases b with ⟨⟨seed₂, h₂⟩, word₂, hword₂⟩
      cases seeds
      cases words
      rfl
    apply extensionality
    · funext i
      exact Fin.append_right _ _ i
    · funext i
      exact Fin.append_left _ _ i

private theorem validFour_count (k : ℕ) :
    (Fintype.card {w : Fin (k + 4) → Letter // validWindows (List.ofFn w)} : ℚ) =
      ∑ seed : Seed, extensions k (seedState seed.1) := by
  rw [Fintype.card_congr (splitSeeds k), Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro seed _
  let eqv := validExtensionsEquiv (seedState seed.1) (seedOrientation seed.1)
    (List.ofFn seed.1) (seed_represents seed) (by simp) (seed_valid seed) k
  rw [← Fintype.card_congr eqv]
  exact card_legalMoves (seedState seed.1) k


private def evolve (initial : AgePair → ℚ) : ℕ → AgePair → ℚ
  | 0 => initial
  | k + 1 => fun state => ((successors state).map (evolve initial k)).sum

private theorem evolve_extensions (k j : ℕ) (state : AgePair) :
    evolve (extensions k) j state = extensions (k + j) state := by
  induction j generalizing state with
  | zero => rfl
  | succ j ih =>
    have h : evolve (extensions k) j = extensions (k + j) := funext ih
    simp only [evolve, extensions, h]
    rfl

private theorem recurrenceSix (initial : AgePair → ℚ) (state : AgePair) :
    evolve initial 6 state + evolve initial 1 state + initial state =
      evolve initial 5 state + 2 * evolve initial 4 state +
        2 * evolve initial 3 state + 2 * evolve initial 2 state := by
  cases state <;> simp only [evolve, successors, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] <;> ring

private theorem extensions_recurrence (k : ℕ) (state : AgePair) :
    extensions (k + 6) state + extensions (k + 1) state + extensions k state =
      extensions (k + 5) state + 2 * extensions (k + 4) state +
        2 * extensions (k + 3) state + 2 * extensions (k + 2) state := by
  simpa only [evolve_extensions] using recurrenceSix (extensions k) state

private noncomputable def validFourCount (k : ℕ) : ℚ :=
  (Fintype.card {w : Fin (k + 4) → Letter // validWindows (List.ofFn w)} : ℚ)

private theorem validFour_recurrence (k : ℕ) :
    validFourCount (k + 6) + validFourCount (k + 1) + validFourCount k =
      validFourCount (k + 5) + 2 * validFourCount (k + 4) +
        2 * validFourCount (k + 3) + 2 * validFourCount (k + 2) := by
  simp only [validFourCount, validFour_count, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun seed _ => extensions_recurrence k (seedState seed.1)

end FourWindowGrowth

open BinaryDeletionDimension FourWindowGrowth
open scoped Classical

def windowEdge {n length : ℕ} (start : {i : ℕ // i + length ≤ n}) : Set (Fin n) :=
  {j | start.1 ≤ j.val ∧ j.val < start.1 + length}

def NoRun {n : ℕ} (length : ℕ) (w : Fin n → Bool) : Prop :=
  ∀ edge ∈ Set.range (windowEdge (n := n) (length := length)), ∃ j ∈ edge, w j = false


private theorem kernelDimension_four_eq_count (k : ℕ) :
    (Module.finrank ℂ (SupportedKernel (NoRun (n := k + 4) 4)) : ℚ) =
      validFourCount k := by
  rw [supportedKernel_finrank, Nat.card_eq_fintype_card, validFourCount]
  congr 1
  apply Fintype.card_congr
  refine Equiv.subtypeEquivRight fun w => ?_
  rw [validWindows_ofFn_iff]
  unfold NoRun
  rw [allowed_pattern_hyperedges]
  constructor
  · intro h i hi bit
    obtain ⟨hf, ht⟩ := h (windowEdge ⟨i, hi⟩) ⟨⟨i, hi⟩, rfl⟩
    cases bit
    · obtain ⟨j, hj, read⟩ := hf
      exact ⟨j, hj.1, hj.2, read⟩
    · obtain ⟨j, hj, read⟩ := ht
      exact ⟨j, hj.1, hj.2, read⟩
  · rintro h edge ⟨⟨i, hi⟩, rfl⟩
    constructor
    · obtain ⟨j, hj₁, hj₂, read⟩ := h i hi false
      exact ⟨j, ⟨hj₁, hj₂⟩, read⟩
    · obtain ⟨j, hj₁, hj₂, read⟩ := h i hi true
      exact ⟨j, ⟨hj₁, hj₂⟩, read⟩


/-- The four-site automaton counts every surviving pattern and gives a six-step recurrence. -/
theorem kernelDimension_four_recurrence (k : ℕ) :
    let d := fun i : ℕ => Module.finrank ℂ (SupportedKernel (NoRun (n := i + 4) 4))
    d (k + 6) + d (k + 1) + d k =
      d (k + 5) + 2 * d (k + 4) + 2 * d (k + 3) + 2 * d (k + 2) := by
  let d := fun i : ℕ => Module.finrank ℂ (SupportedKernel (NoRun (n := i + 4) 4))
  change d (k + 6) + d (k + 1) + d k =
    d (k + 5) + 2 * d (k + 4) + 2 * d (k + 3) + 2 * d (k + 2)
  have eq (i : ℕ) : (d i : ℚ) = validFourCount i := kernelDimension_four_eq_count i
  exact_mod_cast (show (d (k + 6) : ℚ) + d (k + 1) + d k =
      d (k + 5) + 2 * d (k + 4) + 2 * d (k + 3) + 2 * d (k + 2) by
    simpa only [eq] using validFour_recurrence k)

theorem kernelDimension_lower (k length : ℕ) (hlen : 4 ≤ length) :
    (100 / 43 : ℚ) ^ k ≤
      (Module.finrank ℂ (SupportedKernel (NoRun (n := k + 2) length)) : ℚ) := by
  let Allowed := NoRun (n := k + 2) length
  let setOfPatterns := {p : Pattern (Fin (k + 2)) // AllowedPattern Allowed p}
  let embed (p : {w : Fin (k + 2) → Letter // validWindows (List.ofFn w)}) :
      setOfPatterns := by
    refine ⟨p.1, ?_⟩
    show AllowedPattern (NoRun length) p.1
    unfold NoRun
    rw [allowed_pattern_hyperedges]
    rintro edge ⟨start, rfl⟩
    have h₀ : start.1 + 4 ≤ k + 2 := by have := start.2; omega
    constructor
    · obtain ⟨j, hj₀, hj₁, hj⟩ := all_windows_contain_orientations p.1 p.2 h₀ false
      exact ⟨j, ⟨hj₀, by omega⟩, hj⟩
    · obtain ⟨j, hj₀, hj₁, hj⟩ := all_windows_contain_orientations p.1 p.2 h₀ true
      exact ⟨j, ⟨hj₀, by omega⟩, hj⟩
  have hcard := Fintype.card_le_of_injective embed (fun u v huv =>
    Subtype.ext (congrArg (fun a : setOfPatterns => a.1) huv))
  apply (validPatterns_lower k).trans
  change _ ≤ (Module.finrank ℂ (SupportedKernel Allowed) : ℚ)
  rw [supportedKernel_finrank, Nat.card_eq_fintype_card]
  exact_mod_cast hcard


noncomputable def allowedCount (n length : ℕ) : ℕ :=
  Nat.card {w : Fin n → Bool // NoRun length w}

theorem kernelDimension_to_allowedCount (k length : ℕ) (hlen : 4 ≤ length) :
    (50 / 43 : ℚ) ^ k / 4 ≤
      (Module.finrank ℂ (SupportedKernel (NoRun (n := k + 2) length)) : ℚ) /
        (allowedCount (k + 2) length : ℚ) := by
  have hw : allowedCount (k + 2) length ≤ 2 ^ (k + 2) := by
    unfold allowedCount
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
      (by simp)
  have hh : 0 < (allowedCount (k + 2) length : ℚ) := by
    have : Nonempty {w : Fin (k + 2) → Bool // NoRun length w} := by
      refine ⟨⟨fun _ => false, ?_⟩⟩
      rintro edge ⟨start, rfl⟩
      have hh := start.2
      exact ⟨⟨start.1, by omega⟩, ⟨le_rfl, by change start.1 < start.1 + length; omega⟩, rfl⟩
    unfold allowedCount
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_pos (α := {w : Fin (k + 2) → Bool // NoRun length w}))
  have hq : (allowedCount (k + 2) length : ℚ) ≤ (2 : ℚ) ^ (k + 2) := by exact_mod_cast hw
  apply (le_div_iff₀ hh).mpr
  calc
    _ ≤ (50 / 43 : ℚ) ^ k / 4 * (2 : ℚ) ^ (k + 2) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (100 / 43 : ℚ) ^ k := by
      rw [pow_add]
      calc
        (50 / 43 : ℚ) ^ k / 4 * (2 ^ k * 2 ^ 2) =
            (50 / 43 : ℚ) ^ k * 2 ^ k := by ring
        _ = (100 / 43 : ℚ) ^ k := by
          rw [← mul_pow]
          norm_num
    _ ≤ _ := kernelDimension_lower k length hlen

end D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionGrowth
