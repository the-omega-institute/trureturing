/- GID: D5/S1/Words/Hofstadter/OriginalHFoundation
   generality: G
   mirror-B: D5/B/S1/Words/Hofstadter/OriginalHFoundation
   mirror-E: none(waiver:unbounded-structural-identity)
   anchors: []
   utility: none
   digest: Original triple Hofstadter recurrence and exact all-natural morphic prefix counts. -/
import D5.S1.Words.RankOneMorphismIterationBoundDefs
import Mathlib.Data.List.GetD

/-! The original H and substitution of Letouzey–Li–Steiner,
    arXiv:2410.00529v2, Theorem 3.1 and Propositions 4.1–4.3.
    The bounded-depth construction follows Pierre Letouzey's public-domain
    `GenG.v`, commit dde0281c7a92550806f264112692da9165543942.
    The word argument below uses the original letters 1, 2, 3. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Hofstadter.OriginalHFoundation

open RankOneMorphismIterationBound (subst image image_add)

/-- The source alphabet, with constructors named by the original labels. -/
inductive Letter where
  | one | two | three
  deriving DecidableEq, Repr

/-- The original substitution: 1 ↦ 2, 2 ↦ 3, 3 ↦ 31. -/
def tau : Letter → List Letter
  | .one => [.two]
  | .two => [.three]
  | .three => [.three, .one]

/-- The literal iterate τⁿ(3), including the singleton zero iterate. -/
def block (n : ℕ) : List Letter := image tau n .three

/-- The first n letters of an infinite word, in increasing position order. -/
def wordPrefix (x : ℕ → Letter) (n : ℕ) : List Letter := (List.range n).map x

/-- A literal infinite fixed word starting with 3: substitution of every
    finite prefix is again the prefix of the same word of that exact length. -/
def IsOriginalWord (x : ℕ → Letter) : Prop :=
  x 0 = .three ∧ ∀ n,
    wordPrefix x (subst tau (wordPrefix x n)).length = subst tau (wordPrefix x n)

/-- A total word read from its growing literal iterates. -/
def word (n : ℕ) : Letter := (block n).getD n .three

/-- The original initialization and exactly three nested applications. -/
def IsOriginalH (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧ ∀ n, f (n + 1) = n + 1 - f (f (f n))

private def eval : ℕ → ℕ → ℕ
  | 0, _ => 0
  | p + 1, n => n - eval p (eval p (eval p (n - 1)))

/-- A numerical construction independent of the word or any counting oracle. -/
def H (n : ℕ) : ℕ := eval n n

private theorem eval_le (p n : ℕ) : eval p n ≤ n := by
  cases p <;> simp [eval]

private theorem eval_zero (p : ℕ) : eval p 0 = 0 := by
  cases p <;> simp [eval]

private theorem eval_coherent (p q n : ℕ) (hp : n ≤ p) (hq : n ≤ q) :
    eval p n = eval q n := by
  induction p generalizing q n with
  | zero =>
    have : n = 0 := by omega
    subst n
    simp [eval_zero]
  | succ p ih =>
    cases q with
    | zero =>
      have : n = 0 := by omega
      subst n
      simp [eval_zero]
    | succ q =>
      cases n with
      | zero => simp [eval_zero]
      | succ n =>
        have agree (m : ℕ) (hm : m ≤ n) : eval p m = eval q m :=
          ih q m (by omega) (by omega)
        have a := agree n le_rfl
        have b := agree (eval q n) (eval_le q n)
        have c := agree (eval q (eval q n)) ((eval_le q _).trans (eval_le q n))
        simp only [eval, Nat.add_sub_cancel, a, b, c]

private theorem H_le (n : ℕ) : H n ≤ n := eval_le n n

private theorem H_succ (n : ℕ) : H (n + 1) = n + 1 - H (H (H n)) := by
  have agree (m : ℕ) (hm : m ≤ n) : eval n m = H m :=
    eval_coherent n m m hm le_rfl
  have a := agree n le_rfl
  have b := agree (H n) (H_le n)
  have c := agree (H (H n)) ((H_le _).trans (H_le n))
  change n + 1 - eval n (eval n (eval n n)) = _
  rw [a, b, c]

/-- The independently constructed numerical function realizes the original
    recurrence, and every function satisfying those equations is this H. -/
theorem h_characterization : IsOriginalH H ∧ ∀ f, IsOriginalH f → f = H := by
  refine ⟨⟨rfl, H_succ⟩, ?_⟩
  intro f hf
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hf.1
    | succ n =>
      rw [hf.2, H_succ]
      have a := ih n (by omega)
      have b := ih (H n) (by have := H_le n; omega)
      have c := ih (H (H n)) (by have := (H_le _).trans (H_le n); omega)
      rw [a, b, c]

private theorem image_nonempty (k : ℕ) (a : Letter) : image tau k a ≠ [] := by
  induction k with
  | zero => simp [image]
  | succ k ih =>
    cases he : image tau k a with
    | nil => exact False.elim (ih he)
    | cons c v => cases c <;> simp [image, subst, he, tau]

private theorem block_step (k : ℕ) :
    block (k + 1) = block k ++ image tau k .one := by
  simpa [block, tau, subst] using image_add tau k 1 .three

private theorem block_growth (k : ℕ) : k + 1 ≤ (block k).length := by
  induction k with
  | zero => simp [block, image]
  | succ k ih =>
    have ht := List.length_pos_iff.mpr (image_nonempty k .one)
    rw [block_step, List.length_append]
    omega

private theorem block_prefix {k m : ℕ} (h : k ≤ m) : block k <+: block m := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction s with
  | zero => simp
  | succ s ih =>
    have hs : block (k + s) <+: block (k + s + 1) := by
      rw [block_step]
      exact List.prefix_append _ _
    exact ih.trans hs

private theorem word_get (i k : ℕ) (hi : i < (block k).length) :
    word i = (block k).getD i .three := by
  unfold word
  rcases le_total i k with h | h
  · obtain ⟨v, hv⟩ := block_prefix h
    rw [← hv, List.getD_append _ _ _ _ (by have := block_growth i; omega)]
  · obtain ⟨v, hv⟩ := block_prefix h
    rw [← hv, List.getD_append _ _ _ _ hi]

private theorem prefix_block (n k : ℕ) (h : n ≤ (block k).length) :
    wordPrefix word n = (block k).take n := by
  apply List.ext_getElem
  · simp [wordPrefix, Nat.min_eq_left h]
  · intro i hi hi'
    have hin : i < n := by simpa [wordPrefix] using hi
    have hik : i < (block k).length := lt_of_lt_of_le hin h
    simp only [wordPrefix, List.getElem_map, List.getElem_range, List.getElem_take]
    exact (word_get i k hik).trans (List.getD_eq_getElem _ _ hik)

private theorem original_word_blocks {x : ℕ → Letter} (hx : IsOriginalWord x) (k : ℕ) :
    wordPrefix x (block k).length = block k := by
  induction k with
  | zero => simpa [block, image, wordPrefix] using hx.1
  | succ k ih =>
    have h := hx.2 (block k).length
    rw [ih] at h
    exact h

/-- The literal growing iterates define the unique original infinite fixed
    word. They cover every natural prefix length, including whole blocks. -/
theorem word_characterization :
    IsOriginalWord word ∧ (∀ x, IsOriginalWord x → x = word) ∧
    (∀ k, k + 1 ≤ (block k).length) ∧
    (∀ n k, n ≤ (block k).length → wordPrefix word n = (block k).take n) := by
  have hw : IsOriginalWord word := by
    refine ⟨rfl, ?_⟩
    intro n
    have hp : wordPrefix word n <+: block n := by
      rw [prefix_block n n (by have := block_growth n; omega)]
      exact List.take_prefix _ _
    have hs : subst tau (wordPrefix word n) <+: block (n + 1) := hp.flatMap tau
    rw [prefix_block _ (n + 1) hs.length_le]
    exact (List.prefix_iff_eq_take.mp hs).symm
  refine ⟨hw, ?_, block_growth, prefix_block⟩
  intro x hx
  funext i
  have hi : i < (block i).length := by have := block_growth i; omega
  have hx' := original_word_blocks hx i
  have hw' := original_word_blocks hw i
  have he := congrArg (fun v : List Letter => v[i]?) (hx'.trans hw'.symm)
  simpa [wordPrefix, hi] using he

/-- The number of letters other than the original letter 1. -/
def positive (w : List Letter) : ℕ := w.countP (· != .one)

private theorem positive_complement (w : List Letter) :
    positive w + w.count .one = w.length := by
  have hnot : (fun a : Letter => decide (¬ ((a != .one) = true))) =
      (fun a : Letter => a == .one) := by
    funext a
    cases a <;> rfl
  simpa only [positive, List.count, hnot] using
    (List.length_eq_countP_add_countP (fun a : Letter => a != .one) (l := w)).symm

private theorem substitution_counts (w : List Letter) (n : ℕ) :
    let r := positive ((subst tau w).take n)
    ((subst tau w).take n).count .three = positive (w.take r) ∧
    ((subst tau w).take (n + 1)).count .one = (w.take r).count .three := by
  induction w generalizing n with
  | nil => simp [subst, positive]
  | cons a w ih =>
    cases a with
    | one =>
      cases n with
      | zero => simp [subst, tau, positive]
      | succ n => simpa [subst, tau, positive] using ih n
    | two =>
      cases n with
      | zero => simp [subst, tau, positive]
      | succ n => simpa [subst, tau, positive] using ih n
    | three =>
      cases n with
      | zero => simp [subst, tau, positive]
      | succ n =>
        cases n with
        | zero => simp [subst, tau, positive]
        | succ n => simpa [subst, tau, positive, Nat.add_assoc] using ih n

private def P (n : ℕ) : ℕ := positive (wordPrefix word n)

private theorem P_le (n : ℕ) : P n ≤ n := by
  simpa [P, positive, wordPrefix] using
    (List.countP_le_length (p := (· != Letter.one)) (l := wordPrefix word n))

private theorem prefix_counts (n : ℕ) :
    P (P n) = (wordPrefix word n).count .three ∧
    (wordPrefix word (n + 1)).count .one = (wordPrefix word (P n)).count .three := by
  have h0 : wordPrefix word n = (subst tau (block (n + 1))).take n :=
    prefix_block n (n + 2) (by have := block_growth (n + 2); omega)
  have h1 : wordPrefix word (n + 1) = (subst tau (block (n + 1))).take (n + 1) :=
    prefix_block (n + 1) (n + 2) (by have := block_growth (n + 2); omega)
  have hr : positive ((subst tau (block (n + 1))).take n) = P n :=
    congrArg positive h0.symm
  have hin : (block (n + 1)).take (P n) = wordPrefix word (P n) :=
    (prefix_block (P n) (n + 1)
      (by have := block_growth (n + 1); have := P_le n; omega)).symm
  have hp := substitution_counts (block (n + 1)) n
  dsimp only at hp
  rw [hr, hin, ← h0, ← h1] at hp
  exact ⟨hp.1.symm, hp.2⟩

private theorem P_original : IsOriginalH P := by
  refine ⟨rfl, ?_⟩
  intro n
  have h3 : P (P (P n)) = (wordPrefix word (n + 1)).count .one :=
    (prefix_counts (P n)).1.trans (prefix_counts n).2.symm
  have hc := positive_complement (wordPrefix word (n + 1))
  have he : P (n + 1) + (wordPrefix word (n + 1)).count .one = n + 1 := by
    simpa [P, wordPrefix] using hc
  omega

/-- For every original fixed word and every natural prefix length, the
    independently realized original H is exactly the complementary count. -/
theorem original_h_morphic_prefix (x : ℕ → Letter) (hx : IsOriginalWord x) (n : ℕ) :
    H n + (wordPrefix x n).count .one = n := by
  have hxw := word_characterization.2.1 x hx
  subst x
  have hPH := h_characterization.2 P P_original
  rw [← hPH]
  simpa [P, wordPrefix] using positive_complement (wordPrefix word n)

end D5.S1.Words.Hofstadter.OriginalHFoundation
