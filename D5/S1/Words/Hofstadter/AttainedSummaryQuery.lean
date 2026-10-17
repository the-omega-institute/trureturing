/- GID: D5/S1/Words/Hofstadter/AttainedSummaryQuery
   generality: G
   mirror-B: D5/B/S1/Words/Hofstadter/AttainedSummaryQuery
   mirror-E: none(waiver:unbounded-symbolic-simulation)
   anchors: []
   utility: none
   digest: Attained ternary summaries and exact finite-block prefix-query simulation. -/
import D5.S1.Words.Hofstadter.OriginalHFoundation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Hofstadter.AttainedSummaryQuery

open OriginalHFoundation (Letter tau)
open RankOneMorphismIterationBound (image image_add subst)

/-- Three scalar coordinates, indexed by the original letters. -/
structure Triple where
  one : ℕ
  two : ℕ
  three : ℕ
  deriving DecidableEq, Repr

/-- Coordinate selection uses finite control only. -/
def Triple.at (v : Triple) : Letter → ℕ
  | .one => v.one
  | .two => v.two
  | .three => v.three

/-- The simultaneous update reads only the old three coordinates. -/
def forward (v : Triple) : Triple := ⟨v.two, v.three, v.one + v.three⟩

/-- Natural subtraction is used only on attained successors in the proof. -/
def reverse (v : Triple) : Triple := ⟨v.three - v.two, v.one, v.two⟩

/-- The six scalar summary registers. -/
structure Summary where
  lengths : Triple
  counts : Triple
  deriving DecidableEq, Repr

/-- Literal initial lengths and counts of the letter one. -/
def initial : Summary := ⟨⟨1, 1, 1⟩, ⟨1, 0, 0⟩⟩

/-- Both triples advance simultaneously. -/
def advance (s : Summary) : Summary := ⟨forward s.lengths, forward s.counts⟩

/-- Both triples roll back simultaneously. -/
def rollback (s : Summary) : Summary := ⟨reverse s.lengths, reverse s.counts⟩

/-- Numeric provenance from the fixed initial registers; no word is an input. -/
def generated : ℕ → Summary
  | 0 => initial
  | t + 1 => advance (generated t)

private theorem image_next (t : ℕ) (a : Letter) :
    image tau (t + 1) a = match a with
      | .one => image tau t .two
      | .two => image tau t .three
      | .three => image tau t .three ++ image tau t .one := by
  have h := image_add tau t 1 a
  cases a <;> simpa [tau, subst] using h

private theorem alignment (t : ℕ) (a : Letter) :
    (generated t).lengths.at a = (image tau t a).length ∧
    (generated t).counts.at a = (image tau t a).count .one := by
  induction t generalizing a with
  | zero => cases a <;> simp [generated, initial, Triple.at, image]
  | succ t ih =>
    have h1 := ih .one
    have h2 := ih .two
    have h3 := ih .three
    cases a <;> simp only [generated, advance, forward, Triple.at, image_next,
      List.length_append, List.count_append] at * <;> constructor <;> omega

private theorem coordinate_bounds (t : ℕ) (a : Letter) :
    (generated t).counts.at a ≤ (generated t).lengths.at a ∧
    (generated t).lengths.at a ≤ 2 ^ t := by
  have hc : (generated t).counts.at a ≤ (generated t).lengths.at a := by
    rw [(alignment t a).1, (alignment t a).2]
    exact List.count_le_length
  refine ⟨hc, ?_⟩
  clear hc
  induction t generalizing a with
  | zero => cases a <;> simp [generated, initial, Triple.at]
  | succ t ih =>
    have h1 := ih .one
    have h2 := ih .two
    have h3 := ih .three
    cases a <;> simp only [generated, advance, forward, Triple.at, pow_succ] at h1 h2 h3 ⊢ <;> omega

private theorem lengths_ordered (t : ℕ) :
    (generated t).lengths.one ≤ (generated t).lengths.two ∧
    (generated t).lengths.two ≤ (generated t).lengths.three := by
  induction t with
  | zero => simp [generated, initial]
  | succ t ih => simp only [generated, advance, forward]; omega

private theorem lengths_mono_step (t : ℕ) (a : Letter) :
    (generated t).lengths.at a ≤ (generated (t + 1)).lengths.at a := by
  have h := lengths_ordered t
  cases a <;> simp only [generated, advance, forward, Triple.at] <;> omega

private theorem lengths_mono {t u : ℕ} (h : t ≤ u) (a : Letter) :
    (generated t).lengths.at a ≤ (generated u).lengths.at a := by
  exact (monotone_nat_of_le_succ (fun t => lengths_mono_step t a)) h

private theorem three_step_growth (j : ℕ) (a : Letter) :
    2 ^ j ≤ (generated (3 * j)).lengths.at a := by
  induction j generalizing a with
  | zero => cases a <;> simp [generated, initial, Triple.at]
  | succ j ih =>
    have h1 := ih .one
    have h2 := ih .two
    have h3 := ih .three
    rw [show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by omega]
    cases a <;> simp only [generated, advance, forward, Triple.at, pow_succ] at h1 h2 h3 ⊢ <;> omega

private theorem before_cutoff (N t : ℕ) (h : (generated t).lengths.three < N) :
    t < 3 * N := by
  by_contra hn
  have hl := lengths_mono (by omega : 3 * N ≤ t) .three
  have hg := three_step_growth N .three
  have hp := N.lt_two_pow_self
  change (generated (3 * N)).lengths.three ≤ (generated t).lengths.three at hl
  change 2 ^ N ≤ (generated (3 * N)).lengths.three at hg
  omega

/-- An acquired counter and its six retained scalar registers. -/
structure Top where
  layer : ℕ
  summary : Summary
  deriving DecidableEq, Repr

/-- The alignment argument is erased; runtime tests only the current third
    length and otherwise updates the six registers and counter. -/
private def seek (N t : ℕ) (s : Summary) (hs : s = generated t) : Top :=
  if N ≤ s.lengths.three then ⟨t, s⟩
  else seek N (t + 1) (advance s) (by simp [hs, generated])
termination_by 3 * N - t
decreasing_by
  have _hh : ¬ N ≤ s.lengths.three := by assumption
  have ht := before_cutoff N t (by rw [← hs]; omega)
  omega

/-- Threshold acquisition starts from the literal level-zero registers. -/
def acquire (N : ℕ) : Top := seek N 0 initial rfl

/-- The least b with N < 2^b is an analysis quantity, never a seek input. -/
def analysisBits (N : ℕ) : ℕ := Nat.find (show ∃ b, N < 2 ^ b from
  ⟨N, N.lt_two_pow_self⟩)

private theorem seek_spec (N t : ℕ) (s : Summary) (hs : s = generated t) :
    let z := seek N t s hs
    t ≤ z.layer ∧ z.summary = generated z.layer ∧ N ≤ z.summary.lengths.three ∧
    ∀ k, t ≤ k → k < z.layer → (generated k).lengths.three < N := by
  rw [seek]
  split_ifs with h
  · dsimp only
    exact ⟨le_rfl, hs, h, by intro k hk hk'; omega⟩
  · have ih := seek_spec N (t + 1) (advance s) (by simp [hs, generated])
    dsimp only at ih ⊢
    refine ⟨by omega, ih.2.1, ih.2.2.1, ?_⟩
    intro k hk hk'
    by_cases he : k = t
    · subst k; simpa [hs] using Nat.lt_of_not_ge h
    · exact ih.2.2.2 k (by omega) hk'
termination_by 3 * N - t
decreasing_by
  have _hh : ¬ N ≤ s.lengths.three := by assumption
  have ht := before_cutoff N t (by rw [← hs]; omega)
  omega

private theorem rollback_generated (t : ℕ) :
    rollback (generated (t + 1)) = generated t ∧
    (generated (t + 1)).lengths.two ≤ (generated (t + 1)).lengths.three ∧
    (generated (t + 1)).counts.two ≤ (generated (t + 1)).counts.three := by
  simp [generated, advance, rollback, reverse, forward]

/-- Active query registers; the retained top is a separate immutable argument. -/
structure State where
  layer : ℕ
  summary : Summary
  letter : Letter
  residual : ℕ
  total : ℕ
  deriving DecidableEq, Repr

/-- Copy the top, retain the address as residual, and start with zero count. -/
def start (z : Top) (a : Letter) (m : ℕ) : State :=
  ⟨z.layer, z.summary, a, m, 0⟩

/-- A positive-layer descent rolls back first. The split uses the closed
    left endpoint; the transition reads no word, prior prefix value or trace. -/
def descend (q : State) : State :=
  if q.layer = 0 then q else
  let s := rollback q.summary
  match q.letter with
  | .one => ⟨q.layer - 1, s, .two, q.residual, q.total⟩
  | .two => ⟨q.layer - 1, s, .three, q.residual, q.total⟩
  | .three =>
    if q.residual ≤ s.lengths.three then
      ⟨q.layer - 1, s, .three, q.residual, q.total⟩
    else ⟨q.layer - 1, s, .one, q.residual - s.lengths.three,
      q.total + s.counts.three⟩

/-- Iteration is a semantic trajectory, not an array supplied to descend. -/
def trajectory (z : Top) (a : Letter) (m k : ℕ) : State :=
  descend^[k] (start z a m)

/-- At layer zero a singleton one contributes its residual, either zero or one. -/
def readout (q : State) : ℕ := q.total + if q.letter = .one then q.residual else 0

/-- Every call executes exactly the acquired number of descents, even at zero. -/
def query (z : Top) (m : ℕ) : ℕ := readout (trajectory z .three m z.layer)

/-- The conserved finite prefix count, valid residual, and address budget. -/
def Invariant (rank m : ℕ) (q : State) : Prop :=
  q.summary = generated q.layer ∧
  q.residual ≤ q.summary.lengths.at q.letter ∧
  q.total + q.residual ≤ m ∧
  rank = q.total + ((image tau q.layer q.letter).take q.residual).count .one

/-- Every subtraction about to be executed has its source-order premise. -/
def Legal (q : State) : Prop :=
  0 < q.layer →
    q.summary.lengths.two ≤ q.summary.lengths.three ∧
    q.summary.counts.two ≤ q.summary.counts.three ∧
    (q.letter = .three → (rollback q.summary).lengths.three < q.residual →
      (rollback q.summary).lengths.three ≤ q.residual)

private theorem legal_of_aligned (q : State) (hs : q.summary = generated q.layer) :
    Legal q := by
  intro hp
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q.layer ≠ 0)
  have h := rollback_generated t
  rw [hs, ht]
  exact ⟨h.2.1, h.2.2, by intros; omega⟩

private theorem step_invariant (rank m : ℕ) (q : State)
    (h : Invariant rank m q) (hp : 0 < q.layer) :
    Invariant rank m (descend q) ∧ (descend q).layer + 1 = q.layer := by
  rcases q with ⟨t, s, a, r, Q⟩
  change 0 < t at hp
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  rcases h with ⟨hs, hr, hb, hc⟩
  dsimp only at hs hr hb hc hp ⊢
  subst s
  have hroll := (rollback_generated t).1
  have ha := alignment t .three
  change (generated t).lengths.three = (image tau t .three).length ∧
    (generated t).counts.three = (image tau t .three).count .one at ha
  have h1 := alignment t .one
  have h2 := alignment t .two
  have hv := (coordinate_bounds t .three).1
  cases a with
  | one =>
    simp only [descend, Nat.succ_ne_zero,
      ↓reduceIte, hroll, Nat.succ_sub_one]
    refine ⟨⟨rfl, ?_, hb, ?_⟩, True.intro⟩
    · simpa [generated, advance, forward, Triple.at] using hr
    · simpa only [image_next] using hc
  | two =>
    simp only [descend, Nat.succ_ne_zero,
      ↓reduceIte, hroll, Nat.succ_sub_one]
    refine ⟨⟨rfl, ?_, hb, ?_⟩, True.intro⟩
    · simpa [generated, advance, forward, Triple.at] using hr
    · simpa only [image_next] using hc
  | three =>
    by_cases hleft : r ≤ (generated t).lengths.three
    · simp only [descend, Nat.succ_ne_zero,
        ↓reduceIte, hroll, Nat.succ_sub_one, hleft]
      refine ⟨⟨rfl, hleft, hb, ?_⟩, True.intro⟩
      rw [image_next, List.take_append_of_le_length (by rwa [← ha.1])] at hc
      exact hc
    · have hgt : (generated t).lengths.three < r := Nat.lt_of_not_ge hleft
      have hrl : (generated t).lengths.three ≤ r := hgt.le
      simp only [descend, Nat.succ_ne_zero,
        ↓reduceIte, hroll, Nat.succ_sub_one, hleft]
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, True.intro⟩
      · simp only [generated, advance, forward, Triple.at] at hr
        change r - (generated t).lengths.three ≤ (generated t).lengths.one
        omega
      · change Q + (generated t).counts.three + (r - (generated t).lengths.three) ≤ m
        change (generated t).counts.three ≤ (generated t).lengths.three at hv
        omega
      · rw [image_next, List.take_append,
          List.take_of_length_le (by rwa [← ha.1]), List.count_append] at hc
        rw [← ha.1, ← ha.2] at hc
        simpa only [Nat.add_assoc] using hc

private theorem simulation (T : ℕ) (a : Letter) (m : ℕ)
    (hm : m ≤ (generated T).lengths.at a) (k : ℕ) (hk : k ≤ T) :
    let q := trajectory ⟨T, generated T⟩ a m k
    q.layer = T - k ∧
    Invariant (((image tau T a).take m).count .one) m q ∧ Legal q := by
  induction k with
  | zero =>
    change T = T - 0 ∧ Invariant _ m (start ⟨T, generated T⟩ a m) ∧
      Legal (start ⟨T, generated T⟩ a m)
    refine ⟨by omega, ⟨rfl, hm, ?_, ?_⟩, legal_of_aligned _ rfl⟩
    · change 0 + m ≤ m; omega
    · exact (Nat.zero_add _).symm
  | succ k ih =>
    have hi := ih (by omega)
    have hp : 0 < (trajectory ⟨T, generated T⟩ a m k).layer := by rw [hi.1]; omega
    have hs := step_invariant _ _ _ hi.2.1 hp
    have he : trajectory ⟨T, generated T⟩ a m (k + 1) =
        descend (trajectory ⟨T, generated T⟩ a m k) := by
      simp only [trajectory, Function.iterate_succ_apply']
    rw [he]
    refine ⟨by omega, hs.1, legal_of_aligned _ hs.1.1⟩

private theorem terminal_correct (rank m : ℕ) (q : State)
    (h : Invariant rank m q) (ht : q.layer = 0) :
    q.residual = 0 ∨ q.residual = 1 := by
  have hr := h.2.1
  rw [h.1, ht] at hr
  have he : (generated 0).lengths.at q.letter = 1 := by
    cases q.letter <;> rfl
  rw [he] at hr
  omega

private theorem terminal_readout (rank m : ℕ) (q : State)
    (h : Invariant rank m q) (ht : q.layer = 0) :
    readout q = rank ∧ readout q ≤ m := by
  have hr := terminal_correct rank m q h ht
  have hc := h.2.2.2
  have hb := h.2.2.1
  rw [ht] at hc
  rcases hr with hr | hr <;> cases ha : q.letter <;>
    simp_all [readout, image] <;> omega

/-- Uniform symbolic correctness of acquisition and every reached query state.
    The final count is of the actual finite root block, with all endpoints. -/
theorem attained_summary_query (N : ℕ) :
    let z := acquire N
    z.summary = generated z.layer ∧
    N ≤ z.summary.lengths.three ∧
    (∀ t, t < z.layer → (generated t).lengths.three < N) ∧
    (∀ t, N ≤ (generated t).lengths.three →
      (∀ k, k < t → (generated k).lengths.three < N) → t = z.layer) ∧
    N < 2 ^ analysisBits N ∧
    (∀ b, b < analysisBits N → 2 ^ b ≤ N) ∧
    z.layer ≤ 3 * analysisBits N ∧
    (∀ t a, (generated t).lengths.at a = (image tau t a).length ∧
      (generated t).counts.at a = (image tau t a).count .one ∧
      (generated t).counts.at a ≤ (generated t).lengths.at a ∧
      (generated t).lengths.at a ≤ 2 ^ t) ∧
    (∀ m, m ≤ N →
      (∀ k, k ≤ z.layer →
        let q := trajectory z .three m k;
        q.layer = z.layer - k ∧
        Invariant (((image tau z.layer .three).take m).count .one) m q ∧ Legal q) ∧
      (let q := trajectory z .three m z.layer;
        q.layer = 0 ∧ (q.residual = 0 ∨ q.residual = 1)) ∧
      query z m = ((image tau z.layer .three).take m).count .one ∧
      query z m ≤ m ∧ m - query z m ≤ m) := by
  let z := acquire N
  have hs := seek_spec N 0 initial rfl
  change 0 ≤ z.layer ∧ z.summary = generated z.layer ∧
    N ≤ z.summary.lengths.three ∧
    ∀ k, 0 ≤ k → k < z.layer → (generated k).lengths.three < N at hs
  have hfirst (t : ℕ) (ht : t < z.layer) : (generated t).lengths.three < N :=
    hs.2.2.2 t (Nat.zero_le _) ht
  have hbits : N < 2 ^ analysisBits N := by
    unfold analysisBits
    exact Nat.find_spec (p := fun b : ℕ => N < 2 ^ b) ⟨N, N.lt_two_pow_self⟩
  have hbound : z.layer ≤ 3 * analysisBits N := by
    by_contra hn
    have hg := three_step_growth (analysisBits N) .three
    have hf := hfirst (3 * analysisBits N) (by omega)
    change 2 ^ analysisBits N ≤ (generated (3 * analysisBits N)).lengths.three at hg
    omega
  refine ⟨hs.2.1, hs.2.2.1, hfirst, ?_, hbits, ?_, hbound, ?_, ?_⟩
  · intro t ht hf
    have hz : N ≤ (generated z.layer).lengths.three := by
      simpa [hs.2.1] using hs.2.2.1
    by_contra he
    rcases lt_or_gt_of_ne he with h | h
    · have := hfirst t h; omega
    · have := hf z.layer h; omega
  · intro b hb
    exact Nat.le_of_not_gt (Nat.find_min (p := fun b : ℕ => N < 2 ^ b)
      ⟨N, N.lt_two_pow_self⟩ hb)
  · intro t a
    exact ⟨(alignment t a).1, (alignment t a).2,
      (coordinate_bounds t a).1, (coordinate_bounds t a).2⟩
  · intro m hm
    have hm' : m ≤ (generated z.layer).lengths.at .three := by
      change m ≤ (generated z.layer).lengths.three
      rw [← hs.2.1]
      omega
    have he : z = ⟨z.layer, generated z.layer⟩ := by
      calc z = ⟨z.layer, z.summary⟩ := by cases z; rfl
           _ = ⟨z.layer, generated z.layer⟩ := congrArg (Top.mk z.layer) hs.2.1
    have hall (k : ℕ) (hk : k ≤ z.layer) := simulation z.layer .three m hm' k hk
    have hend := hall z.layer le_rfl
    simp only [Nat.sub_self] at hend
    have ht : (trajectory z .three m z.layer).layer = 0 := by simpa [← he] using hend.1
    have hi : Invariant (((image tau z.layer .three).take m).count .one) m
        (trajectory z .three m z.layer) := by simpa [← he] using hend.2.1
    have hout := terminal_readout _ _ _ hi ht
    refine ⟨?_, ⟨ht, terminal_correct _ _ _ hi ht⟩, hout.1, hout.2, Nat.sub_le _ _⟩
    intro k hk
    simpa only [← he] using hall k hk

end D5.S1.Words.Hofstadter.AttainedSummaryQuery
