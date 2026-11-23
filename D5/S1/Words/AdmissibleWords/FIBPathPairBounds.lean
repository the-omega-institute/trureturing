/- GID: D5/S1/Words/AdmissibleWords/FIBPathPairBounds
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FIBPathPairBounds
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Cumulative downward variation gives the sharp path-event difference from a fixed starting site. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import D5.S1.Words.AdmissibleWords.AdmissibleCount

open Set MeasureTheory
open D5.S1.Words.AdmissibleWords.AdmissibleCount

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.FIBPathPairBounds

/-- Sum of positive decreases along the path from the starting site. -/
def downwardVariation (q : ℕ → ℝ) (start : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => downwardVariation q start k + if start ≤ k then max 0 (q k - q (k + 1)) else 0

private theorem drops_zero (q : ℕ → ℝ) {start k : ℕ} (hk : k ≤ start) :
    downwardVariation q start k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have before : ¬ start ≤ k := by omega
      simp [downwardVariation, before, ih (by omega)]

private theorem drops_nonneg (q : ℕ → ℝ) (start k : ℕ) : 0 ≤ downwardVariation q start k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      apply add_nonneg ih
      split
      · exact le_max_left _ _
      · rfl

private theorem net_drop (q : ℕ → ℝ) {start k : ℕ} (hk : start ≤ k) :
    q start - downwardVariation q start k ≤ q k := by
  induction k with
  | zero =>
      rw [show start = 0 by omega]
      simp [downwardVariation]
  | succ k ih =>
      by_cases h : start ≤ k
      · have step := le_max_right 0 (q k - q (k + 1))
        simp only [downwardVariation, h, ite_true]
        linarith [ih h]
      · rw [show k + 1 = start by omega, drops_zero q le_rfl, sub_zero]

private def overlap (q : ℕ → ℝ) (start k : ℕ) : ℝ :=
  if k < start then min (q start) (q k)
  else max 0 (max (q start + q k - 1) (q start - downwardVariation q start k))

private theorem overlap_bounds (q : ℕ → ℝ) (bound : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (start k : ℕ) :
    0 ≤ overlap q start k ∧ overlap q start k ≤ q start ∧
    overlap q start k ≤ q k ∧ q k - overlap q start k ≤ 1 - q start := by
  by_cases h : k < start
  · simp only [overlap, ite_eq_left h]
    obtain ⟨hs0, hs1⟩ := bound start
    obtain ⟨hk0, hk1⟩ := bound k
    refine ⟨le_min hs0 hk0, min_le_left .., min_le_right .., ?_⟩
    rcases le_total (q start) (q k) with hle | hle
    · rw [min_eq_left hle]
      linarith
    · rw [min_eq_right hle]
      linarith
  · simp only [overlap, ite_eq_right h]
    obtain ⟨hs0, hs1⟩ := bound start
    obtain ⟨hk0, hk1⟩ := bound k
    refine ⟨le_max_left .., max_le hs0 (max_le (by linarith) (by linarith [drops_nonneg q start k])),
      max_le hk0 (max_le (by linarith) (net_drop q (by omega))), ?_⟩
    have hh := (le_max_left (q start + q k - 1) (q start - downwardVariation q start k)).trans
      (le_max_right 0 _)
    linarith

private theorem overlap_at_start (q : ℕ → ℝ) (bound : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (start : ℕ) : overlap q start start = q start := by
  simp only [overlap, lt_irrefl, ite_false, drops_zero q le_rfl, sub_zero]
  rw [max_eq_right (show q start + q start - 1 ≤ q start by linarith [(bound start).2])]
  rw [max_eq_right (bound start).1]

private theorem drop_formula (q : ℕ → ℝ) {start k : ℕ} (hk : start ≤ k) :
    q start - overlap q start k =
      min (q start) (min (1 - q k) (downwardVariation q start k)) := by
  simp [overlap, show ¬ k < start by omega, ← min_sub_sub_left,
    show q start - (q start + q k - 1) = 1 - q k by linarith]

private def Step (a b δ : ℝ) : Prop := a ≤ b ∧ b - a ≤ δ

private theorem step_max {a b c d δ : ℝ}
    (h₁ : Step a b δ) (h₂ : Step c d δ) : Step (max a c) (max b d) δ :=
  ⟨max_le_max h₁.1 h₂.1, (max_sub_max_le_max ..).trans (max_le h₁.2 h₂.2)⟩

private theorem step_min_left {s a b : ℝ} (hle : a ≤ b) : Step (min s a) (min s b) (b - a) := by
  refine ⟨min_le_min le_rfl hle, ?_⟩
  by_cases h : s ≤ a
  · rw [min_eq_left h, min_eq_left (h.trans hle)]
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    linarith [min_le_right s b]

private theorem overlap_step (q : ℕ → ℝ) (bound : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (start k : ℕ) :
    (q k ≤ q (k + 1) → Step (overlap q start k) (overlap q start (k + 1)) (q (k + 1) - q k)) ∧
    (q (k + 1) ≤ q k → Step (overlap q start (k + 1)) (overlap q start k) (q k - q (k + 1))) := by
  by_cases hk : k < start
  · have before : overlap q start k = min (q start) (q k) := by simp [overlap, hk]
    have next : overlap q start (k + 1) = min (q start) (q (k + 1)) := by
      by_cases h : k + 1 < start
      · simp [overlap, h]
      · simp [show k + 1 = start by omega, overlap_at_start q bound]
    simpa only [before, next] using
      And.intro (fun h => step_min_left (s := q start) h)
        (fun h => step_min_left (s := q start) h)
  · have after : start ≤ k := by omega
    have next : ¬ k + 1 < start := by omega
    simp only [overlap, ite_eq_right hk, ite_eq_right next, downwardVariation, after, ite_true]
    constructor
    · intro inc
      rw [max_eq_left (sub_nonpos.mpr inc), add_zero]
      apply step_max ⟨le_rfl, by linarith⟩
      apply step_max
      · constructor <;> linarith
      · exact ⟨le_rfl, by linarith⟩
    · intro dec
      rw [max_eq_right (sub_nonneg.mpr dec)]
      apply step_max ⟨le_rfl, by linarith⟩
      apply step_max <;> constructor <;> linarith

private def event (q : ℕ → ℝ) (start k : ℕ) : Set ℝ :=
  let u := overlap q start k
  Ico 0 u ∪ Ico (q start) (q start + (q k - u))

private theorem event_subset_unit (q : ℕ → ℝ) (bounds : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (start k : ℕ) : event q start k ⊆ Ico 0 1 := by
  obtain ⟨hu0, hus, huk, hku⟩ := overlap_bounds q bounds start k
  intro x hx
  change x ∈ Ico 0 (overlap q start k) ∪
    Ico (q start) (q start + (q k - overlap q start k)) at hx
  rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨h0, h1.trans_le (hus.trans (bounds start).2)⟩
  · refine ⟨(bounds start).1.trans h0, h1.trans_le ?_⟩
    linarith

private theorem event_measure (q : ℕ → ℝ) (bounds : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (start k : ℕ) : volume.real (event q start k) = q k := by
  obtain ⟨hu0, hus, huk, _⟩ := overlap_bounds q bounds start k
  unfold event
  dsimp only
  have hd : Disjoint (Ico 0 (overlap q start k))
      (Ico (q start) (q start + (q k - overlap q start k))) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge (hus.trans hy.1)) hx.2)
  rw [measureReal_union hd measurableSet_Ico (by simp) (by simp),
    Real.volume_real_Ico_of_le hu0, Real.volume_real_Ico_of_le (by linarith)]
  linarith

private theorem event_nested (q : ℕ → ℝ) (bounds : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    (start k : ℕ) :
    (q k ≤ q (k + 1) → event q start k ⊆ event q start (k + 1)) ∧
    (q (k + 1) ≤ q k → event q start (k + 1) ⊆ event q start k) := by
  have subset {s t : ℕ} (h : Step (overlap q start s) (overlap q start t) (q t - q s)) :
      event q start s ⊆ event q start t := by
    apply union_subset_union (Ico_subset_Ico_right h.1)
    apply Ico_subset_Ico_right
    have := h.2
    linarith
  exact ⟨fun h => subset ((overlap_step q bounds start k).1 h),
    fun h => subset ((overlap_step q bounds start k).2 h)⟩

private theorem event_sdiff (q : ℕ → ℝ) (bounds : ∀ k, 0 ≤ q k ∧ q k ≤ 1)
    {start k : ℕ} (hk : start ≤ k) :
    volume.real (event q start start \ event q start k) =
      min (q start) (min (1 - q k) (downwardVariation q start k)) := by
  obtain ⟨hu0, hus, _, _⟩ := overlap_bounds q bounds start k
  have shape : event q start start \ event q start k = Ico (overlap q start k) (q start) := by
    unfold event
    dsimp only
    rw [overlap_at_start q bounds, sub_self, add_zero, Ico_self, union_empty]
    ext x
    simp only [mem_sdiff, mem_Ico, mem_union, not_or, not_and_or, not_le, not_lt]
    constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> grind
  rw [shape, Real.volume_real_Ico_of_le hus, drop_formula q hk]

private structure NestedProfile (q : ℕ → ℝ) (A : ℕ → Set ℝ) : Prop where
  measurable : ∀ k, MeasurableSet (A k)
  within : ∀ k, A k ⊆ Ico 0 1
  marginals : ∀ k, volume.real (A k) = q k
  adjacent : ∀ k, A k ⊆ A (k + 1) ∨ A (k + 1) ⊆ A k

private theorem NestedProfile.finite {q : ℕ → ℝ} {A : ℕ → Set ℝ} (h : NestedProfile q A)
    {s : Set ℝ} (k : ℕ) (hs : s ⊆ A k) : volume s ≠ ⊤ :=
  measure_ne_top_of_subset (hs.trans (h.within k)) (by simp)

private theorem successive_difference {q : ℕ → ℝ} {A : ℕ → Set ℝ} (h : NestedProfile q A)
    (k : ℕ) : volume.real (A k \ A (k + 1)) = max 0 (q k - q (k + 1)) := by
  rcases h.adjacent k with inc | dec
  · have le := measureReal_mono inc (h.finite (k + 1) subset_rfl)
    rw [h.marginals, h.marginals] at le
    simp [sdiff_eq_empty.mpr inc, max_eq_left (sub_nonpos.mpr le)]
  · have le := measureReal_mono dec (h.finite k subset_rfl)
    rw [h.marginals, h.marginals] at le
    rw [measureReal_sdiff dec (h.measurable _) (h.finite k subset_rfl),
      h.marginals, h.marginals, max_eq_right (sub_nonneg.mpr le)]

private theorem cumulative_difference {q : ℕ → ℝ} {A : ℕ → Set ℝ} (h : NestedProfile q A)
    {start k : ℕ} (hk : start ≤ k) : volume.real (A start \ A k) ≤ downwardVariation q start k := by
  induction k with
  | zero => simp [show start = 0 by omega, downwardVariation]
  | succ k ih =>
      by_cases hle : start ≤ k
      · rw [downwardVariation, ite_eq_left hle]
        have sub : A start \ A (k + 1) ⊆ (A start \ A k) ∪ (A k \ A (k + 1)) := by
          intro x hx
          by_cases hm : x ∈ A k
          · exact Or.inr ⟨hm, hx.2⟩
          · exact Or.inl ⟨hx.1, hm⟩
        have fin : volume ((A start \ A k) ∪ (A k \ A (k + 1))) ≠ ⊤ :=
          measure_ne_top_of_subset (union_subset (sdiff_subset.trans (h.within start))
            (sdiff_subset.trans (h.within k))) (by simp)
        calc
          _ ≤ volume.real ((A start \ A k) ∪ (A k \ A (k + 1))) :=
            measureReal_mono sub fin
          _ ≤ volume.real (A start \ A k) + volume.real (A k \ A (k + 1)) :=
            measureReal_union_le _ _
          _ ≤ _ := by rw [successive_difference h k]; gcongr; exact ih hle
      · simp [show k + 1 = start by omega, drops_zero q le_rfl]

private theorem difference_le {q : ℕ → ℝ} {A : ℕ → Set ℝ} (h : NestedProfile q A)
    {start k : ℕ} (hk : start ≤ k) :
    volume.real (A start \ A k) ≤ min (q start) (min (1 - q k) (downwardVariation q start k)) := by
  apply le_min
  · rw [← h.marginals start]
    exact measureReal_mono sdiff_subset (h.finite start subset_rfl)
  · apply le_min _ (cumulative_difference h hk)
    have sub : A start \ A k ⊆ Ico (0 : ℝ) 1 \ A k := sdiff_subset_sdiff_left (h.within start)
    have hfin : volume (Ico (0 : ℝ) 1) ≠ ⊤ := by simp
    apply (measureReal_mono sub (measure_ne_top_of_subset sdiff_subset hfin)).trans_eq
    rw [measureReal_sdiff (h.within k) (h.measurable k) hfin, h.marginals]
    norm_num [Real.volume_real_Ico]

def flipProb (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then p k else 1 - p k

def flipEvent (A : ℕ → Set ℝ) (k : ℕ) : Set ℝ :=
  if k % 2 = 0 then A k else Ico 0 1 \ A k

private theorem flipEvent_within {A : ℕ → Set ℝ} (inside : ∀ k, A k ⊆ Ico 0 1) (k : ℕ) :
    flipEvent A k ⊆ Ico 0 1 := by
  unfold flipEvent
  split
  · exact inside k
  · exact sdiff_subset

private theorem flipEvent_twice {A : ℕ → Set ℝ} (inside : ∀ k, A k ⊆ Ico 0 1) :
    flipEvent (flipEvent A) = A := by
  funext k
  by_cases h : k % 2 = 0
  · simp [flipEvent, h]
  · simp [flipEvent, h, sdiff_sdiff_eq_self (inside k)]

private theorem flipProb_twice (p : ℕ → ℝ) : flipProb (flipProb p) = p := by
  funext k
  by_cases h : k % 2 = 0 <;> simp [flipProb, h]

private theorem flipEvent_marginals {A : ℕ → Set ℝ} {p : ℕ → ℝ}
    (hm : ∀ k, MeasurableSet (A k)) (inside : ∀ k, A k ⊆ Ico 0 1)
    (volumeA : ∀ k, volume.real (A k) = p k) (k : ℕ) :
    volume.real (flipEvent A k) = flipProb p k := by
  by_cases h : k % 2 = 0
  · simp [flipEvent, flipProb, h, volumeA]
  · rw [flipEvent, flipProb, ite_eq_right h, ite_eq_right h,
      measureReal_sdiff (inside k) (hm k) (by simp [Real.volume_Ico]), volumeA]
    norm_num [Real.volume_real_Ico]

private theorem flipEvent_measurable {A : ℕ → Set ℝ} (hm : ∀ k, MeasurableSet (A k)) (k : ℕ) :
    MeasurableSet (flipEvent A k) := by
  unfold flipEvent
  split
  · exact hm k
  · exact measurableSet_Ico.diff (hm k)

structure HardCoreProfile (p : ℕ → ℝ) (B : ℕ → Set ℝ) : Prop where
  measurable : ∀ k, MeasurableSet (B k)
  within : ∀ k, B k ⊆ Ico 0 1
  marginals : ∀ k, volume.real (B k) = p k
  adjacent : ∀ k, Disjoint (B k) (B (k + 1))

private theorem hard_core_nested {p : ℕ → ℝ} {B : ℕ → Set ℝ} (h : HardCoreProfile p B) :
    NestedProfile (flipProb p) (flipEvent B) := by
  refine ⟨flipEvent_measurable h.measurable, flipEvent_within h.within,
    flipEvent_marginals h.measurable h.within h.marginals, ?_⟩
  intro k
  by_cases even : k % 2 = 0
  · have next : ¬ (k + 1) % 2 = 0 := by omega
    simp only [flipEvent, even, next, ite_true, ite_false]
    exact Or.inl (fun _ hx => ⟨h.within k hx, fun hy => Set.disjoint_left.mp (h.adjacent k) hx hy⟩)
  · have next : (k + 1) % 2 = 0 := by omega
    simp only [flipEvent, even, next, ite_true, ite_false]
    exact Or.inr (fun _ hy => ⟨h.within _ hy, fun hx => Set.disjoint_left.mp (h.adjacent k) hx hy⟩)

private theorem event_hard_core (p : ℕ → ℝ) (bounds : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    (adjacent : ∀ k, p k + p (k + 1) ≤ 1) (start : ℕ) :
    HardCoreProfile p (flipEvent (event (flipProb p) start)) := by
  let q := flipProb p
  have hq (k : ℕ) : 0 ≤ q k ∧ q k ≤ 1 := by
    simp only [q, flipProb]
    split
    · exact bounds k
    · constructor <;> linarith [(bounds k).1, (bounds k).2]
  have hm (k : ℕ) : MeasurableSet (event q start k) :=
    measurableSet_Ico.union measurableSet_Ico
  have hp := flipEvent_marginals hm (event_subset_unit q hq start) (event_measure q hq start)
  change ∀ k, _ = flipProb (flipProb p) k at hp
  rw [flipProb_twice] at hp
  refine ⟨flipEvent_measurable hm, flipEvent_within (event_subset_unit q hq start), hp, ?_⟩
  intro k
  apply Set.disjoint_left.mpr
  by_cases even : k % 2 = 0
  · have next : ¬ (k + 1) % 2 = 0 := by omega
    have le : q k ≤ q (k + 1) := by
      simp [q, flipProb, even, next]
      linarith [adjacent k]
    simp only [flipEvent, even, next, ite_true, ite_false]
    exact fun _ hx hy => hy.2 ((event_nested q hq start k).1 le hx)
  · have next : (k + 1) % 2 = 0 := by omega
    have le : q (k + 1) ≤ q k := by
      simp [q, flipProb, even, next]
      linarith [adjacent k]
    simp only [flipEvent, even, next, ite_true, ite_false]
    exact fun _ hx hy => hx.2 ((event_nested q hq start k).2 le hy)

theorem sharp_hard_core_difference (p : ℕ → ℝ) (bounds : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    (adjacent : ∀ k, p k + p (k + 1) ≤ 1) (start : ℕ) :
    let q := flipProb p
    (∀ B, HardCoreProfile p B → ∀ k ≥ start,
      volume.real (flipEvent B start \ flipEvent B k) ≤
        min (q start) (min (1 - q k) (downwardVariation q start k))) ∧
    ∃ B, HardCoreProfile p B ∧ ∀ k ≥ start,
      volume.real (flipEvent B start \ flipEvent B k) =
        min (q start) (min (1 - q k) (downwardVariation q start k)) := by
  intro q
  have hq (k : ℕ) : 0 ≤ q k ∧ q k ≤ 1 := by
    simp only [q, flipProb]
    split
    · exact bounds k
    · constructor <;> linarith [(bounds k).1, (bounds k).2]
  refine ⟨fun B h k hk => difference_le (hard_core_nested h) hk,
    flipEvent (event q start), event_hard_core p bounds adjacent start, ?_⟩
  intro k hk
  rw [flipEvent_twice (event_subset_unit q hq start)]
  exact event_sdiff q hq hk

def extendProfile {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then p ⟨k, h⟩ else 0

def wordEvent {n : ℕ} (w : ℝ → Fin n → Bool) (k : Fin n) : Set ℝ :=
  {u | w u k = true}

def orientedDifference {n : ℕ} (w : ℝ → Fin n → Bool) (i j : Fin n) : Set ℝ :=
  {u | u ∈ Ico 0 1 ∧ w u i = decide (i.val % 2 = 0) ∧
    w u j ≠ decide (j.val % 2 = 0)}

theorem word_attainment {n : ℕ} (p : Fin n → ℝ) (bounds : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    (adjacent : ∀ i j, i.val + 1 = j.val → p i + p j ≤ 1) (start : Fin n) :
    let q := flipProb (extendProfile p)
    ∃ w : ℝ → Fin n → Bool, (∀ u, Adm n (w u)) ∧
      (∀ k, MeasurableSet (wordEvent w k) ∧ wordEvent w k ⊆ Ico 0 1 ∧
        volume.real (wordEvent w k) = p k) ∧
      ∀ k : Fin n, start ≤ k →
        volume.real (orientedDifference w start k) =
          min (q start) (min (1 - q k) (downwardVariation q start k)) := by
  classical
  intro q
  have pb : ∀ k, 0 ≤ extendProfile p k ∧ extendProfile p k ≤ 1 := by
    intro k
    unfold extendProfile
    split
    · exact bounds _
    · norm_num
  have pa : ∀ k, extendProfile p k + extendProfile p (k + 1) ≤ 1 := by
    intro k
    by_cases h : k + 1 < n
    · have hk : k < n := by omega
      simpa [extendProfile, h, hk] using adjacent ⟨k, hk⟩ ⟨k + 1, h⟩ rfl
    · simpa [extendProfile, h] using (pb k).2
  obtain ⟨B, hB, attain⟩ := (sharp_hard_core_difference (extendProfile p) pb pa start).2
  let w (u : ℝ) (k : Fin n) : Bool := decide (u ∈ B k)
  have event_eq (k : Fin n) : wordEvent w k = B k := by
    ext u
    simp [wordEvent, w]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro u
    rw [adm_iff_no_adjacent_true]
    intro i j hij
    by_cases hi : u ∈ B i
    · have hj : u ∉ B j := by
        rw [← hij]
        exact fun hj => Set.disjoint_left.mp (hB.adjacent i) hi hj
      exact Or.inr (by simp [w, hj])
    · exact Or.inl (by simp [w, hi])
  · intro k
    rw [event_eq]
    exact ⟨hB.measurable k, hB.within k, by simpa [extendProfile] using hB.marginals k⟩
  · intro j hj
    have eq : orientedDifference w start j = flipEvent B start \ flipEvent B j := by
      ext u
      have h₁ : u ∈ B start → u ∈ Ico 0 1 := fun h => hB.within start h
      have h₂ : u ∈ B j → u ∈ Ico 0 1 := fun h => hB.within j h
      by_cases h : (start : ℕ) % 2 = 0 <;> by_cases h' : (j : ℕ) % 2 = 0 <;>
        simp only [orientedDifference, mem_ofPred_eq, w, h, h', decide_true, decide_false,
          ne_eq, decide_eq_true_eq, decide_eq_false_iff_not, not_not, flipEvent, ite_true,
          ite_false, mem_sdiff] <;> tauto
    rw [eq]
    exact attain j hj

end D5.S1.Words.AdmissibleWords.FIBPathPairBounds
