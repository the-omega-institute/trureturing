/- GID: D5/S0/Computability/Coding/RetainedDepthExactImage
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/RetainedDepthExactImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local complete-bundle cuts characterize the exact image of depth-budget codes. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Mathlib.Order.Partition.Finpartition

open scoped BigOperators

namespace D5.S0.Computability.Coding.RetainedDepthExactImage

open PrefixFreeCode DepthBudgetIidGreedyOptimality

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A retained sequence starts at zero, increases strictly, and is unbounded. -/
def Retained (s : ℕ → ℕ) : Prop :=
  s 0 = 0 ∧ StrictMono s ∧ ∀ n, ∃ j, n ≤ s j

/-- The first retained depth not less than a requested depth. -/
noncomputable def firstDepth (s : ℕ → ℕ) (h : Retained s) (n : ℕ) : ℕ :=
  s (Nat.find (h.2.2 n))

/-- The full descendant expansion, including every suffix at the first retained depth. -/
def expansion (s : ℕ → ℕ) (h : Retained s) (F : Set (List A)) : Set (List A) :=
  {g | ∃ w ∈ F, w <+: g ∧ g.length = firstDepth s h w.length}

/-- Segment j is the half-open interval (s j, s (j+1)]. -/
def Band (s : ℕ → ℕ) (j : ℕ) (w : List A) : Prop :=
  s j < w.length ∧ w.length ≤ s (j + 1)

/-- Every descendant at the specified depth belongs to the target code. -/
def Bundle (G : Set (List A)) (r : ℕ) (w : List A) : Prop :=
  ∀ g, g.length = r → w <+: g → g ∈ G

/-- Available ancestors have the entire descendant bundle inside the target level. -/
noncomputable def available (s : ℕ → ℕ) (G : Set (List A)) (j : ℕ) :
    Finset (List A) := by
  classical
  exact ((Finset.range (s (j + 1) + 1)).biUnion (words (α := A))).filter
    (fun w => Band s j w ∧ Bundle G (s (j + 1)) w)

/-- The two finite systems of leaf-cover and depth-budget equations. -/
noncomputable def Equations (s : ℕ → ℕ) (G : Set (List A)) (b : ℕ → ℕ)
    (j : ℕ) (x : List A → Bool) : Prop := by
  classical
  exact (∀ g ∈ G, g.length = s (j + 1) →
    ∑ w ∈ (available s G j).filter (fun w => w <+: g),
      (if x w then 1 else 0 : ℕ) = 1) ∧
    (∀ n, s j < n → n ≤ s (j + 1) →
      ∑ w ∈ (available s G j).filter (fun w => w.length = n),
        (if x w then 1 else 0 : ℕ) ≤ b n)

private theorem mem_words (w : List A) (n : ℕ) : w ∈ words n ↔ w.length = n := by
  classical
  simp [words, List.Vector, Subtype.exists]

private theorem mem_level (F : Set (List A)) (n : ℕ) (w : List A) :
    w ∈ level F n ↔ w.length = n ∧ w ∈ F := by
  classical
  simp [level, mem_words]

private theorem mem_available (s : ℕ → ℕ) (G : Set (List A)) (j : ℕ) (w : List A) :
    w ∈ available s G j ↔ Band s j w ∧ Bundle G (s (j + 1)) w := by
  classical
  simp only [available, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, mem_words]
  exact ⟨fun h => h.2, fun h => ⟨⟨w.length, by have := h.1.2; omega, rfl⟩, h⟩⟩

private theorem band_unique (s : ℕ → ℕ) (hs : StrictMono s) (w : List A)
    {j k : ℕ} (hj : Band s j w) (hk : Band s k w) : j = k := by
  rcases lt_trichotomy j k with hjk | he | hkj
  · have := hs.monotone (Nat.succ_le_of_lt hjk)
    obtain ⟨_, _⟩ := hj
    obtain ⟨_, _⟩ := hk
    omega
  · exact he
  · have := hs.monotone (Nat.succ_le_of_lt hkj)
    obtain ⟨_, _⟩ := hj
    obtain ⟨_, _⟩ := hk
    omega

private theorem positive_has_band (s : ℕ → ℕ) (h : Retained s) (n : ℕ)
    (hn : 0 < n) : ∃ j, s j < n ∧ n ≤ s (j + 1) := by
  classical
  let k := Nat.find (h.2.2 n)
  have hk : n ≤ s k := Nat.find_spec (h.2.2 n)
  have hkpos : 0 < k := by
    by_contra hh
    have : k = 0 := by omega
    simpa [this, h.1] using hk
  refine ⟨k - 1, ?_, ?_⟩
  · exact Nat.lt_of_not_ge (Nat.find_min (h.2.2 n) (by dsimp [k]; omega))
  · simpa [Nat.sub_add_cancel hkpos] using hk

private theorem firstDepth_eq (s : ℕ → ℕ) (h : Retained s) {j n : ℕ}
    (hl : s j < n) (hr : n ≤ s (j + 1)) : firstDepth s h n = s (j + 1) := by
  classical
  unfold firstDepth
  congr 1
  apply (Nat.find_eq_iff (h.2.2 n)).mpr
  refine ⟨hr, ?_⟩
  intro k hk hn
  have := h.2.1.monotone (show k ≤ j by omega)
  omega

/-- A finite segment cut has complete bundles, unique leaf coverage, and the original budgets. -/
private def Cut (s : ℕ → ℕ) (G : Set (List A)) (b : ℕ → ℕ) (j : ℕ)
    (C : Finset (List A)) : Prop :=
  (∀ w ∈ C, Band s j w ∧ Bundle G (s (j + 1)) w) ∧
  (∀ g ∈ G, g.length = s (j + 1) → ∃! w, w ∈ C ∧ w <+: g) ∧
  (∀ n, s j < n → n ≤ s (j + 1) → (level (C : Set (List A)) n).card ≤ b n)

private theorem cross_no_prefix (s : ℕ → ℕ) (hs : StrictMono s)
    (G : Set (List A)) (hG : IsPrefixFree G) (a : A) {j k : ℕ} (hjk : j < k)
    {w v : List A} (hw : Band s j w) (hv : Band s k v)
    (bw : Bundle G (s (j + 1)) w) (bv : Bundle G (s (k + 1)) v) : ¬ w <+: v := by
  intro hwv
  let t := v.take (s (j + 1))
  let g := v ++ List.replicate (s (k + 1) - v.length) a
  have hrv : s (j + 1) < v.length :=
    lt_of_le_of_lt (hs.monotone (Nat.succ_le_of_lt hjk)) hv.1
  have htlen : t.length = s (j + 1) := by simp [t, List.length_take, hrv.le]
  have hglen : g.length = s (k + 1) := by simp [g]; omega
  have hwt : w <+: t := List.prefix_of_prefix_length_le hwv
    (List.take_prefix _ _) (by rw [htlen]; exact hw.2)
  have htG := bw t htlen hwt
  have hgG := bv g hglen (List.prefix_append _ _)
  have htg : t <+: g := (List.take_prefix _ _).trans (List.prefix_append _ _)
  have he := congrArg List.length (hG htG hgG htg)
  have hrr := hs (Nat.succ_lt_succ hjk)
  omega

end D5.S0.Computability.Coding.RetainedDepthExactImage
