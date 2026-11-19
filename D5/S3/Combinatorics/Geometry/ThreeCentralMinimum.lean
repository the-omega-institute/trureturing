/- GID: D5/S3/Combinatorics/Geometry/ThreeCentralMinimum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/ThreeCentralMinimum
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For n ≥ 4 the least central-edge count of a three-central n-point metric is 2⌈n/2⌉. -/

import D5.S3.Combinatorics.Geometry.CentralEdgeCover

/-! # The sharp three-central minimum

For every `n ≥ 4`, every three-central metric space on `n` points has at least `2 ⌈n / 2⌉`
central edges, and a narrow-band metric on `Fin n` attains this count: two pair classes, each
covering every point with `⌈n / 2⌉` pairs, receive the distances `1` and `2`, and every other
pair receives its own distance strictly between `1` and `2`.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.ThreeCentralMinimum

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover

noncomputable section

variable (N : ℕ)

/-- The pairs `{2k, 2k+1}`, closed by `{0, n-1}` when `n` is odd. -/
private def fA (k : ℕ) : Sym2 (Fin (N + 4)) :=
  if h : 2 * k + 1 < N + 4 then s(⟨2 * k, by omega⟩, ⟨2 * k + 1, h⟩)
  else s(⟨0, by omega⟩, ⟨N + 3, by omega⟩)

/-- The pairs `{2k+1, 2k+2}`, closed by `{0, n-1}` for even `n` and `{0, 2}` for odd `n`. -/
private def fB (k : ℕ) : Sym2 (Fin (N + 4)) :=
  if h : 2 * k + 2 < N + 4 then s(⟨2 * k + 1, by omega⟩, ⟨2 * k + 2, h⟩)
  else if N % 2 = 0 then s(⟨0, by omega⟩, ⟨N + 3, by omega⟩)
  else s(⟨0, by omega⟩, ⟨2, by omega⟩)

/-- Number of pairs in each class: `⌈n / 2⌉`. -/
private abbrev half : ℕ := (N + 4 + 1) / 2

private def SA : Finset (Sym2 (Fin (N + 4))) := (Finset.range (half N)).image (fA N)

private def SB : Finset (Sym2 (Fin (N + 4))) := (Finset.range (half N)).image (fB N)

private lemma disjoint_AB : Disjoint (SA N) (SB N) := by
  rw [Finset.disjoint_left]
  intro e hA hB
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hB
  simp only [Finset.mem_range, half] at hj hk
  revert hk'
  unfold fA fB
  split_ifs <;> simp [Fin.ext_iff] <;> omega

private lemma cover_A (x : Fin (N + 4)) : ∃ y, y ≠ x ∧ s(x, y) ∈ SA N := by
  obtain ⟨i, hi⟩ := x
  by_cases h1 : i % 2 = 1
  · refine ⟨⟨i - 1, by omega⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
      Finset.mem_image.mpr ⟨i / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
    unfold fA; split_ifs <;> simp [Fin.ext_iff] <;> omega
  · by_cases h2 : i + 1 < N + 4
    · refine ⟨⟨i + 1, h2⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
        Finset.mem_image.mpr ⟨i / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
      unfold fA; split_ifs <;> simp [Fin.ext_iff] <;> omega
    · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
        Finset.mem_image.mpr ⟨i / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
      unfold fA; split_ifs <;> simp [Fin.ext_iff] <;> omega

private lemma cover_B (x : Fin (N + 4)) : ∃ y, y ≠ x ∧ s(x, y) ∈ SB N := by
  obtain ⟨i, hi⟩ := x
  by_cases h0 : i = 0
  · subst h0
    by_cases hN : N % 2 = 0
    · refine ⟨⟨N + 3, by omega⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
        Finset.mem_image.mpr ⟨(N + 4) / 2 - 1, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
      unfold fB; split_ifs <;> simp [Fin.ext_iff]
      omega
    · refine ⟨⟨2, by omega⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
        Finset.mem_image.mpr ⟨(N + 3) / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
      unfold fB; split_ifs <;> simp [Fin.ext_iff]
      omega
  · by_cases h1 : i % 2 = 0
    · refine ⟨⟨i - 1, by omega⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
        Finset.mem_image.mpr ⟨(i - 2) / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
      unfold fB; split_ifs <;> simp [Fin.ext_iff] <;> omega
    · by_cases h2 : i + 1 < N + 4
      · refine ⟨⟨i + 1, h2⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
          Finset.mem_image.mpr ⟨i / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
        unfold fB; split_ifs <;> simp [Fin.ext_iff] <;> omega
      · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.mk.injEq]; omega,
          Finset.mem_image.mpr ⟨i / 2, by simp only [Finset.mem_range, half]; omega, ?_⟩⟩
        unfold fB; split_ifs <;> simp [Fin.ext_iff] <;> omega

private lemma cover_A' (x : Fin (N + 4)) : ∃ y, y ≠ x ∧ s(y, x) ∈ SA N := by
  obtain ⟨y, h1, h2⟩ := cover_A N x
  exact ⟨y, h1, by rw [Sym2.eq_swap]; exact h2⟩

private lemma cover_B' (x : Fin (N + 4)) : ∃ y, y ≠ x ∧ s(y, x) ∈ SB N := by
  obtain ⟨y, h1, h2⟩ := cover_B N x
  exact ⟨y, h1, by rw [Sym2.eq_swap]; exact h2⟩

/-- A code of the unordered pair, between `1` and `n ^ 2`. -/
private def code (x y : Fin (N + 4)) : ℕ := (N + 4) * min x.1 y.1 + max x.1 y.1 + 1

/-- The narrow-band distance: `1` on the first class, `2` on the second, and a distinct value
strictly between `1` and `2` on every other pair. -/
private def d (x y : Fin (N + 4)) : ℝ :=
  if x = y then 0 else if s(x, y) ∈ SA N then 1 else if s(x, y) ∈ SB N then 2
  else 1 + (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ)

private lemma d_self (x : Fin (N + 4)) : d N x x = 0 := by
  unfold d
  simp only [↓reduceIte]

private lemma code_comm (x y : Fin (N + 4)) : code N x y = code N y x := by
  unfold code; rw [min_comm, max_comm]

private lemma code_pos (x y : Fin (N + 4)) : 0 < code N x y := by unfold code; omega

private lemma code_le (x y : Fin (N + 4)) : code N x y ≤ (N + 4) * (N + 4) := by
  unfold code
  have h1 : min x.1 y.1 ≤ N + 3 := by have := x.2; omega
  have h2 : max x.1 y.1 ≤ N + 3 := by have := x.2; have := y.2; omega
  have := Nat.mul_le_mul_left (N + 4) h1
  nlinarith

private lemma code_inj (x y x' y' : Fin (N + 4)) (h : code N x y = code N x' y') :
    s(x, y) = s(x', y') := by
  unfold code at h
  have hb : max x.1 y.1 < N + 4 := by have := x.2; have := y.2; omega
  have hb' : max x'.1 y'.1 < N + 4 := by have := x'.2; have := y'.2; omega
  have h' : (N + 4) * min x.1 y.1 + max x.1 y.1 = (N + 4) * min x'.1 y'.1 + max x'.1 y'.1 := by
    omega
  have hmin : min x.1 y.1 = min x'.1 y'.1 := by
    have := congrArg (· / (N + 4)) h'
    simp only [Nat.mul_add_div (show 0 < N + 4 by omega), Nat.div_eq_of_lt hb,
      Nat.div_eq_of_lt hb', add_zero] at this
    exact this
  have hmax : max x.1 y.1 = max x'.1 y'.1 := by rw [hmin] at h'; omega
  rw [Sym2.eq_iff]
  simp only [Fin.ext_iff]
  omega

private lemma d_comm (x y : Fin (N + 4)) : d N x y = d N y x := by
  unfold d
  rw [Sym2.eq_swap, code_comm]
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h]

private lemma d_bounds {x y : Fin (N + 4)} (h : x ≠ y) : 1 ≤ d N x y ∧ d N x y ≤ 2 := by
  unfold d
  have hc := code_le N x y
  have hM : (0 : ℝ) < (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) := by positivity
  have hle : (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hM]; exact_mod_cast (by omega : code N x y ≤ (N + 4) * (N + 4) + 1)
  have hge : 0 ≤ (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) := by positivity
  simp only [h, ↓reduceIte]
  split_ifs <;> constructor <;> linarith

/-- On a pair outside both classes the distance lies strictly between `1` and `2`. -/
private lemma d_other {x y : Fin (N + 4)} (h : x ≠ y) (hA : s(x, y) ∉ SA N)
    (hB : s(x, y) ∉ SB N) :
    d N x y = 1 + (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) ∧
      1 < d N x y ∧ d N x y < 2 := by
  have hM : (0 : ℝ) < (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) := by positivity
  have hpos : 0 < (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) :=
    div_pos (by exact_mod_cast code_pos N x y) hM
  have hlt : (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one hM]; exact_mod_cast (by have := code_le N x y; omega)
  have he : d N x y = 1 + (code N x y : ℝ) / (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) := by
    unfold d; simp only [h, hA, hB, ↓reduceIte]
  exact ⟨he, by linarith, by linarith⟩

/-- The point set `Fin n` with the narrow-band metric. -/
def Space : Type := Fin (N + 4)

instance : Fintype (Space N) := inferInstanceAs (Fintype (Fin (N + 4)))

instance : DecidableEq (Space N) := inferInstanceAs (DecidableEq (Fin (N + 4)))

noncomputable instance : MetricSpace (Space N) where
  dist x y := d N x y
  dist_self x := d_self N x
  dist_comm x y := d_comm N x y
  dist_triangle x y z := by
    show d N x z ≤ d N x y + d N y z
    by_cases hxz : x = z
    · subst hxz
      have : d N x x = 0 := d_self N x
      rw [this]
      by_cases hxy : x = y
      · subst hxy; rw [this]; norm_num
      · have := (d_bounds N hxy).1; have := (d_bounds N (Ne.symm hxy)).1; linarith
    · have h1 := (d_bounds N hxz).2
      by_cases hxy : x = y
      · subst hxy
        have : d N x x = 0 := d_self N x
        rw [this, zero_add]
      · by_cases hyz : y = z
        · subst hyz
          have : d N y y = 0 := d_self N y
          rw [this, add_zero]
        · have := (d_bounds N hxy).1; have := (d_bounds N hyz).1; linarith
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    have := (d_bounds N hne).1
    change d N x y = 0 at h
    linarith


private lemma one_mem (p : Space N) : ∃ y : Space N, dist y p = 1 := by
  obtain ⟨y, hne, hy⟩ := cover_A' N p
  refine ⟨(y : Space N), ?_⟩
  change d N y p = 1
  unfold d
  simp only [hne, hy, ↓reduceIte]

private lemma two_mem (p : Space N) : ∃ y : Space N, dist y p = 2 := by
  obtain ⟨y, hne, hy⟩ := cover_B' N p
  refine ⟨(y : Space N), ?_⟩
  change d N y p = 2
  unfold d
  have hA : s(y, p) ∉ SA N := fun h => Finset.disjoint_left.mp (disjoint_AB N) h hy
  simp only [hne, hA, hy, ↓reduceIte]

private lemma center_eq : center (Space N) = {0, 1, 2} := by
  ext t
  simp only [center, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ht0, ht⟩
    by_contra hne
    push Not at hne
    obtain ⟨h0, h1, h2⟩ := hne
    -- a partner of the point 0
    obtain ⟨y0, hy0⟩ := ht (⟨0, by omega⟩ : Fin (N + 4))
    change d N y0 ⟨0, by omega⟩ = t at hy0
    have hy0ne : y0 ≠ (⟨0, by omega⟩ : Fin (N + 4)) := by
      intro h; rw [h, d_self] at hy0; exact h0 hy0.symm
    have other : ∀ x y : Fin (N + 4), x ≠ y → d N x y = t →
        s(x, y) ∉ SA N ∧ s(x, y) ∉ SB N := by
      intro x y hxy hd
      constructor
      · intro hA; unfold d at hd; simp only [hxy, hA, ↓reduceIte] at hd; exact h1 hd.symm
      · intro hB
        have hA : s(x, y) ∉ SA N := fun hA => by
          unfold d at hd; simp only [hxy, hA, ↓reduceIte] at hd; exact h1 hd.symm
        unfold d at hd; simp only [hxy, hA, hB, ↓reduceIte] at hd; exact h2 hd.symm
    obtain ⟨oA, oB⟩ := other y0 _ hy0ne hy0
    -- a third point
    obtain ⟨z, hz0, hzy⟩ : ∃ z : Fin (N + 4),
        z ≠ (⟨0, by omega⟩ : Fin (N + 4)) ∧ z ≠ y0 := by
      by_cases h : y0 = ⟨1, by omega⟩
      · exact ⟨⟨2, by omega⟩, by simp [Fin.ext_iff], by rw [h]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨1, by omega⟩, by simp, Ne.symm h⟩
    obtain ⟨w, hw⟩ := ht z
    change d N w z = t at hw
    have hwz : w ≠ z := by intro h; rw [h, d_self] at hw; exact h0 hw.symm
    obtain ⟨wA, wB⟩ := other w z hwz hw
    have e1 := (d_other N hy0ne oA oB).1
    have e2 := (d_other N hwz wA wB).1
    have hcode : code N w z = code N y0 ⟨0, by omega⟩ := by
      have hM : (0 : ℝ) < (((N + 4) * (N + 4) + 1 : ℕ) : ℝ) := by positivity
      have : (code N w z : ℝ) = code N y0 ⟨0, by omega⟩ := by
        have := hw.trans hy0.symm
        rw [e1, e2] at this
        field_simp at this
        linarith
      exact_mod_cast this
    have hs := Sym2.eq_iff.mp (code_inj N w z y0 ⟨0, by omega⟩ hcode)
    rcases hs with ⟨_, h⟩ | ⟨_, h⟩
    · exact hz0 h
    · exact hzy h
  · rintro (rfl | rfl | rfl)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · exact ⟨zero_le_one, one_mem N⟩
    · exact ⟨zero_le_two, two_mem N⟩

private lemma center_card : Nat.card (center (Space N)) = 3 := by
  rw [center_eq, Nat.card_coe_set_eq]
  exact Set.ncard_eq_three.mpr ⟨0, 1, 2, by norm_num, by norm_num, by norm_num, rfl⟩

open Classical in
private lemma edges_le : (centralGraph (Space N)).edgeFinset.card ≤ 2 * half N := by
  have hsub : (centralGraph (Space N)).edgeFinset ⊆ SA N ∪ SB N := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      simp only [centralGraph, SimpleGraph.fromRel_adj] at he
      obtain ⟨hxy, hc⟩ := he
      have hc' : d N x y ∈ center (Space N) := by
        rcases hc with h | h
        · exact h
        · rw [show d N x y = dist y x from (d_comm N x y).trans rfl]; exact h
      rw [center_eq] at hc'
      by_contra hn
      have hn1 : s(x, y) ∉ SA N := fun h => hn (Finset.mem_union_left _ h)
      have hn2 : s(x, y) ∉ SB N := fun h => hn (Finset.mem_union_right _ h)
      obtain ⟨_, hlt1, hlt2⟩ := d_other N hxy hn1 hn2
      have h0 := (d_bounds N hxy).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc'
      rcases hc' with h | h | h <;> linarith
  calc (centralGraph (Space N)).edgeFinset.card ≤ (SA N ∪ SB N).card := Finset.card_le_card hsub
    _ ≤ (SA N).card + (SB N).card := Finset.card_union_le _ _
    _ ≤ half N + half N := Nat.add_le_add
        (Finset.card_image_le.trans (Finset.card_range _).le)
        (Finset.card_image_le.trans (Finset.card_range _).le)
    _ = 2 * half N := by ring

open Classical in
/-- For every `n ≥ 4`, every three-central metric space on `n` points has at least
`2 ⌈n / 2⌉` central edges, and some three-central metric space on `n` points has exactly
`2 ⌈n / 2⌉` central edges. -/
theorem three_central_minimum (n : ℕ) (hn : 4 ≤ n) :
    (∀ (X : Type) [Fintype X] [MetricSpace X], Fintype.card X = n →
      Nat.card (center X) = 3 → 2 * ((n + 1) / 2) ≤ (centralGraph X).edgeFinset.card) ∧
    ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), Fintype.card X = n ∧
      Nat.card (center X) = 3 ∧ (centralGraph X).edgeFinset.card = 2 * ((n + 1) / 2) := by
  refine ⟨fun X _ _ hX hk => ?_, ?_⟩
  · have := edge_cover_bound X
    rw [hk, hX] at this
    simpa using this
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
    refine ⟨Space N, inferInstance, inferInstance, ?_, center_card N, ?_⟩
    · exact Fintype.card_fin (N + 4)
    · apply le_antisymm (edges_le N)
      have := edge_cover_bound (Space N)
      rw [center_card N, show Fintype.card (Space N) = N + 4 from Fintype.card_fin _] at this
      simpa using this

end

end D5.S3.Combinatorics.Geometry.ThreeCentralMinimum
