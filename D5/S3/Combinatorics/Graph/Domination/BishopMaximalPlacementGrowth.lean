/- GID: D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth
   mirror-E: none(waiver:unbounded-asymptotic-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.claim; result=D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.result; claim=D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.claim
   digest: Native maximal bishop subsets on fixed coordinate square boards. -/

import D5.S3.Combinatorics.Graph.Domination.FiniteLinePrefixCount
import D5.S3.Geometry.FiniteGraphSubgraphSuspensionConstruction
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth

open Finset
open scoped BigOperators
open D5.S3.Geometry.FiniteGraphSubgraphSuspension
open FiniteLinePrefixCount

abbrev Cell (n : ℕ) := Fin n × Fin n

/-- Signed differences are integers, including negative diagonals. -/
def difference {n : ℕ} (p : Cell n) : ℤ := (p.1.val : ℤ) - p.2.val

def diagonalSum {n : ℕ} (p : Cell n) : ℤ := (p.1.val : ℤ) + p.2.val

/-- Both diagonal directions on the actual fixed-coordinate board. -/
def bishopGraph (n : ℕ) : SimpleGraph (Cell n) where
  Adj p q := p ≠ q ∧ (difference p = difference q ∨ diagonalSum p = diagonalSum q)
  symm := by intro p q h; exact ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  loopless := by intro p h; exact h.1 rfl

/-- Unordered subsets maximal under inclusion, using the frozen native supplier. -/
abbrev Placement (n : ℕ) := MaxIndependent (bishopGraph n)

/-- The n=0 value is a total convention, outside the source's offset one. -/
def count (n : ℕ) : ℕ := Fintype.card (Placement n)

/-- The literal positive-constant eventual upper bound in A146304. -/
def claim : Prop := ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
  ∀ n : ℕ, N ≤ n → (count n : ℝ) ≤ C * (n : ℝ) ^ (n - 1)


private theorem independent_difference_injective {n : ℕ} (M : Placement n) :
    Set.InjOn difference (M.val : Set (Cell n)) := by
  intro p hp q hq hd
  by_contra hne
  exact M.property.1 hp hq hne ⟨hne, Or.inl hd⟩

/-- The source's physical cap holds for all n at least two. -/
theorem physical_cap {n : ℕ} (hn : 2 ≤ n) (M : Placement n) : M.val.card ≤ 2 * n - 2 := by
  classical
  let a : Cell n := (⟨0, by omega⟩, ⟨n - 1, by omega⟩)
  let b : Cell n := (⟨n - 1, by omega⟩, ⟨0, by omega⟩)
  have hab : a ≠ b := by
    intro he
    have := congrArg (fun p : Cell n => p.1.val) he
    dsimp [a, b] at this
    omega
  have hsum : diagonalSum a = diagonalSum b := by simp [diagonalSum, a, b]
  have hnot : a ∉ M.val ∨ b ∉ M.val := by
    by_contra h
    push_neg at h
    exact M.property.1 h.1 h.2 hab ⟨hab, Or.inr hsum⟩
  let idx : Cell n → ℕ := fun p => p.1.val + (n - 1 - p.2.val)
  have hinj : Set.InjOn idx (M.val : Set (Cell n)) := by
    intro p hp q hq he
    apply independent_difference_injective M hp hq
    have hp1 := p.1.isLt
    have hp2 := p.2.isLt
    have hq1 := q.1.isLt
    have hq2 := q.2.isLt
    dsimp [idx] at he
    unfold difference
    omega
  rcases hnot with ha | hb
  · have hmap : Set.MapsTo idx (M.val : Set (Cell n)) (Finset.Icc 1 (2 * n - 2) : Set ℕ) := by
      intro p hp
      have hx := p.1.isLt
      have hy := p.2.isLt
      have hpa : p ≠ a := by intro he; exact ha (he ▸ hp)
      have hpos : 1 ≤ idx p := by
        by_contra h
        have hpzero : p.1.val = 0 := by dsimp [idx] at h; omega
        have hpy : p.2.val = n - 1 := by dsimp [idx] at h; omega
        apply hpa
        apply Prod.ext <;> apply Fin.ext <;> assumption
      exact mem_Icc.mpr ⟨hpos, by dsimp [idx]; omega⟩
    have hc := Finset.card_le_card_of_injOn idx hmap hinj
    simpa using hc
  · have hmap : Set.MapsTo idx (M.val : Set (Cell n)) (Finset.range (2 * n - 2) : Set ℕ) := by
      intro p hp
      have hx := p.1.isLt
      have hy := p.2.isLt
      have hpb : p ≠ b := by intro he; exact hb (he ▸ hp)
      apply mem_range.mpr
      by_contra h
      have hpx : p.1.val = n - 1 := by dsimp [idx] at h; omega
      have hpzero : p.2.val = 0 := by dsimp [idx] at h; omega
      apply hpb
      apply Prod.ext <;> apply Fin.ext <;> assumption
    have hc := Finset.card_le_card_of_injOn idx hmap hinj
    simpa using hc

/-- The source cap, with its one-square boundary, leaves the native family unchanged. -/
def sourceFamily (n : ℕ) : Finset (Placement n) := by
  classical
  exact univ.filter (fun M => 2 ≤ n → M.val.card ≤ 2 * n - 2)

theorem source_family_card (n : ℕ) : (sourceFamily n).card = count n := by
  classical
  have hall : ∀ M : Placement n, 2 ≤ n → M.val.card ≤ 2 * n - 2 :=
    fun M hn => physical_cap hn M
  simp [sourceFamily, count, hall]

private theorem cell_eq_of_diagonals {n : ℕ} {p q : Cell n}
    (hd : difference p = difference q) (hs : diagonalSum p = diagonalSum q) : p = q := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [difference, diagonalSum] at hd hs <;> omega

/-- The signed labels list each parity's noncentral lines by increasing length. -/
def label (m : ℕ) (c : Fin 2) (h : ℕ) : ℤ :=
  if h % 2 = 0 then ((4 * m : ℕ) : ℤ) - ((2 * (h / 2) + c.val : ℕ) : ℤ)
  else -(((4 * m : ℕ) : ℤ) - ((2 * (h / 2) + c.val : ℕ) : ℤ))

def line (m : ℕ) (c : Fin 2) (j : ℕ) : Finset (Cell (4 * m + 1)) :=
  univ.filter (fun p => difference p = label m c (m + j))

private theorem line_sum_injective (m : ℕ) (c : Fin 2) (j : ℕ) :
    Set.InjOn diagonalSum (line m c j) := by
  intro p hp q hq hs
  exact cell_eq_of_diagonals ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) hs

private theorem label_injective {m : ℕ} (c : Fin 2) {h k : ℕ}
    (hh : h < 4 * m) (hk : k < 4 * m) (he : label m c h = label m c k) : h = k := by
  have hc := c.isLt
  unfold label at he
  split_ifs at he <;> omega

private theorem label_parity (m : ℕ) (c : Fin 2) (h : ℕ) :
    label m c h % 2 = c.val := by
  have hc := c.isLt
  unfold label
  split_ifs <;> omega

private def point (m : ℕ) (c : Fin 2) (h : ℕ) (hh : h < 4 * m)
    (t : Fin (2 * (h / 2) + c.val + 1)) : Cell (4 * m + 1) := by
  let a := 4 * m - (2 * (h / 2) + c.val)
  have hc := c.isLt
  have ht := t.isLt
  have hbound : t.val + a < 4 * m + 1 := by dsimp [a]; omega
  have htbound : t.val < 4 * m + 1 := by omega
  exact if h % 2 = 0 then (⟨t.val + a, hbound⟩, ⟨t.val, htbound⟩)
    else (⟨t.val, htbound⟩, ⟨t.val + a, hbound⟩)

private theorem point_difference (m : ℕ) (c : Fin 2) (h : ℕ) (hh : h < 4 * m)
    (t : Fin (2 * (h / 2) + c.val + 1)) :
    difference (point m c h hh t) = label m c h := by
  have hc := c.isLt
  simp only [point, difference, label]
  split_ifs <;> simp only [Nat.cast_add] <;> omega

private theorem point_injective (m : ℕ) (c : Fin 2) (h : ℕ) (hh : h < 4 * m) :
    Function.Injective (point m c h hh) := by
  intro t u he
  apply Fin.ext
  unfold point at he
  split_ifs at he
  · have := congrArg (fun p : Cell (4 * m + 1) => p.2.val) he
    exact this
  · have := congrArg (fun p : Cell (4 * m + 1) => p.1.val) he
    exact this

private theorem line_card_lower {m : ℕ} (c : Fin 2) {j : ℕ} (hj : j < 3 * m) :
    m + j ≤ (line m c j).card := by
  have hh : m + j < 4 * m := by omega
  have hc := c.isLt
  let f : Fin (2 * ((m + j) / 2) + c.val + 1) → ↥(line m c j) :=
    fun t => ⟨point m c (m + j) hh t, mem_filter.mpr ⟨mem_univ _, point_difference m c (m + j) hh t⟩⟩
  have hf : Function.Injective f := by
    intro t u he
    exact point_injective m c (m + j) hh (congrArg Subtype.val he)
  have hb := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hb
  omega

/-- Actual legal choices on the same 3m prescribed lines of one color. -/
abbrev ColorSeed (m : ℕ) (c : Fin 2) := Prefix (line m c) diagonalSum (3 * m)

private theorem color_seed_card (m : ℕ) (c : Fin 2) :
    m ^ (3 * m) ≤ Fintype.card (ColorSeed m c) := by
  exact card_prefix_lower_bound (line m c) diagonalSum (line_sum_injective m c) m (3 * m)
    (fun j hj => line_card_lower c hj)


/-- The two colors are choices on one common board. -/
abbrev Seed (m : ℕ) := (c : Fin 2) → ColorSeed m c

private def seedSet {m : ℕ} (s : Seed m) : Finset (Cell (4 * m + 1)) :=
  univ.biUnion (fun c => univ.image (s c).val)

private theorem mem_seedSet {m : ℕ} (s : Seed m) (c : Fin 2) (i : Fin (3 * m)) :
    (s c).val i ∈ seedSet s := by
  classical
  exact mem_biUnion.mpr ⟨c, mem_univ _, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩

private theorem seed_difference {m : ℕ} (s : Seed m) (c : Fin 2) (i : Fin (3 * m)) :
    difference ((s c).val i) = label m c (m + i.val) :=
  (mem_filter.mp ((s c).property.1 i)).2

private theorem sum_difference_parity {n : ℕ} (p : Cell n) :
    diagonalSum p % 2 = difference p % 2 := by
  unfold diagonalSum difference
  omega

private theorem seed_sum_parity {m : ℕ} (s : Seed m) (c : Fin 2) (i : Fin (3 * m)) :
    diagonalSum ((s c).val i) % 2 = c.val := by
  rw [sum_difference_parity, seed_difference, label_parity]

private theorem seed_independent {m : ℕ} (s : Seed m) :
    (bishopGraph (4 * m + 1)).IsIndepSet (seedSet s : Set (Cell (4 * m + 1))) := by
  classical
  intro p hp q hq hpq hadj
  obtain ⟨c, _, hp⟩ := mem_biUnion.mp hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  obtain ⟨d, _, hq⟩ := mem_biUnion.mp hq
  obtain ⟨j, _, rfl⟩ := mem_image.mp hq
  rcases hadj.2 with hd | hs
  · by_cases hcd : c = d
    · subst d
      have he := label_injective c (by have := i.isLt; omega) (by have := j.isLt; omega)
        ((seed_difference s c i).symm.trans (hd.trans (seed_difference s c j)))
      have hij : i = j := by apply Fin.ext; omega
      exact hpq (congrArg (s c).val hij)
    · have he := congrArg (fun z : ℤ => z % 2) hd
      rw [seed_difference, seed_difference, label_parity, label_parity] at he
      exact hcd (Fin.ext (by exact_mod_cast he))
  · by_cases hcd : c = d
    · subst d
      have hij := (s c).property.2 hs
      exact hpq (congrArg (s c).val hij)
    · have he := congrArg (fun z : ℤ => z % 2) hs
      rw [seed_sum_parity, seed_sum_parity] at he
      exact hcd (Fin.ext (by exact_mod_cast he))

private def completion {m : ℕ} (s : Seed m) : Placement (4 * m + 1) :=
  Classical.choose (maximal_extension (bishopGraph (4 * m + 1)) (seedSet s) (seed_independent s))

private theorem seed_subset_completion {m : ℕ} (s : Seed m) : seedSet s ⊆ (completion s).val :=
  Classical.choose_spec (maximal_extension (bishopGraph (4 * m + 1)) (seedSet s) (seed_independent s))

private theorem completion_injective (m : ℕ) : Function.Injective (@completion m) := by
  intro s t he
  funext c
  apply Subtype.ext
  funext i
  have hp := seed_subset_completion s (mem_seedSet s c i)
  have hq := seed_subset_completion t (mem_seedSet t c i)
  rw [← he] at hq
  by_contra hne
  exact (completion s).property.1 hp hq hne
    ⟨hne, Or.inl ((seed_difference s c i).trans (seed_difference t c i).symm)⟩

/-- Every seed has a distinct maximal completion, regardless of completion choices. -/
theorem count_lower_bound (m : ℕ) : m ^ (6 * m) ≤ count (4 * m + 1) := by
  classical
  have h0 := color_seed_card m (0 : Fin 2)
  have h1 := color_seed_card m (1 : Fin 2)
  calc
    m ^ (6 * m) = m ^ (3 * m) * m ^ (3 * m) := by rw [← pow_add]; congr 1 <;> omega
    _ ≤ Fintype.card (ColorSeed m 0) * Fintype.card (ColorSeed m 1) := Nat.mul_le_mul h0 h1
    _ = Fintype.card (Seed m) := by simp [Seed, Fintype.card_pi, Fin.prod_univ_two]
    _ ≤ count (4 * m + 1) := Fintype.card_le_of_injective completion (completion_injective m)

/-- A multiplied form of the exponential lower bound for the full ratio. -/
theorem ratio_lower_bound {m : ℕ} (hm : 50 ≤ m) :
    4 ^ m * (4 * m + 1) ^ (4 * m) ≤ count (4 * m + 1) := by
  have hquad : 2500 ≤ m ^ 2 := by nlinarith
  have hbase : 4 * (5 * m) ^ 4 ≤ m ^ 6 := by
    calc
      4 * (5 * m) ^ 4 = 2500 * m ^ 4 := by ring
      _ ≤ m ^ 2 * m ^ 4 := Nat.mul_le_mul_right _ hquad
      _ = m ^ 6 := by ring
  have hp := Nat.pow_le_pow_left hbase m
  have hb : 4 * m + 1 ≤ 5 * m := by omega
  calc
    4 ^ m * (4 * m + 1) ^ (4 * m) ≤ 4 ^ m * (5 * m) ^ (4 * m) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
    _ = (4 * (5 * m) ^ 4) ^ m := by rw [mul_pow, ← pow_mul]
    _ ≤ (m ^ 6) ^ m := hp
    _ = m ^ (6 * m) := (pow_mul _ _ _).symm
    _ ≤ count (4 * m + 1) := count_lower_bound m

/-- The complete eventual Big-O assertion fails for every positive real constant. -/
theorem result : ¬ claim := by
  rintro ⟨C, hC, N, hN, hbound⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (show (1 : ℝ) < 4 by norm_num)
  let m := max 50 (max N k)
  have hm : 50 ≤ m := le_max_left _ _
  have hNm : N ≤ m := (le_max_left N k).trans (le_max_right _ _)
  have hkm : k ≤ m := (le_max_right N k).trans (le_max_right _ _)
  have hfour : C < (4 : ℝ) ^ m := hk.trans_le (pow_le_pow_right₀ (by norm_num) hkm)
  have hpow : 0 < (4 * (m : ℝ) + 1) ^ (4 * m) := pow_pos (by positivity) _
  have hlower : (4 : ℝ) ^ m * (4 * (m : ℝ) + 1) ^ (4 * m) ≤ (count (4 * m + 1) : ℝ) := by
    exact_mod_cast ratio_lower_bound hm
  have hupper := hbound (4 * m + 1) (by omega)
  have hexp : 4 * m + 1 - 1 = 4 * m := by omega
  rw [hexp] at hupper
  push_cast at hupper
  have hsourceLower : (4 : ℝ) ^ m * (4 * (m : ℝ) + 1) ^ (4 * m) ≤
      ((sourceFamily (4 * m + 1)).card : ℝ) := by
    rw [source_family_card]
    exact hlower
  have hsourceUpper : ((sourceFamily (4 * m + 1)).card : ℝ) ≤
      C * (4 * (m : ℝ) + 1) ^ (4 * m) := by
    rw [source_family_card]
    exact hupper
  have hstrict := mul_lt_mul_of_pos_right hfour hpow
  linarith

end D5.S3.Combinatorics.Graph.Domination.BishopMaximalPlacementGrowth
