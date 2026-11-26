/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactElevenGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Seven-cycle axis labels exclude eleven columns in the signed two-contact cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Eleven-column exclusion for two-contact Huang cube columns

The cycle argument follows the structural proof and the independent review archived
with the Q9 projection evidence for Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactElevenGap

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeGirth (adjacent_exists_flip)
open PrimeContactCubeLift (RowSigns EmptyGain)
open PrimeContactCubeOrders PrimeContactCardinalityGap
open PrimeContactTransport (Exponent)
open private diff diff_card diff_symm diff_triangle diff_triangle_card diff_double_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap

open private square_of_shared_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift

section SevenCycle

private theorem step_two (i : Fin 7) : i + 1 + 1 = i + 2 := by
  rw [add_assoc]
  rfl

/-- The axes flipped along the indicated edge of a cyclic cube labeling. -/
abbrev sevenCycleLabel {n : ℕ} (q : Fin 7 → Q n) (i : Fin 7) :=
  diff (q i) (q (i + 1))

/-- Consecutive distance-two labels are disjoint when there is no two-step chord. -/
theorem seven_cycle_consecutive_labels_disjoint {n : ℕ} {q : Fin 7 → Q n}
    (hinj : Function.Injective q)
    (hedge : ∀ i, hammingDist (q i) (q (i + 1)) = 2)
    (hskip : ∀ i, hammingDist (q i) (q (i + 2)) ≠ 2) (i : Fin 7) :
    Disjoint (sevenCycleLabel q i) (sevenCycleLabel q (i + 1)) := by
  have h := diff_triangle_card (q i) (q (i + 2)) (q (i + 1))
  rw [diff_symm (q (i + 2)) (q (i + 1)), ← step_two i] at h
  rw [diff_card (q i) (q (i + 1 + 1)), diff_card (q i) (q (i + 1)),
    diff_card (q (i + 1)) (q (i + 1 + 1)), hedge, hedge] at h
  have hpos : 0 < hammingDist (q i) (q (i + 2)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hi := hinj (hammingDist_eq_zero.mp hz)
    exact (show ∀ j : Fin 7, j ≠ j + 2 by decide) i hi
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by
    have := hskip i
    change hammingDist (q i) (q (i + 1 + 1)) +
      2 * (sevenCycleLabel q i ∩ sevenCycleLabel q (i + 1)).card = 2 + 2 at h
    rw [step_two i] at h
    omega))

/-- A coordinate with no consecutive flips has either zero or two flips
on a closed seven-step Boolean walk. The seven Boolean inputs record
vertex bits, so closure is built into the last comparison. -/
private theorem seven_bit_flip_count (a b c d e f g : Bool)
    (habc : ¬ (a ≠ b ∧ b ≠ c)) (hbcd : ¬ (b ≠ c ∧ c ≠ d))
    (hcde : ¬ (c ≠ d ∧ d ≠ e)) (hdef : ¬ (d ≠ e ∧ e ≠ f))
    (hefg : ¬ (e ≠ f ∧ f ≠ g)) (hfga : ¬ (f ≠ g ∧ g ≠ a))
    (hgab : ¬ (g ≠ a ∧ a ≠ b)) :
    let s := (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) +
      (if c ≠ d then 1 else 0) + (if d ≠ e then 1 else 0) +
      (if e ≠ f then 1 else 0) + (if f ≠ g then 1 else 0) +
      (if g ≠ a then 1 else 0)
    s = (0 : ℕ) ∨ s = 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
    simp_all

/-- Every axis used by a nontriangular seven-cycle appears exactly twice. -/
theorem seven_cycle_axis_occurrences {n : ℕ} {q : Fin 7 → Q n}
    (hdisj : ∀ i, Disjoint (sevenCycleLabel q i) (sevenCycleLabel q (i + 1))) (k : Fin n) :
    (Finset.univ.filter (fun i => q i k ≠ q (i + 1) k)).card = 0 ∨
      (Finset.univ.filter (fun i => q i k ≠ q (i + 1) k)).card = 2 := by
  have h (i : Fin 7) : ¬ (q i k ≠ q (i + 1) k ∧ q (i + 1) k ≠ q (i + 1 + 1) k) := by
    intro hi
    exact Finset.disjoint_left.mp (hdisj i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2⟩)
  have hsum : (Finset.univ.filter (fun i => q i k ≠ q (i + 1) k)).card =
      ∑ i : Fin 7, if q i k ≠ q (i + 1) k then (1 : ℕ) else 0 := by
    symm
    exact_mod_cast (Finset.sum_boole (R := ℕ) (fun i : Fin 7 => q i k ≠ q (i + 1) k)
      Finset.univ)
  rw [hsum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have hh := seven_bit_flip_count (q 0 k) (q 1 k) (q 2 k) (q 3 k) (q 4 k) (q 5 k)
    (q 6 k) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)
  dsimp only at hh
  simp only [Nat.add_assoc] at hh
  convert hh using 4 <;> congr <;> rfl

/-- A three-step shortcut is an edge exactly when the outer labels agree. -/
theorem seven_cycle_chord_iff_label_eq {n : ℕ} {q : Fin 7 → Q n}
    (hedge : ∀ i, hammingDist (q i) (q (i + 1)) = 2)
    (hd : ∀ i, Disjoint (sevenCycleLabel q i) (sevenCycleLabel q (i + 1))) (i : Fin 7) :
    hammingDist (q i) (q (i + 3)) = 2 ↔ sevenCycleLabel q i = sevenCycleLabel q (i + 2) := by
  have he : ∀ j, (sevenCycleLabel q j).card = 2 := fun j => (diff_card ..).trans (hedge j)
  have hab : diff (q i) (q (i + 2)) = sevenCycleLabel q i ∪ sevenCycleLabel q (i + 1) := by
    rw [diff_triangle (q i) (q (i + 2)) (q (i + 1)), diff_symm (q (i + 2)) (q (i + 1))]
    rw [← step_two i]
    exact congrArg₂ (· ∪ ·) (Finset.sdiff_eq_self_of_disjoint (hd i))
      (Finset.sdiff_eq_self_of_disjoint (hd i).symm)
  have h := diff_triangle_card (q i) (q (i + 3)) (q (i + 2))
  rw [diff_symm (q (i + 3)) (q (i + 2))] at h
  have hi : i + 2 + 1 = i + 3 := by rw [add_assoc]; rfl
  rw [← hi, hab] at h
  change (diff (q i) (q (i + 2 + 1))).card +
    2 * ((sevenCycleLabel q i ∪ sevenCycleLabel q (i + 1)) ∩ sevenCycleLabel q (i + 2)).card =
      (sevenCycleLabel q i ∪ sevenCycleLabel q (i + 1)).card + (sevenCycleLabel q (i + 2)).card at h
  have hbc : Disjoint (sevenCycleLabel q (i + 1)) (sevenCycleLabel q (i + 2)) := by
    simpa only [step_two] using hd (i + 1)
  rw [Finset.union_inter_distrib_right,
    Finset.disjoint_iff_inter_eq_empty.mp hbc,
    Finset.union_empty, Finset.card_union_of_disjoint (hd i), he, he, he, diff_card, hi] at h
  constructor
  · intro hc
    have hl := Finset.inter_subset_left (s₁ := sevenCycleLabel q i) (s₂ := sevenCycleLabel q (i + 2))
    have hr := Finset.inter_subset_right (s₁ := sevenCycleLabel q i) (s₂ := sevenCycleLabel q (i + 2))
    have hl' := Finset.eq_of_subset_of_card_le hl (by rw [he]; omega)
    have hr' := Finset.eq_of_subset_of_card_le hr (by rw [he]; omega)
    exact hl'.symm.trans hr'
  · intro heq
    rw [← heq, Finset.inter_self, he] at h
    omega

private theorem labels_no_three {n : ℕ} {q : Fin 7 → Q n}
    (hd : ∀ i, Disjoint (sevenCycleLabel q i) (sevenCycleLabel q (i + 1)))
    {k : Fin n} {i j l : Fin 7} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : k ∈ sevenCycleLabel q i) (hj : k ∈ sevenCycleLabel q j) (hl : k ∈ sevenCycleLabel q l) : False := by
  let S := Finset.univ.filter (fun s : Fin 7 => q s k ≠ q (s + 1) k)
  have hsub : {i, j, l} ⊆ S := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
  have hc := Finset.card_le_card hsub
  have hsize : ({i, j, l} : Finset (Fin 7)).card = 3 := by
    simp [Finset.card_insert_of_notMem, hij, hil, hjl]
  have hocc : S.card = 0 ∨ S.card = 2 := seven_cycle_axis_occurrences hd k
  omega

-- After cancelling two pairs of equal labels, the three other labels
-- have even coordinate multiplicity. If two of them are disjoint,
-- their union must lie in the third, contradicting its size.
private theorem seven_remaining_not_disjoint {n : ℕ} {q : Fin 7 → Q n}
    (hsize : ∀ i, (sevenCycleLabel q i).card = 2)
    (hdisj : ∀ i, Disjoint (sevenCycleLabel q i) (sevenCycleLabel q (i + 1)))
    {a b c d p r s : Fin 7}
    (hcover : ∀ j : Fin 7, j = a ∨ j = b ∨ j = c ∨ j = d ∨ j = p ∨ j = r ∨ j = s)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) (hpd : p ≠ d)
    (hra : r ≠ a) (hrb : r ≠ b) (hrc : r ≠ c) (hrd : r ≠ d)
    (heab : sevenCycleLabel q a = sevenCycleLabel q b) (hecd : sevenCycleLabel q c = sevenCycleLabel q d)
    (hpr : Disjoint (sevenCycleLabel q p) (sevenCycleLabel q r)) : False := by
  have hother {k : Fin n} {j : Fin 7} (hj : k ∈ sevenCycleLabel q j) :
      ∃ l : Fin 7, k ∈ sevenCycleLabel q l ∧ l ≠ j := by
    let S := Finset.univ.filter (fun i : Fin 7 => q i k ≠ q (i + 1) k)
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hpos := Finset.card_pos.mpr ⟨j, hjS⟩
    have hocc : S.card = 0 ∨ S.card = 2 := seven_cycle_axis_occurrences hdisj k
    have hEr : (S.erase j).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hjS]
      omega
    obtain ⟨l, hl⟩ := hEr
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (Finset.mem_erase.mp hl).2).2⟩, (Finset.mem_erase.mp hl).1⟩
  have hsub : sevenCycleLabel q p ∪ sevenCycleLabel q r ⊆ sevenCycleLabel q s := by
    intro k hk
    rcases Finset.mem_union.mp hk with hp | hr
    · obtain ⟨l, hl, hne⟩ := hother hp
      rcases hcover l with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (labels_no_three hdisj hpa hpb hab hp hl (heab ▸ hl)).elim
      · exact (labels_no_three hdisj hpa hpb hab hp (heab.symm ▸ hl) hl).elim
      · exact (labels_no_three hdisj hpc hpd hcd hp hl (hecd ▸ hl)).elim
      · exact (labels_no_three hdisj hpc hpd hcd hp (hecd.symm ▸ hl) hl).elim
      · exact (hne rfl).elim
      · exact (Finset.disjoint_left.mp hpr hp hl).elim
      · exact hl
    · obtain ⟨l, hl, hne⟩ := hother hr
      rcases hcover l with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (labels_no_three hdisj hra hrb hab hr hl (heab ▸ hl)).elim
      · exact (labels_no_three hdisj hra hrb hab hr (heab.symm ▸ hl) hl).elim
      · exact (labels_no_three hdisj hrc hrd hcd hr hl (hecd ▸ hl)).elim
      · exact (labels_no_three hdisj hrc hrd hcd hr (hecd.symm ▸ hl) hl).elim
      · exact (Finset.disjoint_left.mp hpr hl hr).elim
      · exact (hne rfl).elim
      · exact hl
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hpr, hsize, hsize, hsize] at hc
  omega

private theorem seven_chord_from_zero {n : ℕ} {q : Fin 7 → Q n}
    (hedge : ∀ i, hammingDist (q i) (q (i + 1)) = 2)
    (hd : ∀ i, Disjoint (sevenCycleLabel q i) (sevenCycleLabel q (i + 1)))
    (hno : ∀ i j, hammingDist (q i) (q j) = 2 →
      hammingDist (q (i + 1)) (q j) ≠ 2)
    (h0 : hammingDist (q 0) (q 3) = 2) (j : Fin 7)
    (hj : hammingDist (q j) (q (j + 3)) = 2) : j = 0 := by
  have he : ∀ i, (sevenCycleLabel q i).card = 2 := fun i => (diff_card ..).trans (hedge i)
  have hA : sevenCycleLabel q 0 = sevenCycleLabel q 2 := (seven_cycle_chord_iff_label_eq hedge hd 0).mp h0
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < (sevenCycleLabel q 0).card by rw [he]; decide)
  have hk2 : k ∈ sevenCycleLabel q 2 := hA ▸ hk
  have hB := (seven_cycle_chord_iff_label_eq hedge hd j).mp hj
  fin_cases j
  · rfl
  · exact (seven_remaining_not_disjoint he hd (a := 0) (b := 2) (c := 1) (d := 3)
      (p := 4) (r := 5) (s := 6) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA hB (hd 4)).elim
  · exact (labels_no_three hd (i := 0) (j := 2) (l := 4) (by decide)
      (by decide) (by decide) hk hk2 (hB ▸ hk2)).elim
  · exact (hno 6 3 ((hammingDist_comm (q 6) (q 3)).trans hj) h0).elim
  · exact (hno 3 0 ((hammingDist_comm (q 3) (q 0)).trans h0) hj).elim
  · exact (labels_no_three hd (i := 0) (j := 2) (l := 5) (by decide)
      (by decide) (by decide) hk hk2 (hB.symm ▸ hk)).elim
  · exact (seven_remaining_not_disjoint he hd (a := 0) (b := 2) (c := 6) (d := 1)
      (p := 3) (r := 4) (s := 5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA hB (hd 3)).elim

/-- A seven-cycle of distance-two cube edges, with no triangle containing
any cycle edge, has at most one chord. Each chord is indexed in the unique
direction in which its endpoints are three steps apart. -/
theorem seven_cycle_chord_unique {n : ℕ} (q : Fin 7 → Q n)
    (hinj : Function.Injective q)
    (hedge : ∀ i, hammingDist (q i) (q (i + 1)) = 2)
    (hno : ∀ i j, hammingDist (q i) (q j) = 2 →
      hammingDist (q (i + 1)) (q j) ≠ 2)
    {i j : Fin 7} (hi : hammingDist (q i) (q (i + 3)) = 2)
    (hj : hammingDist (q j) (q (j + 3)) = 2) : i = j := by
  let p (k : Fin 7) := q (i + k)
  have hpedge (k : Fin 7) : hammingDist (p k) (p (k + 1)) = 2 := by
    simpa only [p, add_assoc] using hedge (i + k)
  have hpno (k l : Fin 7) (h : hammingDist (p k) (p l) = 2) :
      hammingDist (p (k + 1)) (p l) ≠ 2 := by
    simpa only [p, add_assoc] using hno (i + k) (i + l) h
  have hpInj : Function.Injective p := fun _ _ h => add_left_cancel (hinj h)
  have hpdisj := seven_cycle_consecutive_labels_disjoint hpInj hpedge (fun k hc =>
    hpno k (k + 2) hc (by simpa only [step_two] using hpedge (k + 1)))
  have h0 : hammingDist (p 0) (p 3) = 2 := by simpa [p] using hi
  have hj' : hammingDist (p (j - i)) (p (j - i + 3)) = 2 := by
    simpa only [p, ← add_assoc, add_sub_cancel, add_comm i j] using hj
  have heq := seven_chord_from_zero hpedge hpdisj hpno h0 (j - i) hj'
  exact (sub_eq_zero.mp heq).symm

end SevenCycle

section ResidualGraph

private abbrev triangleType (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) :=
  (threeContactRowsAt K occupied q).card

private def activeColumns (K : Finset (Q 8)) (occupied : Q 8 → Bool) : Finset (Q 8) :=
  K.filter (fun q => triangleType K occupied q < 2)

private theorem active_card (K : Finset (Q 8)) (occupied : Q 8 → Bool) :
    (activeColumns K occupied).card = columnCount K occupied 0 + columnCount K occupied 1 := by
  unfold activeColumns columnCount
  rw [← Finset.card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h0 := (Finset.mem_filter.mp hx).2
    have h1 := (Finset.mem_filter.mp hy).2
    omega)]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_union]
  change (q ∈ K ∧ triangleType K occupied q < 2) ↔
    (q ∈ K ∧ triangleType K occupied q = 0) ∨ (q ∈ K ∧ triangleType K occupied q = 1)
  constructor
  · rintro ⟨hq, ht⟩
    by_cases h0 : triangleType K occupied q = 0
    · exact Or.inl ⟨hq, h0⟩
    · exact Or.inr ⟨hq, by omega⟩
  · rintro (⟨hq, ht⟩ | ⟨hq, ht⟩) <;> exact ⟨hq, by omega⟩

private theorem hamming_ne_of_edge {x y : Q 8} (h : hammingDist x y = 2) : x ≠ y := by
  rintro rfl
  simp at h

private theorem no_triangle_on_residual {K : Finset (Q 8)} {x y z : Q 8}
    (hy : y ∈ triangleFreeNeighbors K x) (hz : z ∈ K)
    (hxz : hammingDist x z = 2) (hyz : hammingDist y z = 2) : False := by
  have hm : z ∈ commonColumns K x y := mem_commonColumns.mpr ⟨hz, hxz, hyz⟩
  have hzero := (mem_triangleFreeNeighbors.mp hy).2.2
  exact (Finset.notMem_empty z) (Finset.card_eq_zero.mp hzero ▸ hm)

private theorem residual_subset_active {K : Finset (Q 8)} {occupied : Q 8 → Bool}
    (hdeg : ∀ q ∈ K, (triangleFreeNeighbors K q).card + 2 * triangleType K occupied q = 4)
    {x : Q 8} (hx : x ∈ K) : triangleFreeNeighbors K x ⊆ (activeColumns K occupied).erase x := by
  intro y hy
  obtain ⟨hyK, hxy, _⟩ := mem_triangleFreeNeighbors.mp hy
  have hpos := Finset.card_pos.mpr ⟨x, mem_triangleFreeNeighbors_symm hx hy⟩
  exact Finset.mem_erase.mpr ⟨(hamming_ne_of_edge hxy).symm, Finset.mem_filter.mpr
    ⟨hyK, by have := hdeg y hyK; omega⟩⟩

/-- With at most six active columns, a degree-four vertex requires six
active columns and a second degree-four vertex. -/
private theorem second_degree_four {K : Finset (Q 8)} {occupied : Q 8 → Bool}
    (hdeg : ∀ q ∈ K, (triangleFreeNeighbors K q).card + 2 * triangleType K occupied q = 4)
    (hsmall : (activeColumns K occupied).card ≤ 6) {x : Q 8} (hx : x ∈ K)
    (hx0 : triangleType K occupied x = 0) :
    (activeColumns K occupied).card = 6 ∧ 2 ≤ columnCount K occupied 0 := by
  let S := activeColumns K occupied
  let N := triangleFreeNeighbors K x
  let R := S \ insert x N
  have hxS : x ∈ S := Finset.mem_filter.mpr ⟨hx, by omega⟩
  have hNsub := residual_subset_active hdeg hx
  have hNcard : N.card = 4 := by
    have hh := hdeg x hx
    change N.card + 2 * triangleType K occupied x = 4 at hh
    omega
  have hxN : x ∉ N := fun h => (Finset.mem_erase.mp (hNsub h)).1 rfl
  have hsub : insert x N ⊆ S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hxS
    · exact (Finset.mem_erase.mp (hNsub hz)).2
  have hcount : R.card + 5 = S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_insert_of_notMem hxN, hNcard] at h
    exact h
  have hnext {y : Q 8} (hy : y ∈ N) : ∃ z ∈ R, z ∈ triangleFreeNeighbors K y := by
    obtain ⟨hyK, hxy, _⟩ := mem_triangleFreeNeighbors.mp hy
    have hback := mem_triangleFreeNeighbors_symm hx hy
    have hpos : 0 < (triangleFreeNeighbors K y).card := Finset.card_pos.mpr ⟨x, hback⟩
    have hdy := hdeg y hyK
    have he : ((triangleFreeNeighbors K y).erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hback]
      omega
    obtain ⟨z, hz⟩ := he
    obtain ⟨hzx, hzy⟩ := Finset.mem_erase.mp hz
    have hzS := (Finset.mem_erase.mp (residual_subset_active hdeg hyK hzy)).2
    refine ⟨z, Finset.mem_sdiff.mpr ⟨hzS, ?_⟩, hzy⟩
    intro hz'
    rcases Finset.mem_insert.mp hz' with h | hzN
    · exact hzx h
    · obtain ⟨hzK, hxz, _⟩ := mem_triangleFreeNeighbors.mp hzN
      exact no_triangle_on_residual hy hzK hxz (mem_triangleFreeNeighbors.mp hzy).2.1
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < N.card by omega)
  obtain ⟨z, hz, _⟩ := hnext hy
  have hRpos := Finset.card_pos.mpr ⟨z, hz⟩
  have hRcard : R.card = 1 := by change S.card ≤ 6 at hsmall; omega
  have hR : R = {z} := Finset.card_eq_one.mp hRcard |>.elim fun w hw => by
    have hzw : z = w := Finset.mem_singleton.mp (hw ▸ hz)
    simpa [hzw] using hw
  have hzK : z ∈ K := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
  have hzNe : z ≠ x := fun h => (Finset.mem_sdiff.mp hz).2 (Finset.mem_insert.mpr (Or.inl h))
  have hNz : N ⊆ triangleFreeNeighbors K z := by
    intro y hy
    obtain ⟨w, hw, hwAdj⟩ := hnext hy
    have hwz : w = z := Finset.mem_singleton.mp (hR ▸ hw)
    subst w
    exact mem_triangleFreeNeighbors_symm (mem_triangleFreeNeighbors.mp hy).1 hwAdj
  have hdz := hdeg z hzK
  have hle := Finset.card_le_card hNz
  have hz0 : triangleType K occupied z = 0 := by omega
  have hpair : {x, z} ⊆ K.filter (fun q => triangleType K occupied q = 0) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hx, hx0⟩
    · obtain rfl := Finset.mem_singleton.mp hq
      exact Finset.mem_filter.mpr ⟨hzK, hz0⟩
  have hc := Finset.card_le_card hpair
  rw [Finset.card_pair hzNe.symm] at hc
  change S.card = 6 ∧ _
  exact ⟨by omega, hc⟩

/-- The weighted order cover and triangle incidence leave only four or seven
degree-two vertices in the graph obtained by deleting triangle edges. -/
theorem residual_pattern_of_eleven
    {K : Finset (Q 8)} {occupied : Q 8 → Bool} {τ σ : Q 8 → ℝ} {v : Q 8 → Exponent 8}
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (hv : EmptyGain (K : Set (Q 8)) occupied v)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4)
    (hn : K.card = 11) :
    columnCount K occupied 0 = 0 ∧
      ((columnCount K occupied 1 = 4 ∧ columnCount K occupied 2 = 7) ∨
       (columnCount K occupied 1 = 7 ∧ columnCount K occupied 2 = 4)) := by
  have hK : K.Nonempty := Finset.card_pos.mp (by omega)
  have hdeg (q : Q 8) (hq : q ∈ K) :=
    card_triangleFreeNeighbors_add_twice hs htwo hthree hq (hfour q hq)
  have ht (q : Q 8) (hq : q ∈ K) : triangleType K occupied q ≤ 2 := by
    have hh := hdeg q hq
    change (triangleFreeNeighbors K q).card + 2 * triangleType K occupied q = 4 at hh
    omega
  obtain ⟨hpartition, hinc⟩ := columnCount_partition_and_incidence ht
  have hcover := weighted_order_coverage_of_cube K hK occupied τ σ v hs hv hfour htwo hthree
  have hSc := active_card K occupied
  have hzero : columnCount K occupied 0 = 0 := by
    by_contra hne
    have hsmall : (activeColumns K occupied).card ≤ 6 := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < columnCount K occupied 0 by omega)
    obtain ⟨hxK, hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hS6, htwo0⟩ := second_degree_four hdeg hsmall hxK hx0
    omega
  have hn1 : columnCount K occupied 1 ≠ 1 := by
    intro hone
    have hSc1 : (activeColumns K occupied).card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < columnCount K occupied 1 by omega)
    obtain ⟨hxK, hx1⟩ := Finset.mem_filter.mp hx
    change triangleType K occupied x = 1 at hx1
    have hxS : x ∈ activeColumns K occupied := Finset.mem_filter.mpr ⟨hxK, by omega⟩
    have hle := Finset.card_le_card (residual_subset_active hdeg hxK)
    rw [Finset.card_erase_of_mem hxS, hSc1] at hle
    have hdx := hdeg x hxK
    change (triangleFreeNeighbors K x).card + 2 * triangleType K occupied x = 4 at hdx
    omega
  omega

end ResidualGraph

section CycleExtraction

variable {α : Type*} [Fintype α] (G : SimpleGraph α)

private def cyclicNext {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

private theorem cycle_order (hreg : ∀ x : α, (G.neighborSet x).ncard = 2)
    (htri : ∀ {x y z}, G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (hcard : Fintype.card α ≤ 7) (x : α) :
    ∃ q : Fin (Fintype.card α) → α, Function.Bijective q ∧ ∀ i, G.Adj (q i) (q (cyclicNext i)) := by
  classical
  have hcycle (u : α) : ∃ p : G.Walk u u, p.IsCycle ∧
      p.toSubgraph.verts = (G.connectedComponentMk u).supp :=
    SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (fun {v} _ => hreg v) SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      (Set.nonempty_of_ncard_ne_zero (by rw [hreg]; decide))
  have hlength {u : α} {p : G.Walk u u} (hp : p.IsCycle) : 4 ≤ p.length := by
    have h := hp.three_le_length
    by_contra! hl
    have h3 : p.length = 3 := by omega
    have h01 := p.adj_getVert_succ (i := 0) (by omega)
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    have h23 := p.adj_getVert_succ (i := 2) (by omega)
    have hend : p.getVert 3 = p.getVert 0 := by rw [← h3]; simp
    change G.Adj (p.getVert 2) (p.getVert 3) at h23
    rw [hend] at h23
    exact htri h01 h23.symm h12
  have hinj {u : α} {p : G.Walk u u} (hp : p.IsCycle) :
      Function.Injective (fun i : Fin p.length => p.getVert i) := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn'
    · change i.val ≤ p.length - 1
      omega
    · change j.val ≤ p.length - 1
      omega
    · exact hij
  obtain ⟨p, hp, hps⟩ := hcycle x
  have hsupp : (G.connectedComponentMk x).supp = Set.univ := by
    by_contra hne
    have hother : ∃ y, y ∉ (G.connectedComponentMk x).supp := by
      by_contra! hall
      exact hne (Set.eq_univ_of_forall hall)
    obtain ⟨y, hy⟩ := hother
    obtain ⟨r, hr, hrs⟩ := hcycle y
    let f : Fin p.length ⊕ Fin r.length → α :=
      Sum.elim (fun i => p.getVert i) (fun i => r.getVert i)
    have hsep (i : Fin p.length) (j : Fin r.length) : p.getVert i ≠ r.getVert j := by
      have hi : p.getVert i ∈ (G.connectedComponentMk x).supp :=
        hps ▸ p.mem_verts_toSubgraph.mpr (p.getVert_mem_support i)
      have hj : r.getVert j ∈ (G.connectedComponentMk y).supp :=
        hrs ▸ r.mem_verts_toSubgraph.mpr (r.getVert_mem_support j)
      intro he
      apply hy
      have hix := ((G.connectedComponentMk x).mem_supp_iff _).mp hi
      have hjy := ((G.connectedComponentMk y).mem_supp_iff _).mp hj
      rw [he] at hix
      exact ((G.connectedComponentMk x).mem_supp_iff y).mpr (hjy.symm.trans hix)
    have hf : Function.Injective f := by
      intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · exact congrArg Sum.inl (hinj hp hab)
      · exact (hsep a b hab).elim
      · exact (hsep b a hab.symm).elim
      · exact congrArg Sum.inr (hinj hr hab)
    have hsum := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hsum
    have := hlength hp
    have := hlength hr
    omega
  have hsurj : Function.Surjective (fun i : Fin p.length => p.getVert i) := by
    intro y
    have hy : y ∈ p.toSubgraph.verts := by rw [hps, hsupp]; trivial
    obtain ⟨j, hjy, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (p.mem_verts_toSubgraph.mp hy)
    by_cases hjlt : j < p.length
    · exact ⟨⟨j, hjlt⟩, hjy⟩
    · have he : j = p.length := by omega
      refine ⟨⟨0, by have := hlength hp; omega⟩, ?_⟩
      simpa [he] using hjy
  have heq := Fintype.card_of_bijective ⟨hinj hp, hsurj⟩
  rw [Fintype.card_fin] at heq
  rw [← heq]
  refine ⟨fun i => p.getVert i, ⟨hinj hp, hsurj⟩, ?_⟩
  intro i
  have ha := p.adj_getVert_succ i.isLt
  change G.Adj (p.getVert i.val) (p.getVert (cyclicNext i).val)
  have hi : (cyclicNext i).val = i.val + 1 ∨
      i.val + 1 = p.length ∧ (cyclicNext i).val = 0 := by
    change (i.val + 1) % p.length = i.val + 1 ∨
      i.val + 1 = p.length ∧ (i.val + 1) % p.length = 0
    by_cases hlt : i.val + 1 < p.length
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · have he : i.val + 1 = p.length := by omega
      exact Or.inr ⟨he, by rw [he, Nat.mod_self]⟩
  rcases hi with hi | ⟨hl, hi⟩
  · simpa only [hi] using ha
  · simpa [hi, hl] using ha

end CycleExtraction

section Exclusion

variable {K : Finset (Q 8)} {occupied : Q 8 → Bool}

private theorem residual_cycle {m : ℕ}
    (hdeg : ∀ q ∈ K, (triangleFreeNeighbors K q).card + 2 * triangleType K occupied q = 4)
    (hzero : columnCount K occupied 0 = 0)
    (hcard : (activeColumns K occupied).card = m) (hm : 0 < m) (hm' : m ≤ 7) :
    ∃ q : Fin m → Q 8, Function.Injective q ∧
      (∀ x, x ∈ activeColumns K occupied ↔ ∃ i, q i = x) ∧
      ∀ i, q (cyclicNext i) ∈ triangleFreeNeighbors K (q i) := by
  classical
  let S := activeColumns K occupied
  have hK (x : S) : x.val ∈ K := (Finset.mem_filter.mp x.prop).1
  let G : SimpleGraph S :=
    { Adj := fun x y => y.val ∈ triangleFreeNeighbors K x.val
      symm := ⟨fun x _ h => mem_triangleFreeNeighbors_symm (hK x) h⟩
      loopless := ⟨fun x h => hamming_ne_of_edge (mem_triangleFreeNeighbors.mp h).2.1 rfl⟩ }
  have htriangle {x y z : S} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False :=
    no_triangle_on_residual hxy (hK z) (mem_triangleFreeNeighbors.mp hxz).2.1
      (mem_triangleFreeNeighbors.mp hyz).2.1
  have hregular (x : S) : (G.neighborSet x).ncard = 2 := by
    have hd := hdeg x.val (hK x)
    have hxt : triangleType K occupied x.val < 2 := (Finset.mem_filter.mp x.prop).2
    have hxt0 : triangleType K occupied x.val ≠ 0 := by
      intro h
      have he : (K.filter (fun y => triangleType K occupied y = 0)).card = 0 := hzero
      have hpos : 0 < (K.filter (fun y => triangleType K occupied y = 0)).card :=
        Finset.card_pos.mpr ⟨x.val, Finset.mem_filter.mpr ⟨hK x, h⟩⟩
      omega
    change (triangleFreeNeighbors K x.val).card + 2 * triangleType K occupied x.val = 4 at hd
    have hc : (triangleFreeNeighbors K x.val).card = 2 := by omega
    have hb : Set.BijOn (fun y : S => y.val) (G.neighborSet x)
        (↑(triangleFreeNeighbors K x.val) : Set (Q 8)) := by
      refine ⟨fun _ h => h, Subtype.val_injective.injOn, ?_⟩
      intro y hy
      have hs' : y ∈ S := (Finset.mem_erase.mp (residual_subset_active hdeg (hK x) hy)).2
      exact ⟨⟨y, hs'⟩, hy, rfl⟩
    simpa only [Set.ncard_coe_finset, hc] using hb.ncard_eq
  have hF : Fintype.card S = m := (Fintype.card_coe S).trans hcard
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < S.card from hcard.symm ▸ hm)
  have hcyc := cycle_order G hregular (fun hxy hxz => htriangle hxy hxz)
    (hF.symm ▸ hm') ⟨x, hx⟩
  rw [hF] at hcyc
  obtain ⟨q, hb, he⟩ := hcyc
  refine ⟨fun i => (q i).val, Subtype.val_injective.comp hb.1, ?_, he⟩
  intro y
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := hb.2 ⟨y, hy⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, rfl⟩
    exact (q i).prop

private theorem four_cycle_card_bound (q : Fin 4 → Q 8) (hinj : Function.Injective q)
    (hcycle : ∀ i, q (i + 1) ∈ triangleFreeNeighbors K (q i))
    (hdegree : ∀ i, (columnNeighbors K (q i)).card = 4)
    (hres : ∀ i, (triangleFreeNeighbors K (q i)).card = 2)
    (hcom : ∀ i j, q i ≠ q j → hammingDist (q i) (q j) ≠ 2 →
      (commonColumns K (q i) (q j)).card ≤ 2) : 12 ≤ K.card := by
  classical
  have hk (i : Fin 4) : q i ∈ K := by
    simpa only [sub_add_cancel] using (mem_triangleFreeNeighbors.mp (hcycle (i - 1))).1
  have edge (i : Fin 4) := (mem_triangleFreeNeighbors.mp (hcycle i)).2.1
  have two (i : Fin 4) : i + 1 + 1 = i + 2 := by rw [add_assoc]; rfl
  have skip₂ (i : Fin 4) : hammingDist (q i) (q (i + 2)) ≠ 2 := by
    intro h
    exact no_triangle_on_residual (hcycle i) (hk (i + 2)) h (by simpa only [two] using edge (i + 1))
  let S := Finset.univ.image q
  let B (i : Fin 4) := columnNeighbors K (q i) \ triangleFreeNeighbors K (q i)
  have hSc : S.card = 4 := by simp [S, Finset.card_image_of_injective _ hinj]
  have hSK : S ⊆ K := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hk i
  have hB (i : Fin 4) : (B i).card = 2 := by
    have hsub : triangleFreeNeighbors K (q i) ⊆ columnNeighbors K (q i) :=
      Finset.filter_subset _ _
    have h : (B i).card + (triangleFreeNeighbors K (q i)).card = (columnNeighbors K (q i)).card :=
      Finset.card_sdiff_add_card_eq_card hsub
    rw [hres i, hdegree i] at h
    omega
  have hadd (i j : Fin 4) : i = j ∨ j = i + 1 ∨ i = j + 1 ∨ j = i + 2 :=
    (by decide : ∀ a b : Fin 4, a = b ∨ b = a + 1 ∨ a = b + 1 ∨ b = a + 2) i j
  have houtside {i : Fin 4} {x : Q 8} (hx : x ∈ B i) : x ∉ S := by
    obtain ⟨hxG, hxH⟩ := Finset.mem_sdiff.mp hx
    have hdist := (mem_columnNeighbors.mp hxG).2
    intro hxS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxS
    rcases hadd i j with rfl | rfl | he | rfl
    · simp at hdist
    · exact hxH (hcycle i)
    · exact hxH (he ▸ mem_triangleFreeNeighbors_symm (hk j) (hcycle j))
    · exact skip₂ i hdist
  have hpair : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint B := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxK, hix⟩ := mem_columnNeighbors.mp (Finset.mem_sdiff.mp hx).1
    have hjx := (mem_columnNeighbors.mp (Finset.mem_sdiff.mp hy).1).2
    rcases hadd i j with h | rfl | h | rfl
    · exact hij h
    · exact no_triangle_on_residual (hcycle i) hxK hix hjx
    · exact no_triangle_on_residual (h ▸ hcycle j) hxK hjx hix
    · have ha : q (i + 1) ∈ commonColumns K (q i) (q (i + 2)) :=
        mem_commonColumns.mpr ⟨hk _, edge i,
          (hammingDist_comm ..).trans (by simpa only [two] using edge (i + 1))⟩
      have hb : q (i + 3) ∈ commonColumns K (q i) (q (i + 2)) := by
        have h30 : ∀ k : Fin 4, k + 3 + 1 = k := by decide
        have h23 : ∀ k : Fin 4, k + 2 + 1 = k + 3 := by decide
        have he30 : hammingDist (q (i + 3)) (q i) = 2 := by
          simpa only [h30] using edge (i + 3)
        exact mem_commonColumns.mpr ⟨hk _, (hammingDist_comm ..).trans he30,
          by simpa only [h23] using edge (i + 2)⟩
      have hx' : x ∈ commonColumns K (q i) (q (i + 2)) := mem_commonColumns.mpr ⟨hxK, hix, hjx⟩
      have hn1 : x ≠ q (i + 1) := fun he => houtside hx (he ▸ Finset.mem_image_of_mem q (Finset.mem_univ _))
      have hn3 : x ≠ q (i + 3) := fun he => houtside hx (he ▸ Finset.mem_image_of_mem q (Finset.mem_univ _))
      have h13 : q (i + 1) ≠ q (i + 3) :=
        fun he => (show ∀ k : Fin 4, k + 1 ≠ k + 3 by decide) i (hinj he)
      have h02 : q i ≠ q (i + 2) :=
        fun he => (show ∀ k : Fin 4, k ≠ k + 2 by decide) i (hinj he)
      have hs : {x, q (i + 1), q (i + 3)} ⊆ commonColumns K (q i) (q (i + 2)) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hx'
        · exact ha
        · exact hb
      have hle := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem (by simp [hn1, hn3]), Finset.card_pair h13] at hle
      have := hcom i (i + 2) h02 (skip₂ i)
      omega
  have hu : (Finset.univ.biUnion B).card = 8 := by
    rw [Finset.card_biUnion hpair]
    simp [hB]
  have hs : Finset.univ.biUnion B ⊆ K \ S := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_sdiff.mpr ⟨(mem_columnNeighbors.mp (Finset.mem_sdiff.mp hi).1).1, houtside hi⟩
  have hle := Finset.card_le_card hs
  have hdiff := Finset.card_sdiff_add_card_eq_card hSK
  omega

private theorem dist_two_of_shared_row {x y r : Q 8} (hne : x ≠ y)
    (hx : (hypercube 8).Adj x r) (hy : (hypercube 8).Adj y r) :
    hammingDist x y = 2 := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hx
  obtain ⟨j, hj⟩ := adjacent_exists_flip hy
  obtain ⟨hij, hxy, _⟩ := square_of_shared_row hne (hi.symm.trans hj)
  rw [← diff_card, ← hxy, diff_double_flip x hij, Finset.card_pair hij]

private theorem seven_cycle_row_bound (q : Fin 7 → Q 8) (hinj : Function.Injective q)
    (hcycle : ∀ i, q (i + 1) ∈ triangleFreeNeighbors K (q i))
    (ht : ∀ i, triangleType K occupied (q i) = 1) :
    6 ≤ (threeContactRows K occupied).card := by
  classical
  have hk (i : Fin 7) : q i ∈ K := by
    simpa only [sub_add_cancel] using (mem_triangleFreeNeighbors.mp (hcycle (i - 1))).1
  have he (i : Fin 7) := (mem_triangleFreeNeighbors.mp (hcycle i)).2.1
  have hno (i j : Fin 7) (hij : hammingDist (q i) (q j) = 2) :
      hammingDist (q (i + 1)) (q j) ≠ 2 :=
    no_triangle_on_residual (hcycle i) (hk j) hij
  have hs (i : Fin 7) : hammingDist (q i) (q (i + 2)) ≠ 2 :=
    fun hij => hno i (i + 2) hij (by simpa only [step_two] using he (i + 1))
  -- Delete one endpoint of the sole possible chord. On the remaining six
  -- ring vertices, any distance-two edge is a ring edge.
  have hremove : ∃ c : Fin 7, ∀ i j : Fin 7, i ≠ c → j ≠ c →
      hammingDist (q i) (q j) = 2 → j = i + 1 ∨ i = j + 1 := by
    have hclass : ∀ i j : Fin 7, i = j ∨ j = i + 1 ∨ i = j + 1 ∨
        j = i + 2 ∨ i = j + 2 ∨ j = i + 3 ∨ i = j + 3 := by decide
    have hoff (i j : Fin 7) (hij : hammingDist (q i) (q j) = 2)
        (hf : j ≠ i + 1) (hb : i ≠ j + 1) :
        j = i + 3 ∨ i = j + 3 := by
      rcases hclass i j with rfl | h | h | rfl | h | h | h
      · simp at hij
      · exact (hf h).elim
      · exact (hb h).elim
      · exact (hs i hij).elim
      · exact (hs j (h ▸ (hammingDist_comm (q j) (q i)).trans hij)).elim
      · exact Or.inl h
      · exact Or.inr h
    by_cases hc : ∃ i : Fin 7, hammingDist (q i) (q (i + 3)) = 2
    · obtain ⟨c, hc⟩ := hc
      refine ⟨c, fun i j hi hj hij => ?_⟩
      by_contra! h'
      rcases hoff i j hij h'.1 h'.2 with rfl | h
      · exact hi (seven_cycle_chord_unique q hinj he hno hij hc)
      · have hjc := seven_cycle_chord_unique q hinj he hno
          (h ▸ (hammingDist_comm (q j) (q i)).trans hij) hc
        exact hj hjc
    · refine ⟨0, fun i j _ _ hij => ?_⟩
      by_contra! h'
      rcases hoff i j hij h'.1 h'.2 with rfl | h
      · exact hc ⟨i, hij⟩
      · exact hc ⟨j, h ▸ (hammingDist_comm (q j) (q i)).trans hij⟩
  obtain ⟨c, hc⟩ := hremove
  let S : Finset (Fin 7) := Finset.univ.erase c
  have hS : S.card = 6 := by simp [S]
  have hrow (i : Fin 7) : ∃ r, r ∈ threeContactRowsAt K occupied (q i) :=
    Finset.card_pos.mp (by have hh := ht i; change (threeContactRowsAt K occupied (q i)).card = 1 at hh; omega)
  choose row hrow using hrow
  have hmap : Set.MapsTo row (↑S : Set (Fin 7)) (↑(threeContactRows K occupied) : Set (Q 8)) := by
    intro i _
    have hr := (mem_threeContactRowsAt.mp (hrow i)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  have hrowInj : (↑S : Set (Fin 7)).InjOn row := by
    intro i hi j hj hij
    by_contra hne
    have hi' : i ≠ c := (Finset.mem_erase.mp hi).1
    have hj' : j ≠ c := (Finset.mem_erase.mp hj).1
    have hir := (mem_threeContactRowsAt.mp (hrow i)).1
    have hjr := (mem_threeContactRowsAt.mp (hrow j)).1
    have hd := dist_two_of_shared_row (fun h => hne (hinj h)) hir (hij.symm ▸ hjr)
    have hqj : q j ∈ triangleFreeNeighbors K (q i) := by
      rcases hc i j hi' hj' hd with h | h
      · rw [h]
        exact hcycle i
      · exact mem_triangleFreeNeighbors_symm (hk j) (by rw [h]; exact hcycle j)
    have hm := (mem_threeContactRowsAt.mp (hrow i)).2.2
    -- The third contact gives a common column of the ring-edge endpoints.
    have htK : {q i, q j} ⊆ rowContacts K (row i) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | hx
      · rw [h]
        exact mem_rowContacts.mpr ⟨hk _, hir⟩
      · rw [Finset.mem_singleton.mp hx]
        exact mem_rowContacts.mpr ⟨hk _, hij.symm ▸ hjr⟩
    have hlt : {q i, q j} ⊂ rowContacts K (row i) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨htK, fun heq => by
        have hh := congrArg Finset.card heq
        rw [Finset.card_pair (fun he => hne (hinj he)), hm] at hh
        omega⟩
    obtain ⟨z, hz, hz'⟩ := Finset.exists_of_ssubset hlt
    obtain ⟨hzK, hzr⟩ := mem_rowContacts.mp hz
    have hzi : q i ≠ z := fun e => hz' (Finset.mem_insert.mpr (Or.inl e.symm))
    have hzj : q j ≠ z := fun e => hz' (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr e.symm)))
    exact no_triangle_on_residual hqj hzK
      (dist_two_of_shared_row hzi hir hzr) (dist_two_of_shared_row hzj (hij.symm ▸ hjr) hzr)
  simpa only [hS] using Finset.card_le_card_of_injOn row hmap hrowInj

/-- Eleven columns are impossible in the two-contact Q8 case with compatible
Huang row signs and an integer exponent lift. -/
theorem card_ne_eleven_of_twoContact {τ σ : Q 8 → ℝ} {v : Q 8 → Exponent 8}
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (hv : EmptyGain (K : Set (Q 8)) occupied v)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4) :
    K.card ≠ 11 := by
  intro hn
  obtain ⟨hzero, hcases⟩ := residual_pattern_of_eleven hs hv htwo hthree hfour hn
  have hdeg (x : Q 8) (hx : x ∈ K) :
      (triangleFreeNeighbors K x).card + 2 * triangleType K occupied x = 4 :=
    card_triangleFreeNeighbors_add_twice hs htwo hthree hx (hfour x hx)
  have hone {x : Q 8} (hx : x ∈ activeColumns K occupied) : triangleType K occupied x = 1 := by
    obtain ⟨hxK, hxt⟩ := Finset.mem_filter.mp hx
    change triangleType K occupied x < 2 at hxt
    by_contra hne
    have hz : triangleType K occupied x = 0 := by omega
    have he : (K.filter (fun y => triangleType K occupied y = 0)).card = 0 := hzero
    have hpos : 0 < (K.filter (fun y => triangleType K occupied y = 0)).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxK, hz⟩⟩
    omega
  have hinc := (columnCount_partition_and_incidence
    (fun x hx => threeContactRowsAt_card_le_two hs htwo hthree hx (hfour x hx))).2
  have hCard := active_card K occupied
  rcases hcases with ⟨h4, _⟩ | ⟨h7, hN2⟩
  · obtain ⟨q, hinj, hq, he⟩ := residual_cycle hdeg hzero
      (show (activeColumns K occupied).card = 4 by omega) (by decide) (by decide)
    have hqa (i : Fin 4) : q i ∈ activeColumns K occupied := (hq _).mpr ⟨i, rfl⟩
    have hqK (i : Fin 4) : q i ∈ K := (Finset.mem_filter.mp (hqa i)).1
    have hres (i : Fin 4) : (triangleFreeNeighbors K (q i)).card = 2 := by
      have hd := hdeg (q i) (hqK i)
      rw [hone (hqa i)] at hd
      omega
    have h12 := four_cycle_card_bound q hinj
      (fun i => show q (cyclicNext i) ∈ triangleFreeNeighbors K (q i) from he i)
      (fun i => card_columnNeighbors hs htwo (hqK i) (hfour _ (hqK i))) hres
      (fun i _ hne hnon => card_commonColumns_of_nonadj_le_two hs htwo hthree (hqK i) hne hnon)
    omega
  · obtain ⟨q, hinj, hq, he⟩ := residual_cycle hdeg hzero
      (show (activeColumns K occupied).card = 7 by omega) (by decide) (by decide)
    have h6 := seven_cycle_row_bound q hinj
      (fun i => show q (cyclicNext i) ∈ triangleFreeNeighbors K (q i) from he i)
      (fun i => hone ((hq _).mpr ⟨i, rfl⟩))
    omega

end Exclusion

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactElevenGap
