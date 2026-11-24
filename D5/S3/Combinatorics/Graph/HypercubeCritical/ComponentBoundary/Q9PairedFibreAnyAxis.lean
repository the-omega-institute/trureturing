/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Huang energy limits single fibres with three paired neighbours. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangBalancedSymmetry
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

/-! The Huang energy bound for three paired neighbours along any axis of the nine-cube. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairedFibreAnyAxis

section FirstAxis

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsSwitching switchingVector switching_sq)
open BalancedCubeComponentBoundary (directions directions_card mem_directions regular_directions)
open Q9OccupiedFibreParity (doubleFibres)
open private huangMatrix huang_energy cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_zero matrix_flip_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private matrix_row flip_cons_zero flip_cons_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private liftVertex parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

attribute [local instance] Classical.propDecidable

/-- Number of rows in `S` having exactly `k` neighbours in `P`. -/
private def contactCount (P S : Finset (Q 8)) (k : ℕ) : ℕ :=
  (S.filter fun r => (directions P r).card = k).card

/-- The first moment and the exact unused energy, with the two resulting bounds. -/
private structure ContactBudget (P S E : Finset (Q 8)) (s : Q 8 → ℝ) : Prop where
  incidence : contactCount P S 1 + 2 * contactCount P S 2 + 3 * contactCount P S 3 =
    4 * P.card
  empty_energy : (contactCount P S 1 : ℝ) - 3 * (contactCount P S 3 : ℝ) =
    ∑ r ∈ E, ((huangMatrix 8).mulVec (switchingVector P s) r) ^ 2
  triple_le_one : 3 * contactCount P S 3 ≤ contactCount P S 1
  triple_le : contactCount P S 3 ≤ 2 * P.card / 3

private theorem paired_row (P : Finset (Q 8)) (s : Q 8 → ℝ) (r : Q 8) :
    (huangMatrix 8).mulVec (switchingVector P s) r =
      ∑ i ∈ directions P r, huangMatrix 8 r (BalancedCriticalSpectrum.flip r i) * s (BalancedCriticalSpectrum.flip r i) := by
  rw [matrix_row]
  calc
    _ = ∑ i ∈ directions P r, huangMatrix 8 r (BalancedCriticalSpectrum.flip r i) *
        switchingVector P s (BalancedCriticalSpectrum.flip r i) := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hnot : BalancedCriticalSpectrum.flip r i ∉ P := fun h => hi ((mem_directions P r i).mpr h)
      simp [switchingVector, hnot]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      simp only [switchingVector, ite_eq_left ((mem_directions P r i).mp hi)]

private theorem sum_contacts (P S : Finset (Q 8)) (k : ℕ → ℕ) (hk : k 0 = 0)
    (hdeg : ∀ r ∈ S, (directions P r).card ≤ 3) :
    (∑ r ∈ S, k (directions P r).card) =
      k 1 * contactCount P S 1 + k 2 * contactCount P S 2 + k 3 * contactCount P S 3 := by
  have hcount (j : ℕ) : contactCount P S j =
      ∑ r ∈ S, if (directions P r).card = j then (1 : ℕ) else 0 := by
    unfold contactCount
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
    rfl
  rw [hcount 1, hcount 2, hcount 3]
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  have h := hdeg r hr
  have hc : (directions P r).card = 0 ∨ (directions P r).card = 1 ∨
      (directions P r).card = 2 ∨ (directions P r).card = 3 := by omega
  rcases hc with h | h | h | h <;> simp [h, hk]

/-- A Q8 estimate with explicit column degrees, coherent single rows, and a
set of remaining rows containing every other incidence. -/
private theorem paired_fibre_energy_of_incidence (P S E : Finset (Q 8)) (s : Q 8 → ℝ)
    (hdisj : Disjoint S E)
    (hunit : ∀ q ∈ P, s q ^ 2 = 1)
    (hcol : ∀ q ∈ P, (directions S q).card = 4)
    (hdeg : ∀ r ∈ S, (directions P r).card ≤ 3)
    (hcover : ∀ r (i : Fin 8), BalancedCriticalSpectrum.flip r i ∈ P → r ∈ S ∪ E)
    (hrow : ∀ r ∈ S, ∃ t : ℝ, t ^ 2 = 1 ∧
      ∀ i ∈ directions P r, huangMatrix 8 r (BalancedCriticalSpectrum.flip r i) * s (BalancedCriticalSpectrum.flip r i) = t) :
    ContactBudget P S E s := by
  let H := (huangMatrix 8).mulVec (switchingVector P s)
  have hinc : (∑ r ∈ S, (directions P r).card) = 4 * P.card := by
    calc
      _ = ∑ q ∈ P, (S.filter fun r => (hypercube 8).Adj r q).card := by
        simpa only [directions_card, bipartiteAbove, bipartiteBelow] using
          (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := S) (t := P) (hypercube 8).Adj)
      _ = ∑ q ∈ P, (directions S q).card := by
        apply sum_congr rfl
        intro q _
        rw [directions_card]
        congr 1
        ext r
        simp only [mem_filter]
        rw [(hypercube 8).adj_comm r q]
      _ = _ := by
        rw [sum_congr rfl hcol]
        simp [Nat.mul_comm]
  have hfirst : contactCount P S 1 + 2 * contactCount P S 2 + 3 * contactCount P S 3 =
      4 * P.card := by
    simpa only [one_mul] using ((sum_contacts P S (fun k => k) rfl hdeg).symm.trans hinc)
  have hnorm : (∑ q, (switchingVector P s q) ^ 2) = (P.card : ℝ) := by
    calc
      _ = ∑ q ∈ P, (switchingVector P s q) ^ 2 := by
        symm
        apply sum_subset (subset_univ _)
        intro q _ hq
        simp [switchingVector, hq]
      _ = ∑ _q ∈ P, (1 : ℝ) := by
        apply sum_congr rfl
        intro q hq
        simpa only [switchingVector, ite_eq_left hq] using hunit q hq
      _ = _ := by simp
  have htotal : (∑ r, H r ^ 2) = 8 * (P.card : ℝ) := by
    simpa [H, hnorm] using huang_energy 8 (switchingVector P s)
  have hsplit : (∑ r, H r ^ 2) = (∑ r ∈ S, H r ^ 2) + ∑ r ∈ E, H r ^ 2 := by
    rw [← sum_union hdisj]
    symm
    apply sum_subset (subset_univ _)
    intro r _ hr
    have hzero : H r = 0 := by
      change (huangMatrix 8).mulVec (switchingVector P s) r = 0
      rw [paired_row]
      apply sum_eq_zero
      intro i hi
      exact (hr (hcover r i ((mem_directions P r i).mp hi))).elim
    simp [hzero]
  have hsingle : (∑ r ∈ S, H r ^ 2) =
      (contactCount P S 1 : ℝ) + 4 * (contactCount P S 2 : ℝ) +
        9 * (contactCount P S 3 : ℝ) := by
    calc
      _ = ∑ r ∈ S, ((directions P r).card : ℝ) ^ 2 := by
        apply sum_congr rfl
        intro r hr
        obtain ⟨t, ht, hi⟩ := hrow r hr
        change ((huangMatrix 8).mulVec (switchingVector P s) r) ^ 2 = _
        rw [paired_row, sum_congr rfl hi, sum_const, nsmul_eq_mul, mul_pow, ht, mul_one]
      _ = _ := by
        have hm := sum_contacts P S (fun k => k ^ 2) rfl hdeg
        change (∑ r ∈ S, (directions P r).card ^ 2) =
          1 * contactCount P S 1 + 4 * contactCount P S 2 + 9 * contactCount P S 3 at hm
        rw [one_mul] at hm
        exact_mod_cast hm
  have hfirstReal : (contactCount P S 1 : ℝ) + 2 * (contactCount P S 2 : ℝ) +
      3 * (contactCount P S 3 : ℝ) = 4 * (P.card : ℝ) := by
    exact_mod_cast hfirst
  have henergy : (contactCount P S 1 : ℝ) - 3 * (contactCount P S 3 : ℝ) =
      ∑ r ∈ E, H r ^ 2 := by
    rw [hsingle] at hsplit
    linarith only [hfirstReal, htotal, hsplit]
  have hnonneg : 0 ≤ ∑ r ∈ E, H r ^ 2 := sum_nonneg fun r _ => sq_nonneg (H r)
  have hcompareReal : 3 * (contactCount P S 3 : ℝ) ≤ (contactCount P S 1 : ℝ) := by
    linarith only [henergy, hnonneg]
  have hcompare : 3 * contactCount P S 3 ≤ contactCount P S 1 := by
    exact_mod_cast hcompareReal
  exact ⟨hfirst, henergy, hcompare, by omega⟩

/-- Fibres of parity `p` with exactly one of their first-coordinate lifts selected. -/
private def firstAxisSingleFibres (C : Finset (Q 9)) (p : Bool) : Finset (Q 8) :=
  univ.filter fun r => cubeParity r = p ∧
    ((Fin.cons false r ∈ C ∧ Fin.cons true r ∉ C) ∨
     (Fin.cons true r ∈ C ∧ Fin.cons false r ∉ C))

/-- Fibres with neither first-coordinate lift selected. -/
private def emptyFibres (C : Finset (Q 9)) : Finset (Q 8) :=
  univ.filter fun r => Fin.cons false r ∉ C ∧ Fin.cons true r ∉ C

private theorem mem_paired {C : Finset (Q 9)} {p : Bool} {q : Q 8} :
    q ∈ doubleFibres C 0 p ↔
      (Fin.cons false q ∈ C ∧ Fin.cons true q ∈ C) ∧ cubeParity q = p := by
  simp only [doubleFibres, mem_filter, mem_univ, true_and, liftVertex, Fin.insertNth_zero',
    cubeParity]

private theorem mem_single {C : Finset (Q 9)} {p : Bool} {q : Q 8} :
    q ∈ firstAxisSingleFibres C p ↔ cubeParity q = p ∧
      ((Fin.cons false q ∈ C ∧ Fin.cons true q ∉ C) ∨
       (Fin.cons true q ∈ C ∧ Fin.cons false q ∉ C)) := by
  simp only [firstAxisSingleFibres, mem_filter, mem_univ, true_and]

private theorem mem_empty {C : Finset (Q 9)} {q : Q 8} :
    q ∈ emptyFibres C ↔ Fin.cons false q ∉ C ∧ Fin.cons true q ∉ C := by
  simp only [emptyFibres, mem_filter, mem_univ, true_and]

private theorem opposite_parity (q : Q 8) (i : Fin 8) (p : Bool)
    (h : cubeParity q = p) : cubeParity (BalancedCriticalSpectrum.flip q i) = !p :=
  (parity_flip q i).trans (congrArg Bool.not h)

private theorem no_adjacent_pairs {C : Finset (Q 9)} (hb : BalancedCriticalSpectrum.IsBalanced C)
    {q : Q 8} (hf : Fin.cons false q ∈ C) (ht : Fin.cons true q ∈ C) (i : Fin 8) :
    ¬ (Fin.cons false (BalancedCriticalSpectrum.flip q i) ∈ C ∧ Fin.cons true (BalancedCriticalSpectrum.flip q i) ∈ C) := by
  rintro ⟨hf', ht'⟩
  have hi : (0 : Fin 9) ≠ i.succ := (Fin.succ_ne_zero i).symm
  exact BalancedCubeGirth.no_selected_square hb hi hf
    (by simpa only [flip_cons_zero, Bool.not_false] using ht)
    (by simpa only [flip_cons_succ] using hf')
    (by simpa only [flip_cons_zero, Bool.not_false, flip_cons_succ] using ht')

private theorem tail_degree_of_pair {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {q : Q 8} {b : Bool} (hq : Fin.cons b q ∈ C) (hm : Fin.cons (!b) q ∈ C) :
    (univ.filter fun i : Fin 8 => Fin.cons b (BalancedCriticalSpectrum.flip q i) ∈ C).card = 2 := by
  let A := directions C (Fin.cons b q)
  have hzero : (0 : Fin 9) ∈ A :=
    (mem_directions C (Fin.cons b q) 0).mpr (by simpa only [flip_cons_zero] using hm)
  have hcard : (A.erase 0).card = 2 := by
    rw [card_erase_of_mem hzero, show A.card = 3 from regular_directions C hr hq]
  rw [← hcard]
  apply card_bij (fun i _ => Fin.succ i)
  · intro i hi
    exact mem_erase.mpr ⟨Fin.succ_ne_zero i, (mem_directions C (Fin.cons b q) i.succ).mpr
      (by simpa only [flip_cons_succ] using (mem_filter.mp hi).2)⟩
  · intro i _ j _ hij
    exact Fin.succ_injective 8 hij
  · intro j hj
    induction j using Fin.cases with
    | zero => exact ((mem_erase.mp hj).1 rfl).elim
    | succ i =>
      have hi := (mem_directions C (Fin.cons b q) i.succ).mp (mem_erase.mp hj).2
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, by simpa only [flip_cons_succ] using hi⟩, rfl⟩

private theorem paired_column {C : Finset (Q 9)} {p : Bool}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C) {q : Q 8} (hq : q ∈ doubleFibres C 0 p) :
    (directions (firstAxisSingleFibres C (!p)) q).card = 4 := by
  obtain ⟨⟨hf, ht⟩, hp⟩ := mem_paired.mp hq
  let A := univ.filter fun i : Fin 8 => Fin.cons false (BalancedCriticalSpectrum.flip q i) ∈ C
  let B := univ.filter fun i : Fin 8 => Fin.cons true (BalancedCriticalSpectrum.flip q i) ∈ C
  have hdisj : Disjoint A B := disjoint_left.mpr fun i hi hj =>
    no_adjacent_pairs hb hf ht i ⟨(mem_filter.mp hi).2, (mem_filter.mp hj).2⟩
  have hset : directions (firstAxisSingleFibres C (!p)) q = A ∪ B := by
    ext i
    have hn := no_adjacent_pairs hb hf ht i
    simp only [mem_directions, mem_single, opposite_parity q i p hp, eq_self, true_and,
      mem_union, A, B, mem_filter, mem_univ]
    tauto
  have hA : A.card = 2 := tail_degree_of_pair hr hf ht
  have hB : B.card = 2 := tail_degree_of_pair hr ht hf
  rw [hset, card_union_of_disjoint hdisj, hA, hB]

private theorem same_pair_sign {C : Finset (Q 9)} {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {q : Q 8} (hf : Fin.cons false q ∈ C) (ht : Fin.cons true q ∈ C) :
    σ (Fin.cons true q) = σ (Fin.cons false q) := by
  have hsedge := hs.2 (Fin.cons false q) hf (BalancedCriticalSpectrum.flip (Fin.cons false q) 0)
    (by simpa only [flip_cons_zero, Bool.not_false] using ht) (flip_adj _ _)
  rw [matrix_flip_zero, flip_cons_zero, Bool.not_false] at hsedge
  calc
    _ = σ (Fin.cons false q) ^ 2 * σ (Fin.cons true q) := by rw [switching_sq hs hf, one_mul]
    _ = σ (Fin.cons false q) * (σ (Fin.cons false q) * σ (Fin.cons true q)) := by ring
    _ = _ := by rw [← hsedge, mul_one]

private theorem coherent_entry {C : Finset (Q 9)} {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {b : Bool} {r : Q 8} (hr : Fin.cons b r ∈ C) (i : Fin 8)
    (hf : Fin.cons false (BalancedCriticalSpectrum.flip r i) ∈ C) (ht : Fin.cons true (BalancedCriticalSpectrum.flip r i) ∈ C) :
    huangMatrix 8 r (BalancedCriticalSpectrum.flip r i) * σ (Fin.cons false (BalancedCriticalSpectrum.flip r i)) =
      (if b then 1 else -1) * σ (Fin.cons b r) := by
  have hq : Fin.cons b (BalancedCriticalSpectrum.flip r i) ∈ C := by cases b <;> assumption
  have hbit : σ (Fin.cons false (BalancedCriticalSpectrum.flip r i)) = σ (Fin.cons b (BalancedCriticalSpectrum.flip r i)) := by
    cases b
    · rfl
    · exact (same_pair_sign hs hf ht).symm
  have hπ : Sensitivity.π (Fin.cons b r) = r :=
    Fin.tail_cons (α := fun _ : Fin 9 => Bool) b r
  have hsedge := hs.2 (Fin.cons b r) hr (BalancedCriticalSpectrum.flip (Fin.cons b r) i.succ)
    (by simpa only [flip_cons_succ] using hq) (flip_adj _ _)
  rw [matrix_flip_succ, Fin.cons_zero, hπ, flip_cons_succ] at hsedge
  let t : ℝ := if b then 1 else -1
  have ht2 : t ^ 2 = 1 := by cases b <;> norm_num [t]
  change t * huangMatrix 8 r (BalancedCriticalSpectrum.flip r i) =
    σ (Fin.cons b r) * σ (Fin.cons b (BalancedCriticalSpectrum.flip r i)) at hsedge
  rw [hbit]
  calc
    _ = t ^ 2 * (huangMatrix 8 r (BalancedCriticalSpectrum.flip r i) * σ (Fin.cons b (BalancedCriticalSpectrum.flip r i))) := by
      rw [ht2, one_mul]
    _ = t * ((t * huangMatrix 8 r (BalancedCriticalSpectrum.flip r i)) * σ (Fin.cons b (BalancedCriticalSpectrum.flip r i))) := by ring
    _ = t * (σ (Fin.cons b r) * σ (Fin.cons b (BalancedCriticalSpectrum.flip r i)) ^ 2) := by rw [hsedge]; ring
    _ = _ := by rw [switching_sq hs hq, mul_one]

/-- The sole axis hypothesis is that the paired fibres use coordinate zero.
The statement uses the actual selected cubic support and a fixed projected parity. -/
private theorem paired_fibre_energy {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (p : Bool) :
    ContactBudget (doubleFibres C 0 p) (firstAxisSingleFibres C (!p)) (emptyFibres C)
      (fun q => σ (Fin.cons false q)) := by
  let P := doubleFibres C 0 p
  let S := firstAxisSingleFibres C (!p)
  have hselected (r : Q 8) (hrS : r ∈ S) : ∃ b : Bool, Fin.cons b r ∈ C := by
    rcases (mem_single.mp hrS).2 with h | h
    · exact ⟨false, h.1⟩
    · exact ⟨true, h.1⟩
  apply paired_fibre_energy_of_incidence
  · apply disjoint_left.mpr
    intro r hrS hrE
    obtain ⟨b, hb⟩ := hselected r hrS
    cases b
    · exact (mem_empty.mp hrE).1 hb
    · exact (mem_empty.mp hrE).2 hb
  · intro q hq
    exact switching_sq hs (mem_paired.mp hq).1.1
  · intro q hq
    exact paired_column hr ⟨σ, hs⟩ hq
  · intro r hrS
    obtain ⟨b, hb⟩ := hselected r hrS
    rw [← regular_directions C hr hb]
    apply card_le_card_of_injOn Fin.succ
    · intro i hi
      have hq := (mem_paired.mp ((mem_directions P r i).mp hi)).1
      apply (mem_directions C (Fin.cons b r) i.succ).mpr
      rw [flip_cons_succ]
      cases b
      · exact hq.1
      · exact hq.2
    · intro i _ j _ hij
      exact Fin.succ_injective 8 hij
  · intro r i hq
    obtain ⟨⟨hf, ht⟩, hp⟩ := mem_paired.mp hq
    have hpar : cubeParity r = !p := by
      simpa only [BalancedCriticalSpectrum.flip_flip] using opposite_parity (BalancedCriticalSpectrum.flip r i) i p hp
    have hn : ¬ (Fin.cons false r ∈ C ∧ Fin.cons true r ∈ C) := by
      simpa only [BalancedCriticalSpectrum.flip_flip] using
        no_adjacent_pairs ⟨σ, hs⟩ hf ht i
    by_cases hrf : Fin.cons false r ∈ C <;> by_cases hrt : Fin.cons true r ∈ C
    · exact (hn ⟨hrf, hrt⟩).elim
    · exact mem_union_left _ (mem_single.mpr ⟨hpar, Or.inl ⟨hrf, hrt⟩⟩)
    · exact mem_union_left _ (mem_single.mpr ⟨hpar, Or.inr ⟨hrt, hrf⟩⟩)
    · exact mem_union_right _ (mem_empty.mpr ⟨hrf, hrt⟩)
  · intro r hrS
    obtain ⟨b, hb⟩ := hselected r hrS
    refine ⟨(if b then 1 else -1) * σ (Fin.cons b r), ?_, ?_⟩
    · rw [mul_pow, switching_sq hs hb, mul_one]
      cases b <;> norm_num
    · intro i hi
      have hq := (mem_paired.mp ((mem_directions P r i).mp hi)).1
      exact coherent_entry hs hb i hq.1 hq.2


end FirstAxis

section AnyAxis

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (directions)
open HuangBalancedSymmetry (cube_action_regular_balanced)
open Q9OccupiedFibreParity (doubleFibres)
open private liftVertex from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private reindex reindex_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

attribute [local instance] Classical.propDecidable

/-- Projected fibres of parity `p` with exactly one selected lift along `i`. -/
def singleFibres (C : Finset (Q 9)) (i : Fin 9) (p : Bool) : Finset (Q 8) :=
  univ.filter fun q => cubeParity q = p ∧
    ((liftVertex i false q ∈ C ∧ liftVertex i true q ∉ C) ∨
     (liftVertex i true q ∈ C ∧ liftVertex i false q ∉ C))

theorem mem_singleFibres {C : Finset (Q 9)} {i : Fin 9} {p : Bool} {q : Q 8} :
    q ∈ singleFibres C i p ↔ cubeParity q = p ∧
      ((liftVertex i false q ∈ C ∧ liftVertex i true q ∉ C) ∨
       (liftVertex i true q ∈ C ∧ liftVertex i false q ∉ C)) := by
  simp only [singleFibres, mem_filter, mem_univ, true_and]

/-- Move `i` to zero and preserve the order of the remaining eight coordinates. -/
private def axisToZero (i : Fin 9) : Fin 9 ≃ Fin 9 :=
  (finSuccEquiv' i).trans (finSuccEquiv 8).symm

private theorem axisToZero_symm_zero (i : Fin 9) : (axisToZero i).symm 0 = i := by
  change (finSuccEquiv' i).symm (finSuccEquiv 8 0) = i
  simp only [finSuccEquiv_zero, finSuccEquiv'_symm_none]

private theorem axisToZero_symm_succ (i : Fin 9) (k : Fin 8) :
    (axisToZero i).symm k.succ = i.succAbove k := by
  change (finSuccEquiv' i).symm (finSuccEquiv 8 k.succ) = i.succAbove k
  simp only [finSuccEquiv_succ, finSuccEquiv'_symm_some]

private theorem reindex_lift (i : Fin 9) (b : Bool) (q : Q 8) :
    reindex (axisToZero i) (liftVertex i b q) = Fin.cons b q := by
  funext j
  change liftVertex i b q ((axisToZero i).symm j) = (Fin.cons b q : Q 9) j
  induction j using Fin.cases with
  | zero =>
    simpa only [axisToZero_symm_zero, Fin.cons_zero] using
      (Fin.insertNth_apply_same (α := fun _ : Fin 9 => Bool) i b q)
  | succ k =>
    simpa only [axisToZero_symm_succ, Fin.cons_succ] using
      (Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) i b q k)

private theorem mem_image_cons_iff (C : Finset (Q 9)) (i : Fin 9) (b : Bool) (q : Q 8) :
    Fin.cons b q ∈ C.image (reindex (axisToZero i)) ↔ liftVertex i b q ∈ C := by
  constructor
  · intro h
    obtain ⟨x, hx, hxe⟩ := mem_image.mp h
    have he : x = liftVertex i b q :=
      (reindex (axisToZero i)).injective (hxe.trans (reindex_lift i b q).symm)
    exact he ▸ hx
  · intro h
    exact mem_image.mpr ⟨liftVertex i b q, h, reindex_lift i b q⟩

private theorem doubleFibres_reindex (C : Finset (Q 9)) (i : Fin 9) (p : Bool) :
    doubleFibres (C.image (reindex (axisToZero i))) 0 p = doubleFibres C i p := by
  ext q
  simp only [doubleFibres, mem_filter, mem_univ, true_and, liftVertex,
    Fin.insertNth_zero', mem_image_cons_iff]

private theorem singleFibres_reindex (C : Finset (Q 9)) (i : Fin 9) (p : Bool) :
    firstAxisSingleFibres (C.image (reindex (axisToZero i))) p =
      singleFibres C i p := by
  ext q
  simp only [firstAxisSingleFibres, mem_singleFibres, mem_filter, mem_univ,
    true_and, mem_image_cons_iff]

/-- For a balanced cubic Q9 support, three times the number of opposite-parity
single fibres touching exactly three paired fibres of projected parity `p` is at most
twice the size of that paired class. All fibres are taken along the actual axis `i`. -/
theorem triple_contact_card_le {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (i : Fin 9) (p : Bool) :
    3 * ((singleFibres C i (!p)).filter
      (fun q => (directions (doubleFibres C i p) q).card = 3)).card ≤
      2 * (doubleFibres C i p).card := by
  obtain ⟨hr', hb'⟩ := cube_action_regular_balanced (reindex (axisToZero i))
    (axisToZero i) (reindex_flip (axisToZero i)) hr hb
  obtain ⟨σ, hs⟩ := hb'
  have budget := paired_fibre_energy hr' hs p
  have hinc := budget.incidence
  have hcompare := budget.triple_le_one
  simp only [doubleFibres_reindex, singleFibres_reindex] at hinc hcompare
  have hcount : contactCount (doubleFibres C i p) (singleFibres C i (!p)) 3 =
      ((singleFibres C i (!p)).filter
        (fun q => (directions (doubleFibres C i p) q).card = 3)).card := by
    rfl
  rw [← hcount]
  omega


end AnyAxis

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairedFibreAnyAxis
