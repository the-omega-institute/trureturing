/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A balanced cubic nine-cube support has an even total of odd projected double fibres. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import Mathlib.Algebra.BigOperators.Ring.Nat
import Batteries.Tactic.OpenPrivate

/-!
# Descending-edge parity in the nine-cube

The parity invariant and the unsigned proof are due to GPT-6 Pro
(`../near-pure-84/pro-answer.txt`, Sections 3–4). They exclude the all-axis
13/1 projected double-fibre profile in the study of Hong–Wu–Xia, Section 7,
Problem 2. [arXiv:2610.09483v1](https://arxiv.org/abs/2610.09483v1)

As in `Q9AdjacentHuang`, reduction modulo two erases the Huang signs. Here
we reduce the full integral eigenvector equation before counting the edges.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DescendingEdgeParity

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj flip_apply_same
  switchingVector ambient_eigenvector)
open BalancedCubeComponentBoundary (directions directions_card)
open BalancedCubeGirth (flip_comm)
open Q9FoldedIncidence (restrictCoordinates)
open Q9OccupiedFibreParity (doubleFibres)
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private intA intCoeff intA_cast intCoeff_sign_of_adj intCoeff_zero_of_not_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private card_layer insert_drop flip_insert from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

attribute [local instance] Classical.propDecidable

local notation "flip" => BalancedCriticalSpectrum.flip

private abbrev bit (b : Bool) : ZMod 2 := if b = true then 1 else 0

private def indicator (C : Finset (Q 9)) (x : Q 9) : ZMod 2 :=
  if x ∈ C then 1 else 0

private def evenSide (C : Finset (Q 9)) : Finset (Q 9) :=
  C.filter fun x => cubeParity x = false

/-- Count neighbours in the specified support reached along coordinates with bit `t`.
The choices `false` and `true` give the upper and lower neighbour counts. -/
private def neighbourCount (L : Finset (Q 9)) (t : Bool) (x : Q 9) : ℕ :=
  (univ.filter fun i : Fin 9 => x i = t ∧ flip x i ∈ L).card

private theorem neighbourCount_cast (L : Finset (Q 9)) (t : Bool) (x : Q 9) :
    (neighbourCount L t x : ZMod 2) =
      ∑ i : Fin 9, if x i = t ∧ flip x i ∈ L then 1 else 0 := by
  simp only [neighbourCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem flip_parity (x : Q 9) (i : Fin 9) :
    cubeParity (flip x i) = !cubeParity x := by
  have h := cubeParity_ne_of_adj (flip_adj x i)
  cases hx : cubeParity x <;> cases hy : cubeParity (flip x i) <;> simp_all

private def flipEquiv (i : Fin 9) : Q 9 ≃ Q 9 :=
  (show Function.Involutive (fun x : Q 9 => flip x i) from
    fun x => BalancedCriticalSpectrum.flip_flip x i).toPerm

private theorem sum_bits (x : Q 9) (s : Finset (Fin 9)) :
    (∑ i ∈ s, bit (x i)) = bit (∑ i ∈ s, x i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, ih]
    cases x i <;> cases (∑ j ∈ s, x j) <;> decide

-- Reindex each incidence by its upper endpoint. Its true bits contribute its weight.
private theorem sum_upper_count (C : Finset (Q 9)) :
    (∑ x : Q 9, (neighbourCount (evenSide C) false x : ZMod 2)) = 0 := by
  simp_rw [neighbourCount_cast]
  rw [sum_comm]
  calc
    _ = ∑ i : Fin 9, ∑ y : Q 9, if y i = true ∧ y ∈ evenSide C then (1 : ZMod 2) else 0 := by
      apply sum_congr rfl
      intro i _
      let f : Q 9 → ZMod 2 :=
        fun x => if x i = false ∧ flip x i ∈ evenSide C then 1 else 0
      change (∑ x, f x) = _
      rw [← (flipEquiv i).sum_comp f]
      apply sum_congr rfl
      intro y _
      change f (flip y i) = _
      cases hy : y i <;> simp [f, hy, BalancedCriticalSpectrum.flip_flip]
    _ = 0 := by
      rw [sum_comm]
      apply sum_eq_zero
      intro y _
      by_cases hy : y ∈ evenSide C
      · have hp := (mem_filter.mp hy).2
        simp only [hy, and_true]
        change (∑ i : Fin 9, bit (y i)) = 0
        rw [sum_bits, ← show cubeParity y = ∑ i, y i from rfl, hp]
        decide
      · simp [hy]

-- Record a two-edge path from its upper endpoint, taking direction j first.
private def twoStep (L : Finset (Q 9)) (p : Fin 9 × Fin 9 × Q 9) : ZMod 2 :=
  let (i, j, y) := p
  if i ≠ j ∧ y i = true ∧ y j = true ∧ y ∈ L ∧ flip (flip y j) i ∈ L
  then 1 else 0

private theorem sum_twoStep (L : Finset (Q 9)) :
    (∑ p : Fin 9 × Fin 9 × Q 9, twoStep L p) = 0 := by
  let swap : Fin 9 × Fin 9 × Q 9 → Fin 9 × Fin 9 × Q 9 :=
    fun (i, j, y) => (j, i, y)
  refine sum_involution (fun p _ => swap p) ?_ ?_ (fun _ _ => mem_univ _) ?_
  · rintro ⟨i, j, y⟩ _
    have hs : twoStep L (swap (i, j, y)) = twoStep L (i, j, y) := by
      simp only [twoStep, swap, flip_comm y i j]
      congr 1
      apply propext
      exact ⟨fun ⟨h, hj, hi, hy, hz⟩ => ⟨h.symm, hi, hj, hy, hz⟩,
        fun ⟨h, hi, hj, hy, hz⟩ => ⟨h.symm, hj, hi, hy, hz⟩⟩
    rw [hs]
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  · rintro ⟨i, j, y⟩ _ hn he
    have hij : j = i := congrArg Prod.fst he
    exact hn (by simp [twoStep, hij])
  · rintro ⟨i, j, y⟩ _
    rfl

private theorem sum_mixed_count (L : Finset (Q 9)) :
    (∑ x : Q 9, (neighbourCount L true x : ZMod 2) * neighbourCount L false x) = 0 := by
  let step : Q 9 → Fin 9 → Fin 9 → ZMod 2 := fun x i j =>
    if (x i = true ∧ flip x i ∈ L) ∧ (x j = false ∧ flip x j ∈ L)
    then 1 else 0
  calc
    _ = ∑ x : Q 9, ∑ i : Fin 9, ∑ j : Fin 9, step x i j := by
      apply sum_congr rfl
      intro x _
      simp_rw [neighbourCount_cast, sum_mul, mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hi : x i = true ∧ flip x i ∈ L <;>
        by_cases hj : x j = false ∧ flip x j ∈ L <;> simp [step, hi, hj]
    _ = ∑ i : Fin 9, ∑ j : Fin 9, ∑ x : Q 9, step x i j := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = ∑ i : Fin 9, ∑ j : Fin 9, ∑ y : Q 9, twoStep L (i, j, y) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [← (flipEquiv j).sum_comp (fun x => step x i j)]
      apply sum_congr rfl
      intro y _
      change step (flip y j) i j = _
      by_cases hij : i = j
      · subst j
        cases h : y i <;> simp [step, twoStep, h]
      · have hkeep : flip y j i = y i := Function.update_of_ne hij _ _
        have hflip : flip y j j = false ↔ y j = true := by
          rw [flip_apply_same]
          cases y j <;> decide
        simp only [step, twoStep, hkeep, hflip, BalancedCriticalSpectrum.flip_flip]
        congr 1
        apply propext
        exact ⟨fun ⟨⟨hi, hz⟩, hj, hy⟩ => ⟨hij, hi, hj, hy, hz⟩,
          fun ⟨_, hi, hj, hy, hz⟩ => ⟨⟨hi, hz⟩, hj, hy⟩⟩
    _ = 0 := by
      simpa only [Fintype.sum_prod_type] using sum_twoStep L

private theorem parity_insert_false (i : Fin 9) (z : Q 8) :
    cubeParity (Fin.insertNth (α := fun _ => Bool) i false z) = ∑ j, z j := by
  unfold cubeParity
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  cases (∑ j, z j) <;> decide

private theorem doubleFibres_true_card (C : Finset (Q 9)) (i : Fin 9) :
    (doubleFibres C i true).card =
      (C.filter fun x => x i = false ∧ flip x i ∈ evenSide C).card := by
  let project : Q 9 → Q 8 := restrictCoordinates i.succAboveEmb
  let lift (t : Bool) (z : Q 8) := Fin.insertNth (α := fun _ => Bool) i t z
  have hfilter : doubleFibres C i true =
      univ.filter (fun z => lift false z ∈ C ∧ (lift true z ∈ C ∧ (∑ j, z j) = true)) := by
    ext z
    simp only [doubleFibres, lift, mem_filter, mem_univ, true_and]
    tauto
  rw [hfilter, card_layer C i false (fun z => lift true z ∈ C ∧ (∑ j, z j) = true)]
  congr 1
  ext x
  simp only [mem_filter, evenSide]
  change (x ∈ C ∧ x i = false ∧ lift true (project x) ∈ C ∧ (∑ j, project x j) = true) ↔
    x ∈ C ∧ x i = false ∧ (flip x i ∈ C ∧ cubeParity (flip x i) = false)
  by_cases hx : x i = false
  · have hbase : lift false (project x) = x := by
      simpa only [hx] using insert_drop i x
    have htop : lift true (project x) = flip x i := by
      calc
        lift true (project x) = flip (lift false (project x)) i :=
          (flip_insert i false (project x)).symm
        _ = flip x i := congrArg (fun y => flip y i) hbase
    have hbasePar : cubeParity x = ∑ j, project x j :=
      (congrArg cubeParity hbase).symm.trans (parity_insert_false i (project x))
    have hpar : (∑ j, project x j) = true ↔ cubeParity (flip x i) = false := by
      rw [flip_parity, hbasePar]
      cases (∑ j, project x j) <;> decide
    simp [hx, htop, hpar]
  · simp [hx]

private theorem direction_sum_cast (C : Finset (Q 9)) (x : Q 9) :
    ((directions C x).card : ZMod 2) = ∑ i : Fin 9, indicator C (flip x i) := by
  simp only [directions, indicator, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

private theorem count_product_at_row (C : Finset (Q 9))
    (hrow : ∀ x : Q 9, ((directions C x).card : ZMod 2) = indicator C x)
    (x : Q 9) :
    indicator C x * (neighbourCount (evenSide C) false x : ZMod 2) =
      (neighbourCount (evenSide C) true x : ZMod 2) *
          neighbourCount (evenSide C) false x +
        neighbourCount (evenSide C) false x := by
  cases hx : cubeParity x
  · have hzero : neighbourCount (evenSide C) false x = 0 := by
      unfold neighbourCount
      rw [card_eq_zero]
      ext i
      simp [evenSide, flip_parity, hx]
    simp [hzero]
  · have hsum : (neighbourCount (evenSide C) true x : ZMod 2) +
        neighbourCount (evenSide C) false x = indicator C x := by
      rw [← hrow x, direction_sum_cast]
      simp_rw [neighbourCount_cast, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      cases x i <;> simp [indicator, evenSide, flip_parity, hx]
    rw [← hsum, add_mul]
    congr 1
    generalize (neighbourCount (evenSide C) false x : ZMod 2) = b
    fin_cases b
    · exact zero_mul (0 : ZMod 2)
    · exact one_mul (1 : ZMod 2)

/-- If unsigned neighbour parity agrees with membership, the sum of the
odd projected double-fibre counts is even. -/
theorem even_sum_doubleFibres_true_of_neighbour_parity (C : Finset (Q 9))
    (hrow : ∀ x : Q 9, ((directions C x).card : ZMod 2) =
      (if x ∈ C then 1 else 0 : ZMod 2)) :
    Even (∑ i : Fin 9, (doubleFibres C i true).card) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  push_cast
  simp_rw [doubleFibres_true_card]
  calc
    _ = ∑ i : Fin 9, ∑ x ∈ C, if x i = false ∧ flip x i ∈ evenSide C then (1 : ZMod 2) else 0 := by
      simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = ∑ x : Q 9, indicator C x * (neighbourCount (evenSide C) false x : ZMod 2) := by
      rw [sum_comm]
      simp_rw [← neighbourCount_cast]
      have huniv : univ.filter (fun x => x ∈ C) = C := by ext x; simp
      rw [← huniv, sum_filter]
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ C <;> simp [indicator, hx]
    _ = 0 := by
      simp_rw [count_product_at_row C hrow]
      rw [sum_add_distrib, sum_mixed_count, sum_upper_count, add_zero]

/-- The signed Huang eigenvector of a balanced induced cubic support reduces
to the unsigned adjacency equation over `ZMod 2`. -/
private theorem balanced_neighbour_parity {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x : Q 9) :
    ((directions C x).card : ZMod 2) = indicator C x := by
  obtain ⟨σ, hσ⟩ := hb
  let f : Q 9 → ℤ := fun y => if y ∈ C then if σ y = 1 then 1 else -1 else 0
  have hf : (fun y => (f y : ℝ)) = switchingVector C σ := by
    funext y
    by_cases hy : y ∈ C
    · rcases hσ.1 y hy with hs | hs <;> norm_num [f, switchingVector, hy, hs]
    · simp [f, switchingVector, hy]
  have he : intA f x = 3 * f x := by
    apply Int.cast_injective (α := ℝ)
    have h := congrFun (ambient_eigenvector (d := 3) C σ hr hσ) x
    rw [← hf, ← intA_cast] at h
    simpa only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat] using h
  have hcast (y : Q 9) : (f y : ZMod 2) = indicator C y := by
    by_cases hy : y ∈ C
    · by_cases hs : σ y = 1 <;> simp [f, indicator, hy, hs, show (-1 : ZMod 2) = 1 by decide]
    · simp [f, indicator, hy]
  have hcoeff (y : Q 9) : (intCoeff x y : ZMod 2) =
      if (hypercube 9).Adj x y then 1 else 0 := by
    by_cases hy : (hypercube 9).Adj x y
    · rcases intCoeff_sign_of_adj x y hy with h | h <;> simp [hy, h,
        show (-1 : ZMod 2) = 1 by decide]
    · simp [hy, intCoeff_zero_of_not_adj x y hy]
  have hmod := congrArg (fun a : ℤ => (a : ZMod 2)) he
  simp only [intA, Int.cast_sum, Int.cast_mul, hcast, hcoeff, Int.cast_ofNat,
    show (3 : ZMod 2) = 1 by decide, one_mul] at hmod
  calc
    ((directions C x).card : ZMod 2) =
        ∑ y ∈ C, if (hypercube 9).Adj x y then (1 : ZMod 2) else 0 := by
      simp only [directions_card, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    _ = ∑ y : Q 9, (if (hypercube 9).Adj x y then 1 else 0) * indicator C y := by
      have hfilter : univ.filter (fun y => y ∈ C) = C := by ext y; simp
      conv_lhs => rw [← hfilter, sum_filter]
      apply sum_congr rfl
      intro y _
      by_cases hy : y ∈ C <;> simp [indicator, hy]
    _ = _ := hmod

/-- Every balanced induced cubic support in the nine-cube has an even total
of odd projected double fibres. -/
theorem even_sum_doubleFibres_true {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    Even (∑ i : Fin 9, (doubleFibres C i true).card) :=
  even_sum_doubleFibres_true_of_neighbour_parity C (balanced_neighbour_parity hr hb)

/-- No balanced induced cubic support has a 13/1 double-fibre split on
every axis, in either order on each axis. -/
theorem not_all_axes_split_thirteen_one {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ¬ ∀ i : Fin 9,
      ((doubleFibres C i false).card = 13 ∧ (doubleFibres C i true).card = 1) ∨
      ((doubleFibres C i false).card = 1 ∧ (doubleFibres C i true).card = 13) := by
  intro hp
  have he := even_sum_doubleFibres_true hr hb
  rw [even_sum_iff_even_card_odd] at he
  have hall : (univ.filter (fun i : Fin 9 => Odd (doubleFibres C i true).card)) = univ := by
    apply filter_eq_self.mpr
    intro i _
    rcases hp i with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  rw [hall, card_univ, Fintype.card_fin] at he
  exact (by decide : ¬ Even (9 : ℕ)) he

#print axioms even_sum_doubleFibres_true_of_neighbour_parity
#print axioms even_sum_doubleFibres_true
#print axioms not_all_axes_split_thirteen_one

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9DescendingEdgeParity
