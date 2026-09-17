/- GID: D5/S3/Arith/Congruence/ForestConstraintEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ForestConstraintEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unsatisfiable forest constraints have square-energy at least two thirds. -/

import D5.S3.Arith.Congruence.ExactForestMessages
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.Congruence.ForestConstraintEnergy

open Classical in
/-- The actual mass of pure forbidden values and, when a parent value is
supplied, its binary forbidden fibre. A missing boundary denotes a root. -/
noncomputable def forbiddenMass {V Y : Type*} [DecidableEq Y]
    (domain pureBad : V → Finset Y) (forbidden : V → Y → Y → Prop)
    (weight : V → Y → ℝ) (v : V) (boundary : Option Y) : ℝ :=
  ∑ y ∈ domain v,
    if y ∈ pureBad v ∨ boundary.elim False (fun z => forbidden v z y)
      then weight v y else 0

open Classical in
/-- Every unsatisfiable finite forest of unary and binary constraints has total
conditional square-energy at least two thirds. Each node carries its own fixed
normalized nonnegative weights; roots use their pure forbidden mass squared,
and other nodes average their forbidden fibre mass squared over the parent.
Exact messages, local saturation estimates, and the cubic-potential cancellation
are derived from the actual constraints within the proof. -/
theorem unsatisfiable_forest_square_energy
    {V Y : Type*} [Fintype V] [DecidableEq Y]
    (parent : V → Option V) (level : V → ℕ)
    (parent_level : ∀ v p, parent v = some p → level p < level v)
    (domain pureBad : V → Finset Y) (forbidden : V → Y → Y → Prop)
    (weight : V → Y → ℝ)
    (weight_nonneg : ∀ v y, y ∈ domain v → 0 ≤ weight v y)
    (weight_sum : ∀ v, ∑ y ∈ domain v, weight v y = 1)
    (unsatisfiable : ¬∃ value : V → Y,
      (∀ v, value v ∈ domain v ∧ value v ∉ pureBad v) ∧
      ∀ v p, parent v = some p → ¬forbidden v (value p) (value v)) :
    let α := forbiddenMass domain pureBad forbidden weight
    (2 / 3 : ℝ) ≤ ∑ v, (parent v).elim ((α v none) ^ 2)
      (fun p => ∑ z ∈ domain p, weight p z * (α v (some z)) ^ 2) := by
  classical
  let α := forbiddenMass domain pureBad forbidden weight
  let ε (v : V) : ℝ := (parent v).elim ((α v none) ^ 2)
    (fun p => ∑ z ∈ domain p, weight p z * (α v (some z)) ^ 2)
  change (2 / 3 : ℝ) ≤ ∑ v, ε v
  obtain ⟨A, B, message_eq, allowed_eq, feasible⟩ :=
    ExactForestMessages.exact_forest_message_feasibility
      parent level parent_level domain pureBad forbidden
  let prob (v : V) (P : Y → Prop) : ℝ :=
    ∑ y ∈ domain v, if P y then weight v y else 0
  have prob_bounds (v : V) (P : Y → Prop) : 0 ≤ prob v P ∧ prob v P ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg fun y hy => by
        split_ifs
        · exact weight_nonneg v y hy
        · exact le_refl 0
    · calc
        prob v P ≤ ∑ y ∈ domain v, weight v y := by
          apply Finset.sum_le_sum
          intro y hy
          split_ifs
          · exact le_refl _
          · exact weight_nonneg v y hy
        _ = 1 := weight_sum v
  have alpha_nonneg (v : V) (t : Option Y) : 0 ≤ α v t := by
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact weight_nonneg v y hy
    · exact le_refl 0
  let β (v : V) : ℝ := (parent v).elim (if (A v).Nonempty then 0 else 1)
    (fun p => prob p (fun z => z ∈ B v))
  have beta_bounds (v : V) : 0 ≤ β v ∧ β v ≤ 1 := by
    cases hp : parent v with
    | none => simp only [β, hp, Option.elim_none]; split_ifs <;> norm_num
    | some p => simpa only [β, hp, Option.elim_some] using prob_bounds p (fun z => z ∈ B v)
  let children (v : V) : Finset V := Finset.univ.filter fun w => parent w = some v
  let c (v : V) : ℝ := ∑ w ∈ children v, β w
  have child_beta (v w : V) (hw : w ∈ children v) :
      β w = prob v (fun z => z ∈ B w) := by
    have hp := (Finset.mem_filter.mp hw).2
    simp [β, hp]
  have c_nonneg (v : V) : 0 ≤ c v := Finset.sum_nonneg fun w _ => (beta_bounds w).1
  have energy_nonneg (v : V) : 0 ≤ ε v := by
    cases hp : parent v with
    | none => simp only [ε, hp, Option.elim_none]; positivity
    | some p =>
      simp only [ε, hp, Option.elim_some]
      exact Finset.sum_nonneg fun z hz => mul_nonneg (weight_nonneg p z hz) (sq_nonneg _)
  have cover (v : V) (t : Option Y)
      (blocked : t.elim (¬(A v).Nonempty) (fun z => z ∈ B v)) :
      1 ≤ α v t + c v := by
    have pointwise (y : Y) (hy : y ∈ domain v) :
        weight v y ≤
          (if y ∈ pureBad v ∨ t.elim False (fun z => forbidden v z y)
            then weight v y else 0) +
          ∑ w ∈ children v, if y ∈ B w then weight v y else 0 := by
      have hsum : 0 ≤ ∑ w ∈ children v, if y ∈ B w then weight v y else 0 :=
        Finset.sum_nonneg fun w _ => by
          split_ifs
          · exact weight_nonneg v y hy
          · exact le_refl 0
      by_cases hb : y ∈ pureBad v ∨ t.elim False (fun z => forbidden v z y)
      · simp only [if_pos hb]
        linarith
      · have hout : y ∉ A v := by
          intro ha
          cases t with
          | none => exact blocked ⟨y, ha⟩
          | some z =>
            have hall : ∀ a ∈ A v, forbidden v z a := by
              simpa only [Option.elim_some, message_eq, Set.mem_ofPred_eq] using blocked
            exact hb (Or.inr (hall y ha))
        have hc : ∃ w ∈ children v, y ∈ B w := by
          by_contra hn
          push Not at hn
          apply hout
          rw [allowed_eq]
          refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hy, (not_or.mp hb).1⟩, ?_⟩
          intro w hw
          exact hn w (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)
        obtain ⟨w, hw, hyw⟩ := hc
        have hs := Finset.single_le_sum
          (fun u (_ : u ∈ children v) => show 0 ≤ (if y ∈ B u then weight v y else 0) by
            split_ifs
            · exact weight_nonneg v y hy
            · exact le_refl 0) hw
        simpa only [if_neg hb, if_pos hyw, zero_add] using hs
    calc
      1 = ∑ y ∈ domain v, weight v y := (weight_sum v).symm
      _ ≤ ∑ y ∈ domain v,
          ((if y ∈ pureBad v ∨ t.elim False (fun z => forbidden v z y)
            then weight v y else 0) +
          ∑ w ∈ children v, if y ∈ B w then weight v y else 0) :=
        Finset.sum_le_sum pointwise
      _ = α v t + ∑ w ∈ children v, prob v (fun y => y ∈ B w) := by
        simp only [α, forbiddenMass, prob, Finset.sum_add_distrib]
        rw [Finset.sum_comm]
      _ = α v t + c v := by
        congr 1
        exact Finset.sum_congr rfl fun w hw => (child_beta v w hw).symm
  have saturation (v : V) (hc : c v ≤ 1) : β v * (1 - c v) ^ 2 ≤ ε v := by
    cases hp : parent v with
    | none =>
      simp only [β, ε, hp, Option.elim_none]
      split_ifs with ha
      · simpa only [zero_mul] using sq_nonneg (α v none)
      · have hcover := cover v none ha
        have hα := alpha_nonneg v none
        nlinarith [sq_nonneg (α v none - (1 - c v))]
    | some p =>
      simp only [β, ε, hp, Option.elim_some, prob, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro z hz
      by_cases hB : z ∈ B v
      · simp only [if_pos hB]
        have hcover := cover v (some z) hB
        have hα := alpha_nonneg v (some z)
        have hs : (1 - c v) ^ 2 ≤ (α v (some z)) ^ 2 := by
          nlinarith [sq_nonneg (α v (some z) - (1 - c v))]
        exact mul_le_mul_of_nonneg_left hs (weight_nonneg p z hz)
      · simpa only [if_neg hB, zero_mul] using
          mul_nonneg (weight_nonneg p z hz) (sq_nonneg (α v (some z)))
  let Φ (b : ℝ) : ℝ := b - b ^ 3 / 3
  have phi_lower (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : (2 / 3) * b ≤ Φ b := by
    have h := mul_nonneg (mul_nonneg hb0 (sub_nonneg.mpr hb1)) (by linarith : 0 ≤ 1 + b)
    dsimp [Φ]
    nlinarith
  have phi_nonneg (v : V) : 0 ≤ Φ (β v) :=
    le_trans (mul_nonneg (by norm_num) (beta_bounds v).1)
      (phi_lower (β v) (beta_bounds v).1 (beta_bounds v).2)
  have local_energy (v : V) : Φ (β v) ≤ ε v + ∑ w ∈ children v, Φ (β w) := by
    have hb0 := (beta_bounds v).1
    have hb1 := (beta_bounds v).2
    have hc0 := c_nonneg v
    by_cases hc : c v ≤ 1
    · have cubes : (∑ w ∈ children v, β w ^ 3) ≤ (c v) ^ 3 := by
        calc
          (∑ w ∈ children v, β w ^ 3) ≤ ∑ w ∈ children v, (c v)^2 * β w := by
            apply Finset.sum_le_sum
            intro w hw
            have hwc : β w ≤ c v := Finset.single_le_sum (fun u _ => (beta_bounds u).1) hw
            have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (beta_bounds w).1 hwc 2)
              (beta_bounds w).1
            nlinarith
          _ = (c v) ^ 3 := by rw [← Finset.mul_sum]; dsimp [c]; ring
      have hsum : Φ (c v) ≤ ∑ w ∈ children v, Φ (β w) := by
        simp only [Φ, Finset.sum_sub_distrib]
        rw [← Finset.sum_div]
        change c v - (c v)^3 / 3 ≤ c v - (∑ w ∈ children v, β w ^ 3) / 3
        linarith
      have hlocal : Φ (β v) ≤ β v * (1 - c v)^2 + Φ (c v) := by
        by_cases hbc : β v ≤ c v
        · have hs : 0 ≤ 1 - (c v)^2 := by nlinarith
          have h1 := mul_nonneg (sub_nonneg.mpr hbc) hs
          have h2 := mul_nonneg (sq_nonneg (c v - β v))
            (by linarith : 0 ≤ 2 * c v + β v)
          have h3 := mul_nonneg hb0 (sq_nonneg (1 - c v))
          dsimp [Φ]
          nlinarith
        · have h1 := mul_nonneg hc0 (sq_nonneg (1 - β v))
          have h2 := pow_nonneg (sub_nonneg.mpr (le_of_not_ge hbc)) 3
          dsimp [Φ]
          nlinarith
      linarith [saturation v hc]
    · have hsum : (2 / 3) * c v ≤ ∑ w ∈ children v, Φ (β w) := by
        dsimp only [c]
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun w _ => phi_lower (β w) (beta_bounds w).1 (beta_bounds w).2
      have htop : Φ (β v) ≤ 2 / 3 := by
        have h := mul_nonneg (sq_nonneg (1 - β v)) (by linarith : 0 ≤ β v + 2)
        dsimp [Φ]
        nlinarith
      linarith [energy_nonneg v]
  have telescope : (∑ v, ∑ w ∈ children v, Φ (β w)) =
      ∑ w, (parent w).elim 0 (fun _ => Φ (β w)) := by
    simp only [children, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    cases hp : parent w with
    | none => simp
    | some p => simp
  let rootPotential : ℝ := ∑ v, if parent v = none then Φ (β v) else 0
  have potential_split : (∑ v, Φ (β v)) =
      rootPotential + ∑ v, ∑ w ∈ children v, Φ (β w) := by
    rw [telescope, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    cases hp : parent v with
    | none => simp
    | some p => simp
  have total : rootPotential ≤ ∑ v, ε v := by
    have hs := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => local_energy v
    rw [Finset.sum_add_distrib, potential_split] at hs
    linarith
  have some_failed : ¬∀ v, parent v = none → (A v).Nonempty :=
    fun h => unsatisfiable (feasible.mpr h)
  push Not at some_failed
  obtain ⟨root, hroot, hfailed⟩ := some_failed
  have hroot_beta : β root = 1 := by simp [β, hroot, hfailed]
  have root_lower : (2 / 3 : ℝ) ≤ rootPotential := by
    have hs := Finset.single_le_sum
      (fun v (_ : v ∈ Finset.univ) => show 0 ≤ (if parent v = none then Φ (β v) else 0) by
        split_ifs
        · exact phi_nonneg v
        · exact le_refl 0) (Finset.mem_univ root)
    simpa only [if_pos hroot, hroot_beta, Φ, one_pow, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num]
      using hs
  exact root_lower.trans total

#print axioms unsatisfiable_forest_square_energy

end D5.S3.Arith.Congruence.ForestConstraintEnergy
