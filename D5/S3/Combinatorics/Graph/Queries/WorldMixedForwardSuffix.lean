/- GID: D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: A uniform lower bound on the number of fresh positions in a world-dependent suffix yields a conditional probability bound after mixing worlds. -/

import D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw
open D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix

variable {P V W : Type*} [Fintype P] [DecidableEq P]

private theorem tail_mass_le
    (choices : P → Bool → V) (hChoice : ∀ p, Function.Injective (choices p))
    (earlier later : P → Bool → Option V) (seen fresh : Finset P)
    (hDisjoint : Disjoint seen fresh)
    (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (hFresh : ∀ p, p ∈ fresh ↔ ∃ b v, later p b = some v) :
    let table := uniformPmf (P → Equiv.Perm Bool)
    let E : Set (P → Equiv.Perm Bool) := {f | Matches choices earlier f}
    let S : Set (P → Equiv.Perm Bool) := {f | Matches choices later f}
    table.toOuterMeasure (E ∩ S) ≤ table.toOuterMeasure E *
      ((2 ^ fresh.card : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  intro table E S
  by_cases hCompatible : Compatible choices earlier
  · have hEq := suffix_after_prefix choices hChoice earlier later seen fresh
      hDisjoint hSeen hFresh hCompatible
    change table.toOuterMeasure (E ∩ S) / table.toOuterMeasure E =
      _ at hEq
    have hFinite : table.toOuterMeasure E ≠ ∞ := by
      rw [PMF.toOuterMeasure_apply]
      exact table.tsum_coe_indicator_ne_top E
    have hPositive : table.toOuterMeasure E ≠ 0 := by
      change (uniformPmf (P → Equiv.Perm Bool)).toOuterMeasure {f | Matches choices earlier f} ≠ 0
      rw [partial_forward_order_likelihood choices hChoice earlier seen hSeen, ite_eq_left hCompatible]
      simp
    rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hPositive) (Or.inl hFinite), hEq]
    split_ifs <;> simp
  · have hZero : table.toOuterMeasure E = 0 := by
      change (uniformPmf (P → Equiv.Perm Bool)).toOuterMeasure {f | Matches choices earlier f} = 0
      rw [partial_forward_order_likelihood choices hChoice earlier seen hSeen, ite_eq_right hCompatible]
    have hMono : table.toOuterMeasure (E ∩ S) ≤ table.toOuterMeasure E :=
      table.toOuterMeasure.mono Set.inter_subset_left
    simpa only [hZero, zero_mul] using hMono

/-- The mass of a compatible observation at a fixed number of fresh positions. -/
noncomputable def suffixWeight (n : ℕ) : ℝ≥0∞ := ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹

/-- A fresh suffix can depend on the graph world. The same conditional bound
survives averaging after a partial table has been observed. -/
theorem joint_fresh_suffix_bound
    (π : PMF W) (choices : W → P → Bool → V)
    (hChoice : ∀ w p, Function.Injective (choices w p))
    (earlier : P → Bool → Option V) (later : W → P → Bool → Option V)
    (seen : Finset P) (fresh : W → Finset P)
    (hDisjoint : ∀ w, Disjoint seen (fresh w))
    (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (hFresh : ∀ w p, p ∈ fresh w ↔ ∃ b v, later w p b = some v)
    (n : ℕ) (B : Set W) (hLength : ∀ w ∈ B, n ≤ (fresh w).card) :
    let Ω := P → Equiv.Perm Bool
    let table := uniformPmf Ω
    let μ : PMF (W × Ω) := π.bind fun w => table.map (Prod.mk w)
    let E : Set (W × Ω) := {x | Matches (choices x.1) earlier x.2}
    let F : Set (W × Ω) := {x | Matches (choices x.1) (later x.1) x.2}
    let weight := suffixWeight n
    μ.toOuterMeasure ((E ∩ Prod.fst ⁻¹' B) ∩ F) / μ.toOuterMeasure E ≤
      (μ.toOuterMeasure (E ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure E) *
        weight := by
  classical
  intro Ω table μ E F weight
  let event := E ∩ Prod.fst ⁻¹' B
  have hMass : ∀ s : Set (W × Ω), μ.toOuterMeasure s =
      ∑' w, π w * table.toOuterMeasure (Prod.mk w ⁻¹' s) := by
    intro s
    simp only [μ, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  have hPoint (w : W) :
      table.toOuterMeasure (Prod.mk w ⁻¹' (event ∩ F)) ≤
        table.toOuterMeasure (Prod.mk w ⁻¹' event) * weight := by
    by_cases hw : w ∈ B
    · have hs : Prod.mk w ⁻¹' event = {f | Matches (choices w) earlier f} := by
        ext f
        change (Matches (choices w) earlier f ∧ w ∈ B) ↔ Matches (choices w) earlier f
        simp [hw]
      rw [Set.preimage_inter, hs]
      have ht := tail_mass_le (choices w) (hChoice w) earlier (later w) seen (fresh w)
        (hDisjoint w) hSeen (hFresh w)
      change table.toOuterMeasure
        ({f | Matches (choices w) earlier f} ∩ {f | Matches (choices w) (later w) f}) ≤ _
      have hWeight : ((2 ^ (fresh w).card : ℕ) : ℝ≥0∞)⁻¹ ≤ weight := by
        apply ENNReal.inv_le_inv.mpr
        exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (hLength w hw)
      refine ht.trans ?_
      gcongr
    · have hn : Prod.mk w ⁻¹' event = ∅ := by
        ext f
        simp [event, hw]
      rw [Set.preimage_inter, hn]
      simp
  have hBound : μ.toOuterMeasure (event ∩ F) ≤ μ.toOuterMeasure event * weight := by
    rw [hMass, hMass, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum ?_
    intro w
    rw [mul_assoc]
    gcongr
    exact hPoint w
  change μ.toOuterMeasure (event ∩ F) / μ.toOuterMeasure E ≤
    (μ.toOuterMeasure event / μ.toOuterMeasure E) * weight
  calc
    _ ≤ (μ.toOuterMeasure event * weight) / μ.toOuterMeasure E := by
      simp only [div_eq_mul_inv]
      gcongr
    _ = _ := by
      simp only [div_eq_mul_inv, mul_assoc]
      rw [mul_comm weight]

end D5.S3.Combinatorics.Graph.Queries.WorldMixedForwardSuffix
