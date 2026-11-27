/- GID: D5/S3/StatisticalMechanics/HardCore/FerrersResultant
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/FerrersResultant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: An exact all-partition stability criterion for the actual Ferrers graph. -/

import D5.S3.StatisticalMechanics.HardCore.FerrersGraphCount
import D5.S3.Analytic.Polynomial.PairSumStability

/-!
# Stability of Ferrers independence polynomials

An integer coefficient test decides closed stability for every positive partition.
-/

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.FerrersResultant

open Finset Polynomial FerrersGraphCount
open D5.S3.Analytic.Polynomial.PairSumStability
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open scoped BigOperators

variable {n : ℕ}

/-- The number of free vertices after choosing row i as the least selected row. -/
def rowExponent (m : ℕ) (rowLength : Fin n → ℕ) (i : Fin n) : ℕ :=
  n - 1 - i.val + (m - rowLength i)

/-- The integer polynomial given by the partition formula. -/
noncomputable def explicitPolynomial (m : ℕ) (rowLength : Fin n → ℕ) : ℤ[X] :=
  (1 + X) ^ m + X * ∑ i, (1 + X) ^ rowExponent m rowLength i

/-- Maximum size among the column-only case and all least-row cases. -/
def degreeBound (m : ℕ) (rowLength : Fin n → ℕ) : ℕ :=
  max m (univ.sup fun i => rowExponent m rowLength i + 1)

private theorem graph_degree_leading (m : ℕ) (rowLength : Fin n → ℕ)
    (hrow : Antitone rowLength) :
    let p := independencePolynomial (graph m rowLength) univ
    p.natDegree = degreeBound m rowLength ∧ 0 < p.leadingCoeff := by
  intro p
  have hcount (k : ℕ) : p.coeff k = ((graph m rowLength).indepSetFinset k).card :=
    coeff_independencePolynomial_eq_card_indepSetFinset _ _
  have hcoeff (k : ℕ) : p.coeff (k + 1) =
      ↑(m.choose (k + 1) + ∑ i, (rowExponent m rowLength i).choose k) := by
    rw [hcount, card_indepSetFinset_ferrers_succ rowLength hrow]
    rfl
  have hpow (k : ℕ) : ((1 + X : ℤ[X]) ^ k).natDegree = k := by
    simp
  have hupper : p.natDegree ≤ degreeBound m rowLength := by
    change (independencePolynomial (graph m rowLength) univ).natDegree ≤ _
    rw [independencePolynomial_ferrers rowLength hrow, Finset.mul_sum]
    apply (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [hpow]
      exact le_max_left _ _
    · apply natDegree_sum_le_of_forall_le
      intro i hi
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X, hpow, Nat.add_comm]
      exact (Finset.le_sup (f := fun i => rowExponent m rowLength i + 1) hi).trans
        (le_max_right _ _)
  have hcolumns : m ≤ p.natDegree := by
    by_cases hm : m = 0
    · simp [hm]
    have hs : m - 1 + 1 = m := by omega
    have hc := hcoeff (m - 1)
    rw [hs, Nat.choose_self] at hc
    apply le_natDegree_of_ne_zero
    rw [hc]
    positivity
  have hrows : (univ.sup fun i => rowExponent m rowLength i + 1) ≤ p.natDegree := by
    apply Finset.sup_le
    intro i hi
    rw [← Nat.succ_eq_add_one]
    apply le_natDegree_of_ne_zero
    rw [Nat.succ_eq_add_one, hcoeff]
    have hsum : 0 < ∑ j : Fin n, (rowExponent m rowLength j).choose
        (rowExponent m rowLength i) :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i, hi, by simp⟩
    positivity
  have hp0 : p ≠ 0 := by
    intro hz
    have hc := hcount 0
    rw [hz, coeff_zero, card_indepSetFinset_zero] at hc
    norm_num at hc
  refine ⟨hupper.antisymm (max_le hcolumns hrows), ?_⟩
  apply lt_of_le_of_ne _ (leadingCoeff_ne_zero.mpr hp0).symm
  rw [← coeff_natDegree, hcount]
  positivity

/-- The closed stability criterion for Question 4.1, together with its
coefficient, degree, origin, and imaginary-axis statements. -/
def claim : Prop :=
  ∀ (k : ℕ) (rowLength : Fin (k + 1) → ℕ),
    Antitone rowLength → (∀ i, 0 < rowLength i) →
    let m := rowLength 0
    let G := graph m rowLength
    let p := independencePolynomial G univ
    let d := degreeBound m rowLength
    let r := sumResultant (explicitPolynomial m rowLength)
    p = explicitPolynomial m rowLength ∧
      (∀ j : ℕ, p.coeff j = (G.indepSetFinset j).card) ∧
      (G.indepSetFinset 0).card = 1 ∧
      (∀ j : ℕ, (G.indepSetFinset (j + 1)).card =
        m.choose (j + 1) + ∑ i, (rowExponent m rowLength i).choose j) ∧
      0 < d ∧ p.natDegree = d ∧ 0 < p.leadingCoeff ∧
      r.natDegree = d ^ 2 ∧ r.leadingCoeff = p.leadingCoeff ^ (2 * d) ∧
      ((∀ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 → z.re ≤ 0) ↔
        ∀ j : Fin (d ^ 2 + 1), 0 ≤ r.coeff j.val) ∧
      ((∀ j : Fin (d ^ 2 + 1), 0 ≤ r.coeff j.val) →
        (r.coeff 0 = 0 ↔ ∃ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 ∧ z.re = 0)) ∧
      p.coeff 0 = 1

/-- Question 4.1 is decided by the finite coefficient test for every Ferrers partition. -/
theorem result : claim := by
  intro k rowLength hrow hpos m G p d r
  have hp : p = explicitPolynomial m rowLength :=
    independencePolynomial_ferrers rowLength hrow
  obtain ⟨hd, hl⟩ := graph_degree_leading m rowLength hrow
  have hdpos : 0 < d := (hpos 0).trans_le (le_max_left _ _)
  have hr : sumResultant p = r := congrArg _ hp
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp hl.ne'
  obtain ⟨hrd, hrl⟩ := sumResultant_degree_leading
    (Int.castRingHom ℂ) Int.cast_injective p hp0
  have hclosed := closed_iff_sumResultant_coeff_nonneg p hp0
  have hstrict := strict_iff_sumResultant_coeff_nonneg p hp0
  change p.natDegree = d at hd
  rw [hr, hd] at hrd hrl hclosed hstrict
  refine ⟨hp, fun j => coeff_independencePolynomial_eq_card_indepSetFinset G j,
    card_indepSetFinset_zero G, fun j =>
      card_indepSetFinset_ferrers_succ rowLength hrow j,
    hdpos, hd, hl, hrd, hrl, hclosed, ?_, ?_⟩
  swap
  · change (independencePolynomial (graph m rowLength) univ).coeff 0 = 1
    simp only [coeff_independencePolynomial_eq_card_indepSetFinset,
      card_indepSetFinset_zero, Nat.cast_one]
  intro hscan
  constructor
  · intro hzero
    by_contra! hboundary
    have hs (z : ℂ) (hz : p.eval₂ (Int.castRingHom ℂ) z = 0) : z.re < 0 :=
      lt_of_le_of_ne (hclosed.mpr hscan z hz) (hboundary z hz)
    exact (hstrict.mp hs).2.ne' hzero
  · rintro ⟨z, hz, hre⟩
    by_contra hzero
    have hc : 0 < r.coeff 0 := lt_of_le_of_ne (hscan 0) (Ne.symm hzero)
    exact (hstrict.mpr ⟨hscan, hc⟩ z hz).ne hre

end D5.S3.StatisticalMechanics.HardCore.FerrersResultant
