/- GID: D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim; result=D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result; claim=D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim
   digest: Two cubic product-coupled baths admit an open set with five Bose-selected modes. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The cubic two-bath family has a strictly positive signed-Pfaffian kernel on a nonempty
open set. This refutes the generic non-Ohmic bound preregistered in issue #25984; the Ohmic
bound and physical realization of the baths are outside the statement. -/

namespace D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open scoped BigOperators
open Matrix Set

/-- The source's odd power-law spectrum, with its positive scale set to one. -/
noncomputable def spectral (d x : ℝ) : ℝ := Real.sign x * |x| ^ d

/-- Squared coupling amplitudes normalized to total weight one. -/
noncomputable def weight {m : ℕ} (F : Fin m → ℝ) (i : Fin m) : ℝ :=
  F i / (∑ k, F k)

/-- The source's two-bath rate asymmetry, with the positive factor `2π/ℏ` set to one. -/
noncomputable def asym (d : ℝ) {m : ℕ} (ε F G : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => spectral d (ε j - ε i) *
    (weight F i * weight F j - weight G i * weight G j)

/-- Equation MS-problem; `w` denotes the source's vector of selected occupations. -/
def IsSelected {m : ℕ} (a : Matrix (Fin m) (Fin m) ℝ) (s : Finset (Fin m))
    (w : Fin m → ℝ) : Prop :=
  ∀ i, (i ∈ s → 0 < w i ∧ (a *ᵥ w) i = 0) ∧
    (i ∉ s → w i = 0 ∧ (a *ᵥ w) i < 0)

/-- Positive two-bath parameters supporting at least four selected modes. -/
def violating (d : ℝ) (m : ℕ) :
    Set ((Fin m → ℝ) × (Fin m → ℝ) × (Fin m → ℝ)) :=
  {p | (∀ i, 0 < p.2.1 i) ∧ (∀ i, 0 < p.2.2 i) ∧
    ∃ s w, IsSelected (asym d p.1 p.2.1 p.2.2) s w ∧ 4 ≤ s.card}

/-- The preregistered generic reading of the expected two-bath bound. -/
def claim : Prop :=
  ∀ d : ℝ, 0 < d → ∀ m : ℕ, interior (violating d m) = ∅

private noncomputable def pfaffianVector (a : Matrix (Fin 5) (Fin 5) ℝ) : Fin 5 → ℝ :=
  ![a 1 2 * a 3 4 - a 1 3 * a 2 4 + a 1 4 * a 2 3,
    -(a 0 2 * a 3 4 - a 0 3 * a 2 4 + a 0 4 * a 2 3),
    a 0 1 * a 3 4 - a 0 3 * a 1 4 + a 0 4 * a 1 3,
    -(a 0 1 * a 2 4 - a 0 2 * a 1 4 + a 0 4 * a 1 2),
    a 0 1 * a 2 3 - a 0 2 * a 1 3 + a 0 3 * a 1 2]

private noncomputable def base :
    (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) :=
  (![1, 2, 3, 4, 5], ![5, 4, 4, 4, 4], ![6, 6, 3, 3, 3])

private def couplingDomain : Set ((Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ)) :=
  {p | (∀ i, 0 < p.2.1 i) ∧ (∀ i, 0 < p.2.2 i)}

private noncomputable def neighborhood :
    Set ((Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ)) :=
  {p | p ∈ couplingDomain ∧ ∀ i, 0 < pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i}

private theorem spectral_three (x : ℝ) : spectral 3 x = x ^ 3 := by
  change Real.sign x * |x| ^ ((3 : ℕ) : ℝ) = x ^ (3 : ℕ)
  rw [Real.rpow_natCast]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · subst x
    norm_num [Real.sign]
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

private theorem asym_skew {m : ℕ} (ε F G : Fin m → ℝ) (i j : Fin m) :
    asym 3 ε F G j i = -asym 3 ε F G i j := by
  unfold asym
  rw [spectral_three, spectral_three]
  ring

private theorem pfaffian_kernel (a : Matrix (Fin 5) (Fin 5) ℝ)
    (h : ∀ i j, a j i = -a i j) : a *ᵥ pfaffianVector a = 0 := by
  have hd (i : Fin 5) : a i i = 0 := by linarith [h i i]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pfaffianVector, hd,
      h 0 1, h 0 2, h 0 3, h 0 4, h 1 2, h 1 3, h 1 4, h 2 3, h 2 4, h 3 4] <;>
    ring

private theorem couplingDomain_open : IsOpen couplingDomain := by
  change IsOpen ({p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) |
    ∀ i, 0 < p.2.1 i} ∩ {p | ∀ i, 0 < p.2.2 i})
  simp only [setOf_forall]
  apply IsOpen.inter <;> apply isOpen_iInter_of_finite <;> intro i <;>
    exact isOpen_lt continuous_const (by fun_prop)

private theorem asym_continuousOn (i j : Fin 5) :
    ContinuousOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      asym 3 p.1 p.2.1 p.2.2 i j) couplingDomain := by
  intro p hp
  have hF : (∑ k, p.2.1 k) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun k _ => hp.1 k) Finset.univ_nonempty)
  have hG : (∑ k, p.2.2 k) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun k _ => hp.2 k) Finset.univ_nonempty)
  apply ContinuousAt.continuousWithinAt
  unfold asym
  simp_rw [spectral_three]
  unfold weight
  fun_prop (disch := assumption)

private theorem pfaffian_continuousOn (i : Fin 5) :
    ContinuousOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i) couplingDomain := by
  have h (j k : Fin 5) := asym_continuousOn j k
  fin_cases i <;> dsimp [pfaffianVector] <;> fun_prop

private theorem neighborhood_open : IsOpen neighborhood := by
  have h : IsOpen (⋂ i : Fin 5, couplingDomain ∩
      (fun p => pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i) ⁻¹' Ioi 0) :=
    isOpen_iInter_of_finite fun i =>
      (pfaffian_continuousOn i).isOpen_inter_preimage couplingDomain_open isOpen_Ioi
  convert h using 1
  ext p
  simp only [neighborhood, mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage, mem_Ioi]
  exact ⟨fun hp i => ⟨hp.1, hp.2 i⟩, fun hp => ⟨(hp 0).1, fun i => (hp i).2⟩⟩

private theorem base_mem : base ∈ neighborhood := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro i <;> fin_cases i <;>
    norm_num [base, pfaffianVector, asym, spectral_three, weight, Fin.sum_univ_succ]

private theorem neighborhood_subset : neighborhood ⊆ violating 3 5 := by
  intro p hp
  refine ⟨hp.1.1, hp.1.2, Finset.univ,
    pfaffianVector (asym 3 p.1 p.2.1 p.2.2), ?_, by decide⟩
  intro i
  constructor
  · intro _
    exact ⟨hp.2 i, congrFun (pfaffian_kernel _ (asym_skew p.1 p.2.1 p.2.2)) i⟩
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem interior_nonempty : (interior (violating 3 5)).Nonempty := by
  exact ⟨base, interior_mono neighborhood_subset
    (neighborhood_open.interior_eq.symm ▸ base_mem)⟩

theorem result : ¬ claim := by
  intro h
  obtain ⟨p, hp⟩ := interior_nonempty
  rw [h 3 (by norm_num) 5] at hp
  exact hp

end D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation
