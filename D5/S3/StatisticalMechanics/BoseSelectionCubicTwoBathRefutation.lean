/- GID: D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim; result=D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result; claim=D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.claim
   digest: Two cubic product-coupled baths admit an open set with five Bose-selected modes. -/

import D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation
import D5.S3.Geometry.FiniteCoordinateTruncation

/-! The cubic two-bath family has a strictly positive signed-Pfaffian kernel on a nonempty
open set. This refutes the generic non-Ohmic bound preregistered in issue #25984; the Ohmic
bound and physical realization of the baths are outside the statement. -/

namespace D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation

open scoped BigOperators
open Matrix Set
open D5.S3.Geometry
open D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation (spow)

/-- The source's two-bath rate asymmetry, with the positive factor `2π/ℏ` set to one. -/
noncomputable def asym (d : ℝ) {m : ℕ} (ε F G : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => spow d (ε j - ε i) *
    (FiniteCoordinateTruncation.normalize F i * FiniteCoordinateTruncation.normalize F j -
      FiniteCoordinateTruncation.normalize G i * FiniteCoordinateTruncation.normalize G j)

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

private theorem spectral_three (x : ℝ) : spow 3 x = x ^ 3 := by
  by_cases hx : x = 0
  · simp [spow, hx]
  · simp only [spow, ite_eq_right hx]
    norm_num [Real.rpow_two, sq_abs, pow_succ]; ring

private theorem asym_skew {m : ℕ} (ε F G : Fin m → ℝ) (i j : Fin m) :
    asym 3 ε F G j i = -asym 3 ε F G i j := by
  rw [asym, asym]
  rw [spectral_three, spectral_three]
  rw [FiniteCoordinateTruncation.normalize]
  simp only [FiniteCoordinateTruncation.normalize]
  ring

private theorem pfaffian_kernel (a : Matrix (Fin 5) (Fin 5) ℝ)
    (h : ∀ i j, a j i = -a i j) : a *ᵥ pfaffianVector a = 0 := by
  have hd (i : Fin 5) : a i i = 0 := CharZero.eq_neg_self_iff.mp (h i i)
  rw [pfaffianVector]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pfaffianVector, hd,
      h 0 1, h 0 2, h 0 3, h 0 4, h 1 2, h 1 3, h 1 4, h 2 3, h 2 4, h 3 4] <;>
    ring

private theorem couplingDomain_open : IsOpen couplingDomain := by
  change IsOpen ({p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) |
    ∀ i, 0 < p.2.1 i} ∩ {p | ∀ i, 0 < p.2.2 i})
  simp only [ofPred_forall]
  apply IsOpen.inter <;> apply isOpen_iInter_of_finite <;> intro i <;>
    exact isOpen_lt continuous_const (by fun_prop)

private theorem asym_continuousOn (i j : Fin 5) :
    ContinuousOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      asym 3 p.1 p.2.1 p.2.2 i j) couplingDomain := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hF := FiniteCoordinateTruncation.continuous_normalize
    (f := fun p : couplingDomain => p.val.2.1) continuous_subtype_val.snd.fst
    (fun p => ne_of_gt (Finset.sum_pos (fun k _ => p.property.1 k) Finset.univ_nonempty))
  have hG := FiniteCoordinateTruncation.continuous_normalize
    (f := fun p : couplingDomain => p.val.2.2) continuous_subtype_val.snd.snd
    (fun p => ne_of_gt (Finset.sum_pos (fun k _ => p.property.2 k) Finset.univ_nonempty))
  change Continuous (fun p : couplingDomain => asym 3 p.val.1 p.val.2.1 p.val.2.2 i j)
  simp only [asym, spectral_three]
  exact ((((continuous_apply j).comp continuous_subtype_val.fst).sub
    ((continuous_apply i).comp continuous_subtype_val.fst)).pow 3).mul
      ((((continuous_apply i).comp hF).mul ((continuous_apply j).comp hF)).sub
        (((continuous_apply i).comp hG).mul ((continuous_apply j).comp hG)))

private theorem pfaffian_continuousOn (i : Fin 5) :
    ContinuousOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) =>
      pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i) couplingDomain := by
  have h (j k : Fin 5) := asym_continuousOn j k
  fin_cases i <;> dsimp [pfaffianVector] <;> fun_prop

private theorem neighborhood_open : IsOpen neighborhood := by
  rw [neighborhood]
  have h : IsOpen (⋂ i : Fin 5, couplingDomain ∩
      (fun p => pfaffianVector (asym 3 p.1 p.2.1 p.2.2) i) ⁻¹' Ioi 0) :=
    isOpen_iInter_of_finite fun i =>
      (pfaffian_continuousOn i).isOpen_inter_preimage couplingDomain_open isOpen_Ioi
  convert h using 1
  ext p
  simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage, mem_Ioi]
  exact ⟨fun hp i => ⟨hp.1, hp.2 i⟩, fun hp => ⟨(hp 0).1, fun i => (hp i).2⟩⟩

private theorem base_mem : base ∈ neighborhood := by
  rw [neighborhood, base]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro i <;> fin_cases i <;>
    norm_num [base, pfaffianVector, asym, spectral_three, FiniteCoordinateTruncation.normalize,
      Fin.sum_univ_succ]

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
