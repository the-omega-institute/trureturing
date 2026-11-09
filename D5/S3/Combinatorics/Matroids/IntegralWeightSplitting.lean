/- GID: D5/S3/Combinatorics/Matroids/IntegralWeightSplitting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/IntegralWeightSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite matroid exchange inequalities imply integral global base optimality. -/

import D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import D5.S3.Combinatorics.Matroids.FiniteIntersectionPolytope
import Mathlib.Analysis.Convex.KreinMilman

/-! # Integral base optimality and weight splitting -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.IntegralWeightSplitting

open scoped BigOperators
open Set Matroid

universe u
variable {E : Type u} [Finite E]

/-- The actual integral finite sum over a set of carrier elements. -/
noncomputable def weightSum (q : E → ℤ) (B : Set E) : ℤ :=
  ∑ e ∈ B.toFinite.toFinset, q e

/-- Single-element exchange optimality implies optimality against every native base. -/
theorem exchange_local_is_global_minimum (M : Matroid E) (q : E → ℤ)
    {B : Set E} (hB : M.IsBase B)
    (hlocal : ∀ b ∈ B, ∀ e ∈ M.E \ B,
      M.IsBase (insert e (B \ {b})) → q b ≤ q e) :
    ∀ C, M.IsBase C → weightSum q B ≤ weightSum q C := by
  classical
  let r : E → ℝ := fun e => (q e : ℝ)
  have hsat : ∀ t : ℝ,
      (B ∩ NativeWeightedBaseRankSaturation.lowerWeightSet M r t).ncard =
        (M.eRk (NativeWeightedBaseRankSaturation.lowerWeightSet M r t)).toNat := by
    intro t
    let X := NativeWeightedBaseRankSaturation.lowerWeightSet M r t
    have hXE : X ⊆ M.E := fun _ h => h.1
    have hI : M.Indep (B ∩ X) := hB.indep.inter_right X
    have hBasis : M.IsBasis (B ∩ X) X := by
      by_contra hnot
      obtain ⟨J, hJ⟩ := M.exists_isBasis X hXE
      obtain ⟨e, heJ, heI⟩ :=
        hI.exists_insert_of_not_isBasis inter_subset_right hnot hJ
      have heX : e ∈ X := hJ.subset heJ.1
      have heNotB : e ∉ B := fun heB => heJ.2 ⟨heB, heX⟩
      obtain ⟨b, hb, hex⟩ :=
        D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.exchange_base_over_independent_subset
          hB heNotB heI
      have hbe : r b ≤ r e := by
        dsimp [r]
        exact_mod_cast hlocal b hb.1 e ⟨heX.1, heNotB⟩ hex
      have hbX : b ∈ X := ⟨hB.subset_ground hb.1, hbe.trans heX.2⟩
      exact hb.2 ⟨hb.1, hbX⟩
    rw [ncard_def, hBasis.encard_eq_eRk]
  have hmin := ((NativeWeightedBaseRankSaturation.native_weighted_base_rank_saturation
    M r).2 B hB).mpr hsat
  intro C hC
  have h := hmin C hC
  dsimp [NativeWeightedBaseRankSaturation.baseWeight, r] at h
  unfold weightSum
  exact_mod_cast h

#print axioms exchange_local_is_global_minimum

/-- Tagged native exchanges; `true` tags the first matroid. -/
def ExchangeArc (M₁ M₂ : Matroid E) (B : Set E) :=
  {a : Bool × E × E // a.2.1 ∈ B ∧ a.2.2 ∈ M₁.E \ B ∧
    (if a.1 then M₁ else M₂).IsBase (insert a.2.2 (B \ {a.2.1}))}

/-- The first matroid is oriented inside-to-outside and the second in reverse. -/
def exchangeGraph (M₁ M₂ : Matroid E) (B : Set E) :
    Maths.EdgeGraph E (ExchangeArc M₁ M₂ B) where
  source a := if a.val.1 then a.val.2.1 else a.val.2.2
  target a := if a.val.1 then a.val.2.2 else a.val.2.1

/-- The asymmetric integral arc weight in the closed-walk obstruction. -/
def exchangeWeight (M₁ M₂ : Matroid E) (B : Set E) (w : E → ℤ)
    (a : ExchangeArc M₁ M₂ B) : ℤ :=
  if a.val.1 then 0 else w a.val.2.1 - w a.val.2.2

private noncomputable def point (S : Set E) (e : E) : ℝ :=
  if e ∈ S then 1 else 0

private noncomputable def linearTotal [Fintype E] (q : E → ℝ) : (E → ℝ) →L[ℝ] ℝ :=
  ∑ e, q e • ContinuousLinearMap.proj e

private lemma linearTotal_apply [Fintype E] (q x : E → ℝ) :
    linearTotal q x = ∑ e, q e * x e := by
  simp [linearTotal]

private lemma point_sum (S U : Set E) :
    (∑ e ∈ U.toFinite.toFinset, point S e) = ((S ∩ U).ncard : ℝ) := by
  classical
  rw [Set.ncard_eq_toFinset_card (S ∩ U)]
  simp only [point, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  ext e
  simp [and_comm]

private lemma point_feasible (M : Matroid E) {S : Set E} (hS : M.IsBase S) (U : Set E) :
    (∑ e ∈ U.toFinite.toFinset, point S e) ≤ ((M.eRk U).toNat : ℝ) := by
  rw [point_sum]
  have hi : M.Indep (S ∩ U) := hS.indep.inter_right U
  have hr : (S ∩ U).ncard ≤ (M.eRk U).toNat := by
    rw [ncard_def, ← hi.eRk_eq_encard]
    exact ENat.toNat_le_toNat (M.eRk_mono inter_subset_right)
      (M.isRkFinite_set U).eRk_lt_top.ne
  exact_mod_cast hr

private lemma point_total [Fintype E] (q : E → ℝ) (S : Set E) :
    linearTotal q (point S) = ∑ e ∈ S.toFinite.toFinset, q e := by
  classical
  rw [linearTotal_apply]
  simp only [point, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp

end D5.S3.Combinatorics.Matroids.IntegralWeightSplitting
