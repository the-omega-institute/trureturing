/- GID: D5/S3/Entropy/Submodularity/MarkovDataProcessing
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/MarkovDataProcessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove mutual-information data processing for finite Markov chains. -/

import D5.S3.Entropy.Submodularity.ConditionalMutualInformation

/-!
# Markov data processing

This module pivots a right-nested three-variable law and derives the mutual-information
data-processing inequality from conditional mutual information. The four local projection
identities restate private facts from `StrongSubadditivity`, whose public interface does not expose
them. The private entropy reindexing helper composes a law with an equivalence and changes no
support. By contrast, the frozen `shannonEntropy_extend_injective` relabeling theorem extends a law
by zero along an injection into a possibly larger type; the two operations are deliberately kept
distinct here.

A repository and pinned-Mathlib search found no finite-real Markov mutual-information DPI
interface. The closest Mathlib data-processing results concern Bayes risk, so the proof composes
the repository's finite entropy and conditional-product interfaces.
-/

namespace D5.S3.Entropy.Submodularity.MarkovDataProcessing

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation

private theorem entropy_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → ℝ) :
    shannonEntropy (fun a => p (e a)) = shannonEntropy p :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Pivot a right-nested three-variable law so that `Y` is the conditioning coordinate. -/
noncomputable def yFirstLaw {ι κ μ : Type*} (p : ι × (κ × μ) → ℝ)
    (q : κ × (ι × μ)) : ℝ :=
  p (q.2.1, (q.1, q.2.2))

/-- Pivot a right-nested three-variable law so that `Z` is the conditioning coordinate. -/
noncomputable def zFirstLaw {ι κ μ : Type*} (p : ι × (κ × μ) → ℝ)
    (q : μ × (ι × κ)) : ℝ :=
  p (q.2.1, (q.2.2, q.1))

private def yPivot (ι κ μ : Type*) : κ × (ι × μ) ≃ ι × (κ × μ) where
  toFun q := (q.2.1, (q.1, q.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private def zPivot (ι κ μ : Type*) : μ × (ι × κ) ≃ ι × (κ × μ) where
  toFun q := (q.2.1, (q.2.2, q.1))
  invFun q := (q.2.2, (q.1, q.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

private theorem entropy_yFirstLaw (p : ι × (κ × μ) → ℝ) :
    shannonEntropy (yFirstLaw p) = shannonEntropy p :=
  entropy_comp_equiv (yPivot ι κ μ) p

private theorem entropy_zFirstLaw (p : ι × (κ × μ) → ℝ) :
    shannonEntropy (zFirstLaw p) = shannonEntropy p :=
  entropy_comp_equiv (zPivot ι κ μ) p

private theorem entropy_yz_comm (p : ι × (κ × μ) → ℝ) :
    shannonEntropy (xzProjection (zFirstLaw p)) =
      shannonEntropy (xzProjection (yFirstLaw p)) :=
  entropy_comp_equiv (Equiv.prodComm μ κ) (xzProjection (yFirstLaw p))

private theorem entropy_xy_yFirstLaw (p : ι × (κ × μ) → ℝ) :
    shannonEntropy (xyProjection (yFirstLaw p)) = shannonEntropy (xyProjection p) :=
  entropy_comp_equiv (Equiv.prodComm κ ι) (xyProjection p)

private theorem entropy_xy_zFirstLaw (p : ι × (κ × μ) → ℝ) :
    shannonEntropy (xyProjection (zFirstLaw p)) = shannonEntropy (xzProjection p) :=
  entropy_comp_equiv (Equiv.prodComm μ ι) (xzProjection p)

omit [Fintype κ] in
private theorem marg_yFirstLaw (p : ι × (κ × μ) → ℝ) :
    marginal (yFirstLaw p) = marginal (fun r : κ × ι => xyProjection p (r.2, r.1)) := by
  funext y
  simp only [marginal, yFirstLaw, xyProjection, Fintype.sum_prod_type]

omit [Fintype μ] in
private theorem marg_zFirstLaw (p : ι × (κ × μ) → ℝ) :
    marginal (zFirstLaw p) = marginal (fun r : μ × ι => xzProjection p (r.2, r.1)) := by
  funext z
  simp only [marginal, zFirstLaw, xzProjection, Fintype.sum_prod_type]

omit [Fintype ι] in
private theorem marg_xy (p : ι × (κ × μ) → ℝ) :
    marginal (xyProjection p) = marginal p := by
  funext i
  simp only [marginal, xyProjection, Fintype.sum_prod_type]

omit [Fintype ι] in
private theorem marg_xz (p : ι × (κ × μ) → ℝ) :
    marginal (xzProjection p) = marginal p := by
  funext i
  simp only [marginal, xzProjection, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

private theorem yFirstLaw_is_law (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    (∀ q, 0 ≤ yFirstLaw p q) ∧ ∑ q, yFirstLaw p q = 1 :=
  ⟨fun q => hp.1 _, by
    rw [← hp.2]
    exact Fintype.sum_equiv (yPivot ι κ μ) _ _ (fun _ => rfl)⟩

omit [Fintype κ] in
private theorem cond_marg_fst (p : ι × (κ × μ) → ℝ) (y : κ) :
    marginal (conditional (yFirstLaw p) y) =
      fun x : ι => xyProjection p (x, y) / marginal (yFirstLaw p) y := by
  funext x
  simp only [marginal, conditional, yFirstLaw, xyProjection, ← Finset.sum_div]

omit [Fintype κ] in
private theorem cond_marg_snd (p : ι × (κ × μ) → ℝ) (y : κ) :
    marginal (fun r : μ × ι => conditional (yFirstLaw p) y (r.2, r.1)) =
      fun z : μ => xzProjection (yFirstLaw p) (y, z) / marginal (yFirstLaw p) y := by
  funext z
  simp only [marginal, conditional, yFirstLaw, xzProjection, ← Finset.sum_div]

/-- Conditional mutual information vanishes exactly on conditionally factorizing slices. -/
theorem conditional_mutual_information_eq_zero_iff_conditional_product
    (p : ι × (κ × μ) → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    conditionalMutualInformation p = 0 ↔
      ∀ i, marginal p i ≠ 0 →
        conditional p i = fun q : κ × μ =>
          marginal (conditional p i) q.1 *
            marginal (fun r : μ × κ => conditional p i (r.2, r.1)) q.2 := by
  rw [← entropy_submodular_eq_iff_conditional_product p hp,
    conditional_mutual_information_eq_entropy_defect p hp.1]
  constructor <;> intro h <;> linarith

/-- The mutual-information gap of a three-variable law is the gap between the conditional
mutual informations obtained by pivoting on `Z` and on `Y`. -/
theorem mutual_information_gap_eq_conditional_gap (p : ι × (κ × μ) → ℝ)
    (hp : ∀ x, 0 ≤ p x) :
    mutualInformation (xyProjection p) - mutualInformation (xzProjection p) =
      conditionalMutualInformation (zFirstLaw p) -
        conditionalMutualInformation (yFirstLaw p) := by
  classical
  have hxy_nonneg : ∀ q, 0 ≤ xyProjection p q := fun q =>
    Finset.sum_nonneg fun z _ => hp (q.1, (q.2, z))
  have hxz_nonneg : ∀ q, 0 ≤ xzProjection p q := fun q =>
    Finset.sum_nonneg fun y _ => hp (q.1, (y, q.2))
  rw [mutual_information_eq_entropy_sub (xyProjection p) hxy_nonneg,
    mutual_information_eq_entropy_sub (xzProjection p) hxz_nonneg,
    conditional_mutual_information_eq_entropy_defect (zFirstLaw p) (fun q => hp _),
    conditional_mutual_information_eq_entropy_defect (yFirstLaw p) (fun q => hp _),
    entropy_yz_comm, entropy_xy_yFirstLaw, entropy_xy_zFirstLaw,
    entropy_yFirstLaw, entropy_zFirstLaw, marg_xy, marg_xz,
    ← marg_yFirstLaw, ← marg_zFirstLaw]
  ring

/-- A Markov chain `X → Y → Z` has vanishing conditional mutual information given `Y`. -/
theorem conditional_mutual_information_eq_zero_of_markov (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hmarkov : ∀ x y z, p (x, (y, z)) * marginal (yFirstLaw p) y =
      xyProjection p (x, y) * xzProjection (yFirstLaw p) (y, z)) :
    conditionalMutualInformation (yFirstLaw p) = 0 := by
  classical
  refine (conditional_mutual_information_eq_zero_iff_conditional_product
    (yFirstLaw p) (yFirstLaw_is_law p hp)).2 ?_
  intro y hy
  rw [cond_marg_fst p y, cond_marg_snd p y]
  funext q
  show p (q.1, (y, q.2)) / marginal (yFirstLaw p) y = _
  rw [div_mul_div_comm, div_eq_div_iff hy (mul_ne_zero hy hy)]
  linear_combination marginal (yFirstLaw p) y * hmarkov q.1 y q.2

/-- **Data-processing inequality.** Along a Markov chain `X → Y → Z`, the information the
output retains about the input never exceeds the information carried by the intermediate. -/
theorem mutual_information_le_of_markov (p : ι × (κ × μ) → ℝ)
    (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (hmarkov : ∀ x y z, p (x, (y, z)) * marginal (yFirstLaw p) y =
      xyProjection p (x, y) * xzProjection (yFirstLaw p) (y, z)) :
    mutualInformation (xzProjection p) ≤ mutualInformation (xyProjection p) := by
  have hgap := mutual_information_gap_eq_conditional_gap p hp.1
  rw [conditional_mutual_information_eq_zero_of_markov p hp hmarkov] at hgap
  have hnonneg := conditional_mutual_information_nonneg (zFirstLaw p)
    ⟨fun q => hp.1 _, by
      rw [← hp.2]
      exact Fintype.sum_equiv (zPivot ι κ μ) _ _ (fun _ => rfl)⟩
  linarith

omit [Fintype κ] in
/-- Every row-normalized channel-generated law satisfies the Markov-chain hypothesis. -/
theorem markov_of_channel (pXY : ι × κ → ℝ) (W : κ → μ → ℝ)
    (hW : ∀ y, ∑ z, W y z = 1) :
    ∀ x y z,
      (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2) (x, (y, z)) *
          marginal
            (yFirstLaw
              (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2)) y =
        xyProjection
            (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2) (x, y) *
          xzProjection
            (yFirstLaw
              (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2)) (y, z) := by
  classical
  intro x y z
  have hxy :
      xyProjection
          (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2) (x, y) =
        pXY (x, y) := by
    simp only [xyProjection, ← Finset.mul_sum, hW y, mul_one]
  have hmarg :
      marginal
          (yFirstLaw
            (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2)) y =
        ∑ x', pXY (x', y) := by
    simp only [marginal, yFirstLaw, Fintype.sum_prod_type, ← Finset.mul_sum, hW y,
      mul_one]
  have hxz :
      xzProjection
          (yFirstLaw
            (fun q : ι × (κ × μ) => pXY (q.1, q.2.1) * W q.2.1 q.2.2)) (y, z) =
        (∑ x', pXY (x', y)) * W y z := by
    simp only [xzProjection, yFirstLaw, Finset.sum_mul]
  rw [hxy, hmarg, hxz]
  ring

end D5.S3.Entropy.Submodularity.MarkovDataProcessing
