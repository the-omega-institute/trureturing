/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint label estimates control merged collision component moments. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CollisionComponentFactor

/-! Fibers of quotient maps preserve the nonempty disjoint label condition in low-order
distinct-index moment estimates. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]

/-- A size estimate for all low-order moments formed from disjoint nonempty label sets. -/
def DisjointLabelMomentBound {k : ℕ} (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (f : Fin k → ι → ℝ) (C s : ℝ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → r < k → ∀ labels : Fin r → Finset (Fin k),
    (∀ j, (labels j).Nonempty) →
    (∀ i j, i ≠ j → Disjoint (labels i) (labels j)) →
    |distinctIndexMoment ℓ Y (fun j d => ∏ i ∈ labels j, f i d)| ≤ C * s ^ r

private theorem fiber_distinctMoment_bound {k r : ℕ} {B : Type*} [DecidableEq B]
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ) (C s : ℝ)
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0) (hC : 1 ≤ C) (hs : 0 ≤ s)
    (hR : DisjointLabelMomentBound ℓ Y f C s)
    (p : Fin k → B) (hp : Function.Surjective p) (e : Fin r → B)
    (he : Function.Injective e) (hrk : r < k) :
    |distinctIndexMoment ℓ Y (fun j d => ∏ i : Fin k with p i = e j, f i d)| ≤
      C * s ^ r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst r
    simpa [distinctIndexMoment, Function.Injective, hunit] using hC
  by_cases hr1 : r = 1
  · subst r
    have hz : distinctIndexMoment ℓ Y
        (fun j : Fin 1 => fun d => ∏ i : Fin k with p i = e j, f i d) = 0 := by
      unfold distinctIndexMoment
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Fin.prod_univ_one, hcenter, mul_zero]
    rw [hz, abs_zero]
    exact mul_nonneg (by linarith) (pow_nonneg hs _)
  have hr2 : 2 ≤ r := by omega
  apply hR r hr2 hrk (fun j => Finset.univ.filter fun i => p i = e j)
  · intro j
    obtain ⟨i, hi⟩ := hp (e j)
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    apply hij
    apply he
    exact (Finset.mem_filter.mp hai).2.symm.trans (Finset.mem_filter.mp haj).2

private theorem nested_collisionComponentWeight {k : ℕ}
    (σ : Setoid (Fin k)) (τ : Setoid (Quotient σ)) (f : Fin k → ι → ℝ)
    (c : Quotient τ) (d : ι) :
    collisionComponentWeight τ (collisionComponentWeight σ f) c d =
      ∏ i : Fin k with Quotient.mk τ (Quotient.mk σ i) = c, f i d := by
  simpa only [collisionComponentWeight, Finset.mem_filter, Finset.mem_univ,
    true_and] using
    (Finset.prod_fiberwise_eq_prod_filter (Finset.univ : Finset (Fin k))
      (Finset.univ.filter fun B : Quotient σ => Quotient.mk τ B = c)
      (Quotient.mk σ) (fun i => f i d))

/-- A collision contribution inherits the original disjoint-label moment estimates.
Its retained component weights are products over nonempty disjoint original label fibers. -/
theorem quotient_merged_assignment_abs_le {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (τ : Setoid (Quotient σ)) (S : Finset (Quotient σ))
    (C H s : ℝ) (q : ℕ) (hC : 1 ≤ C) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C s) (hrk : S.card < k)
    (hq : (S.image (Quotient.mk τ))ᶜ.card ≤ q) :
    |∑ x : Quotient σ → ι with τ ≤ Setoid.ker x ∧ Set.InjOn x S,
      (∏ B, collisionComponentWeight σ f B (x B)) * ℓ (∏ B ∈ S, Y (x B))| ≤
        C ^ (q + 1) * H ^ q * s ^ S.card := by
  apply quotient_assignment_abs_le ℓ Y τ S (collisionComponentWeight σ f)
    C H s q S.card hC hH hs hD
  · intro B d
    rw [collisionComponentWeight, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i hi => hf i d)
  · exact hq
  · intro hS
    let T := S.image (Quotient.mk τ)
    have hT : Fintype.card T = S.card := by
      rw [Fintype.card_coe]
      exact Finset.card_image_iff.mpr hS
    have hp : Function.Surjective (fun i : Fin k => Quotient.mk τ (Quotient.mk σ i)) := by
      intro c
      exact ⟨c.out.out, by simp only [Quotient.out_eq]⟩
    have he : Function.Injective
        (fun j : Fin (Fintype.card T) => (((Fintype.equivFin T).symm j : T) : Quotient τ)) := by
      intro i j hij
      exact (Fintype.equivFin T).symm.injective (Subtype.ext hij)
    have hb := fiber_distinctMoment_bound ℓ Y f C s hunit hcenter hC hs hR
      _ hp _ he (by simpa only [hT] using hrk)
    have hweights :
        (fun j : Fin (Fintype.card T) => collisionComponentWeight τ (collisionComponentWeight σ f)
          ((Fintype.equivFin T).symm j)) =
        (fun j d => ∏ i : Fin k with Quotient.mk τ (Quotient.mk σ i) =
          ((Fintype.equivFin T).symm j : T), f i d) := by
      funext j d
      exact nested_collisionComponentWeight σ τ f _ d
    rw [← hweights] at hb
    simpa only [hT] using hb

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
