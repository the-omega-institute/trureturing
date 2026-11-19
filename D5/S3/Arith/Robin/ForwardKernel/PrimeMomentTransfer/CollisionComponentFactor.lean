/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionComponentFactor
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionComponentFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Free collision components factor from retained distinct-index moments. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.AssignmentMomentReindex

/-! Collision components with no retained block contribute scalar weight sums. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A B : Type*} [Fintype ι] [Fintype B] [DecidableEq B] [CommRing A] [Algebra ℝ A]

/-- Summing the free components leaves precisely the ordered distinct-index moment of
the retained component weights. The index type may be empty. -/
theorem component_assignment_factorization (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (S : Finset B) (w : B → ι → ℝ) :
    (∑ x : B → ι with Function.Injective (fun t : S => x t),
      (∏ t : B, w t (x t)) * ℓ (∏ t ∈ S, Y (x t))) =
      (∏ t ∈ Sᶜ, ∑ d, w t d) *
        distinctIndexMoment ℓ Y (fun i : Fin (Fintype.card S) =>
          w ((Fintype.equivFin S).symm i)) := by
  let e := Equiv.piEquivPiSubtypeProd (fun t : B => t ∈ S) (fun _ => ι)
  rw [Finset.sum_filter]
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have hpoint (x : S → ι) (z : {t : B // t ∉ S} → ι) :
      (if Function.Injective (fun t : S => e.symm (x, z) t) then
        (∏ t, w t (e.symm (x, z) t)) *
          ℓ (∏ t ∈ S, Y (e.symm (x, z) t)) else 0) =
      (∏ t : {t : B // t ∉ S}, w t (z t)) *
        (if Function.Injective x then (∏ t : S, w t (x t)) *
          ℓ (∏ t, Y (x t)) else 0) := by
    have hret : (fun t : S => e.symm (x, z) t) = x := by
      funext t
      simp [e, Equiv.piEquivPiSubtypeProd, t.property]
    rw [hret]
    by_cases hx : Function.Injective x
    · rw [if_pos hx, if_pos hx]
      have hw : (∏ t : B, w t (e.symm (x, z) t)) =
          (∏ t : S, w t (x t)) * (∏ t : {t : B // t ∉ S}, w t (z t)) := by
        rw [← Finset.prod_mul_prod_compl S]
        congr 1
        · rw [← Finset.prod_attach S]
          apply Finset.prod_congr rfl
          intro t ht
          simp [e, Equiv.piEquivPiSubtypeProd, t.property]
        · calc
            (∏ t ∈ Sᶜ, w t (e.symm (x, z) t)) =
                ∏ t : {t : B // t ∉ S}, w t (e.symm (x, z) t) :=
              Finset.prod_subtype Sᶜ (by simp) _
            _ = _ := by
              apply Finset.prod_congr rfl
              intro t ht
              simp [e, Equiv.piEquivPiSubtypeProd, t.property]
      have hy : (∏ t ∈ S, Y (e.symm (x, z) t)) = ∏ t : S, Y (x t) := by
        rw [← Finset.prod_attach S]
        apply Finset.prod_congr rfl
        intro t ht
        simp [e, Equiv.piEquivPiSubtypeProd, t.property]
      rw [hw, hy]
      ring
    · simp [hx]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext z
    rw [hpoint]
  simp_rw [← Finset.sum_mul]
  rw [← Fintype.prod_sum]
  have hfree : (∏ t : {t : B // t ∉ S}, ∑ d, w t d) =
      ∏ t ∈ Sᶜ, ∑ d, w t d := (Finset.prod_subtype (p := fun t : B => t ∉ S) Sᶜ (by simp)
        (fun t => ∑ d, w t d)).symm
  rw [hfree]
  rw [← Finset.mul_sum, ← Finset.sum_filter,
    retained_assignment_reindex ℓ Y S w]

/-- All positional weights in one collision component are multiplied together. -/
def collisionComponentWeight (τ : Setoid B) (w : B → ι → ℝ)
    (c : Quotient τ) (d : ι) : ℝ :=
  ∏ b : B with Quotient.mk τ b = c, w b d

omit [Fintype ι] [Fintype B] [DecidableEq B] in
private theorem quotient_retained_injective_iff (τ : Setoid B) (S : Finset B)
    (hS : Set.InjOn (Quotient.mk τ) S) (x : Quotient τ → ι) :
    Function.Injective (fun t : S.image (Quotient.mk τ) => x t) ↔
      Set.InjOn (fun b => x (Quotient.mk τ b)) S := by
  constructor
  · intro hx b hb c hc hbc
    apply hS hb hc
    have h := hx (a₁ := ⟨Quotient.mk τ b, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩)
      (a₂ := ⟨Quotient.mk τ c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩) hbc
    exact congrArg Subtype.val h
  · intro hx c d hcd
    obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp c.property
    obtain ⟨e, he, hed⟩ := Finset.mem_image.mp d.property
    apply Subtype.ext
    have hbe : b = e := hx hb he (by simpa [hbc, hed] using hcd)
    exact hbc.symm.trans (hbe ▸ hed)

/-- Constant assignments on collision components can be summed on the quotient. If
retained blocks occupy distinct components, each free component contributes its scalar
weight sum and the retained components give an ordered distinct-index moment. -/
theorem quotient_assignment_factorization (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (τ : Setoid B) (S : Finset B) (hS : Set.InjOn (Quotient.mk τ) S)
    (w : B → ι → ℝ) :
    (∑ x : B → ι with τ ≤ Setoid.ker x ∧ Set.InjOn x S,
      (∏ b, w b (x b)) * ℓ (∏ b ∈ S, Y (x b))) =
      (∏ c ∈ (S.image (Quotient.mk τ))ᶜ,
        ∑ d, collisionComponentWeight τ w c d) *
      distinctIndexMoment ℓ Y
        (fun i : Fin (Fintype.card (S.image (Quotient.mk τ))) =>
          collisionComponentWeight τ w
            ((Fintype.equivFin (S.image (Quotient.mk τ))).symm i)) := by
  apply Eq.trans ?_ (component_assignment_factorization ℓ Y (S.image (Quotient.mk τ))
    (collisionComponentWeight τ w))
  symm
  apply Finset.sum_bij (fun x _ b => x (Quotient.mk τ b))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, (quotient_retained_injective_iff τ S hS x).mp hx⟩
    intro b c hbc
    exact congrArg x (Quotient.sound hbc)
  · intro x hx y hy hxy
    funext c
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective c
    exact congrFun hxy b
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    let y : Quotient τ → ι := Quotient.lift x hx.1
    have hy : (fun b => y (Quotient.mk τ b)) = x := rfl
    refine ⟨y, ?_, hy⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (quotient_retained_injective_iff τ S hS y).mpr (by simpa only [hy] using hx.2)
  · intro x hx
    have hw : (∏ c : Quotient τ, collisionComponentWeight τ w c (x c)) =
        ∏ b : B, w b (x (Quotient.mk τ b)) := by
      unfold collisionComponentWeight
      calc
        _ = ∏ c : Quotient τ, ∏ b : B with Quotient.mk τ b = c,
            w b (x (Quotient.mk τ b)) := by
          apply Finset.prod_congr rfl
          intro c hc
          apply Finset.prod_congr rfl
          intro b hb
          rw [(Finset.mem_filter.mp hb).2]
        _ = _ := Finset.prod_fiberwise Finset.univ (Quotient.mk τ) _
    have hy : (∏ c ∈ S.image (Quotient.mk τ), Y (x c)) =
        ∏ b ∈ S, Y (x (Quotient.mk τ b)) := Finset.prod_image hS
    rw [hw, hy]

/-- Two retained blocks in one component force a repeated retained value, so their
constrained distinct-index sum is zero. -/
theorem quotient_assignment_zero_of_retained_collision (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (τ : Setoid B) (S : Finset B) (w : B → ι → ℝ)
    (hS : ¬ Set.InjOn (Quotient.mk τ) S) :
    (∑ x : B → ι with τ ≤ Setoid.ker x ∧ Set.InjOn x S,
      (∏ b, w b (x b)) * ℓ (∏ b ∈ S, Y (x b))) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨hconst, hinj⟩ := (Finset.mem_filter.mp hx).2
  exact False.elim (hS (fun b hb c hc hbc => hinj hb hc
    (hconst (Quotient.exact hbc))))

/-- A component contribution is bounded without putting absolute values inside the
retained moment. Any upper bound q for the number of free components is admissible. -/
theorem quotient_assignment_abs_le (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (τ : Setoid B) (S : Finset B) (w : B → ι → ℝ)
    (C H s : ℝ) (q r : ℕ) (hC : 1 ≤ C) (hH : 1 ≤ H) (hs : 0 ≤ s)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hw : ∀ b d, |w b d| ≤ 1)
    (hq : (S.image (Quotient.mk τ))ᶜ.card ≤ q)
    (hR : Set.InjOn (Quotient.mk τ) S →
      |distinctIndexMoment ℓ Y
        (fun i : Fin (Fintype.card (S.image (Quotient.mk τ))) =>
          collisionComponentWeight τ w
            ((Fintype.equivFin (S.image (Quotient.mk τ))).symm i))| ≤ C * s ^ r) :
    |∑ x : B → ι with τ ≤ Setoid.ker x ∧ Set.InjOn x S,
      (∏ b, w b (x b)) * ℓ (∏ b ∈ S, Y (x b))| ≤
        C ^ (q + 1) * H ^ q * s ^ r := by
  by_cases hS : Set.InjOn (Quotient.mk τ) S
  · rw [quotient_assignment_factorization ℓ Y τ S hS w, abs_mul]
    have hCH : 1 ≤ C * H := by nlinarith
    have hsum (c : Quotient τ) : |∑ d, collisionComponentWeight τ w c d| ≤ C * H := by
      calc
        _ ≤ ∑ d, |collisionComponentWeight τ w c d| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [collisionComponentWeight, Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun b hb => hw b d)
        _ = (Fintype.card ι : ℝ) := by simp
        _ ≤ C * H := hD
    have hprod : |∏ c ∈ (S.image (Quotient.mk τ))ᶜ,
        ∑ d, collisionComponentWeight τ w c d| ≤ (C * H) ^ q := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _c ∈ (S.image (Quotient.mk τ))ᶜ, (C * H) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun c hc => hsum c)
        _ = (C * H) ^ (S.image (Quotient.mk τ))ᶜ.card := by simp
        _ ≤ (C * H) ^ q := pow_le_pow_right₀ hCH hq
    calc
      _ ≤ (C * H) ^ q * (C * s ^ r) :=
        mul_le_mul hprod (hR hS) (abs_nonneg _) (pow_nonneg (by linarith) _)
      _ = _ := by rw [mul_pow, pow_succ]; ring
  · rw [quotient_assignment_zero_of_retained_collision ℓ Y τ S w hS, abs_zero]
    positivity

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
