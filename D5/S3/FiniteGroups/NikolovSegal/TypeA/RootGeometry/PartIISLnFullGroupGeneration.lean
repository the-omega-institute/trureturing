/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnFullGroupGeneration
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnFullGroupGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnOppositeRelations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnFullGroup
open Matrix NikolovSegal.SLnRootAction
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- The native SL2 six-transvection diagonal identity at arbitrary actual indices. -/
theorem diag2n_transvection_decompose (i j : Fin n) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha =
      SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
      SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hij (-1) *
      SpecialLinearGroup.transvection hij.symm 1 * SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  change Matrix.diagonal (fun k : Fin n => if k=i then a else if k=j then a⁻¹ else 1) =
    (1+Matrix.single i j a)*(1+Matrix.single j i (-a⁻¹))*(1+Matrix.single i j a)*
      (1+Matrix.single i j (-1))*(1+Matrix.single j i 1)*(1+Matrix.single i j (-1))
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,Matrix.one_mul,
    Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  ext r c
  by_cases hri : r=i <;> by_cases hrj : r=j <;> by_cases hci : c=i <;> by_cases hcj : c=j
  all_goals simp_all [eq_comm,Matrix.add_apply,Matrix.single_apply,Matrix.diagonal_apply,Matrix.one_apply,
    mul_inv_cancel₀ ha,inv_mul_cancel₀ ha]
  all_goals ring

/-- Native actual SLn diagonal/transvection induction gives homomorphism
extensionality from all actual elementary transvections. -/
theorem hom_ext_transvections {K : Type*} [Group K] (hn : 1 < n) (f g : G →* K)
    (ht : ∀ i j (hij : i ≠ j) t, f (SpecialLinearGroup.transvection hij t)=
      g (SpecialLinearGroup.transvection hij t)) : ∀ x, f x=g x := by
  letI : Nontrivial (Fin n) := ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,by
    intro h; have he := congrArg Fin.val h; simp at he⟩⟩
  intro x
  apply SpecialLinearGroup.diagonal_transvection_induction' (fun x => f x=g x) x
  · intro i j hij a ha
    rw [diag2n_transvection_decompose i j hij a ha]
    simp only [map_mul,ht]
  · exact ht
  · intro x y hx hy; simp only [map_mul,hx,hy]

theorem transvection_commutator_distinct {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (t s : F) :
    SpecialLinearGroup.transvection hij t * SpecialLinearGroup.transvection hjk s *
      (SpecialLinearGroup.transvection hij t)⁻¹ * (SpecialLinearGroup.transvection hjk s)⁻¹ =
      SpecialLinearGroup.transvection hik (t*s) := by
  rw [transvection_conjugate_chain hij hjk hik t s,
    transvections_commute hjk hik hik.symm hjk.symm s (t*s)]
  simp [mul_assoc]

/-- Genuine negative A2 commutators generate all opposite roots from the
opposite simple roots. This applies equally to SL and intrinsic quotient homs. -/
theorem hom_ext_negative_simple {K : Type*} [Group K] (f g : G →* K)
    (hs : ∀ r : PositiveIndex n, r.val.2.val=r.val.1.val+1 →
      ∀ t, f (negativeRoot r t)=g (negativeRoot r t)) :
    ∀ r t, f (negativeRoot r t)=g (negativeRoot r t) := by
  have hmain : ∀ m : ℕ, ∀ r : PositiveIndex n, r.val.2.val-r.val.1.val=m →
      ∀ t, f (negativeRoot r t)=g (negativeRoot r t) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r hm t
      by_cases hr : r.val.2.val=r.val.1.val+1
      · exact hs r hr t
      have hij := r.property
      let k : Fin n := ⟨r.val.1.val+1,by have hj:=r.val.2.isLt; change r.val.1.val<r.val.2.val at hij; omega⟩
      have hik : r.val.1 < k := by change r.val.1.val < r.val.1.val+1; omega
      have hkj : k < r.val.2 := by change r.val.1.val+1<r.val.2.val; change r.val.1.val<r.val.2.val at hij; omega
      let a : PositiveIndex n := ⟨(k,r.val.2),hkj⟩
      let b : PositiveIndex n := ⟨(r.val.1,k),hik⟩
      have ha : f (negativeRoot a t)=g (negativeRoot a t) := ih
        (a.val.2.val-a.val.1.val) (by dsimp [a,k]; change r.val.1.val<r.val.2.val at hij; omega) a rfl t
      have hb : f (negativeRoot b (1:F))=g (negativeRoot b (1:F)) := ih
        (b.val.2.val-b.val.1.val) (by dsimp [b,k]; change r.val.1.val<r.val.2.val at hij; omega) b rfl 1
      have he : negativeRoot a t * negativeRoot b 1 * (negativeRoot a t)⁻¹ *
          (negativeRoot b 1)⁻¹=negativeRoot r t := by
        simpa only [negativeRoot,mul_one] using transvection_commutator_distinct
          (ne_of_lt hkj).symm (ne_of_lt hik).symm (ne_of_lt hij).symm t (1:F)
      rw [← he]
      simp only [map_mul,map_inv,ha,hb]
  intro r t
  exact hmain _ r rfl t

/-- Full actual-group rigidity from positive-root and opposite-simple-root
agreement; generation is native matrix induction, not a width premise. -/
theorem hom_ext_positive_negative_simple {K : Type*} [Group K]
    (hn : 1 < n) (f g : G →* K)
    (hp : ∀ r t, f (root r t)=g (root r t))
    (hs : ∀ r : PositiveIndex n, r.val.2.val=r.val.1.val+1 →
      ∀ t, f (negativeRoot r t)=g (negativeRoot r t)) : ∀ x, f x=g x := by
  apply hom_ext_transvections hn f g
  intro i j hij t
  rcases lt_or_gt_of_ne hij with hij|hji
  · exact hp ⟨(i,j),hij⟩ t
  · exact hom_ext_negative_simple f g hs ⟨(j,i),hji⟩ t
end NikolovSegal.SLnFullGroup
