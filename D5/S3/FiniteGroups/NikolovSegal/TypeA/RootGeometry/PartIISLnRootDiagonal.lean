/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootDiagonal
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootGraph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NikolovSegal.SLnRootAction
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem reflect_simple_root (r : Fin (n-1)) :
    reflectRoot (simpleRoot r)=simpleRoot r.rev := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    simp only [reflectRoot,simpleRoot,Fin.val_rev]
    have hb:=r.isLt
    omega

/-- Arbitrary nonzero simple-root coefficients are realized by ONE genuine
GL diagonal action on SL, without a determinant-root premise. -/
theorem exists_diagonal_simple_coefficients (chi : PositiveIndex n → Fˣ) (eps : Bool) :
    ∃ a : Fin n → Fˣ, ∀ r : Fin (n-1),
      let s := if eps then reflectRoot (simpleRoot r) else simpleRoot r
      a s.val.1*(a s.val.2)⁻¹=chi (simpleRoot r) := by
  classical
  let lambda : Fin (n-1) → Fˣ := fun r => chi (simpleRoot (if eps then r.rev else r))
  let rho : ℕ → Fˣ := fun k => if hk : k<n-1 then (lambda ⟨k,hk⟩)⁻¹ else 1
  let a : Fin n → Fˣ := fun i => ∏ k ∈ Finset.range i.val, rho k
  have hratio : ∀ r : Fin (n-1), a (simpleRoot r).val.1*(a (simpleRoot r).val.2)⁻¹=lambda r := by
    intro r
    change (∏ k ∈ Finset.range r.val, rho k)*(∏ k ∈ Finset.range (r.val+1), rho k)⁻¹=lambda r
    rw [Finset.prod_range_succ]
    simp [rho,r.isLt,_root_.mul_inv_rev,mul_comm,mul_left_comm,mul_assoc]
  refine ⟨a,?_⟩
  intro r
  cases eps
  · simpa only [Bool.false_eq_true,ite_false,lambda] using hratio r
  · simpa only [ite_true,reflect_simple_root,lambda,Fin.rev_rev] using hratio r.rev
end NikolovSegal.SLnRootAction
