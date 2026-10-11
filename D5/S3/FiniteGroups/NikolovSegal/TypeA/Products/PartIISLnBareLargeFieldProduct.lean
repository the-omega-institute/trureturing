/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBareLargeFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBareLargeFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIPSLnLargeFieldProduct
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnBareFullGroupClassification
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnBareFullGroupClassification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! PartII Sections 2 and 6, actual type-A branch. The accepted native bare
full-group classification is consumed here with the actual all-rank product.
Both classifications are full-group equalities; no projective lift is used.
The resulting scalar products retain the original q/e and correction order.
Other families and the small-field branch remain outside this theorem. -/

namespace NikolovSegal.PartIISLnBareLargeFieldProduct
open Matrix
universe u

private theorem transport_inner {S : Type u} [Group S] {q N : ℕ}
    (beta delta : Fin N → MulAut S) (h : Fin N → S)
    (hd : ∀ i, MulAut.conj (h i)*beta i=delta i)
    (e : Fin N → ℕ) (hp : PartIIScalarProductInput q N delta e) :
    PartIIScalarProductInput q N beta e := by
  intro he
  obtain ⟨v,hv⟩ := hp he
  let y := fun i => v i*(beta i).symm ((h i)⁻¹)
  have hy : ∀ i, beta i*MulAut.conj (y i)⁻¹=delta i*MulAut.conj (v i)⁻¹ := by
    intro i
    rw [← hd i]
    apply MulEquiv.ext
    intro x
    simp only [y,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
      MulEquiv.apply_symm_apply,_root_.mul_inv_rev,inv_inv,mul_assoc]
  refine ⟨y,?_⟩
  intro target
  obtain ⟨c,hc⟩ := hv target
  refine ⟨c,?_⟩
  simpa only [hy] using hc

/-- Uniform chosen-length scalar PRODUCT for EVERY actual SLn automorphism,
all ranks k+4 and sufficiently large fields. No normal-form premise remains.
N,C precede every field/rank/tuple; ONE correction precedes ALL targets. -/
theorem actual_uniform_bare_SLn_scalar_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ beta : Fin N → MulAut (SpecialLinearGroup (Fin (k+4)) F),
      ∀ e : Fin N → ℕ, PartIIScalarProductInput q N beta e := by
  obtain ⟨N,C,hN,hprod⟩ := PartIISLnLargeFieldProduct.actual_uniform_SLn_DFG_scalar_product q hq
  refine ⟨N,max C 4,hN,?_⟩
  intro F _ _ _ hF k beta e
  have hC : C<Fintype.card F := lt_of_le_of_lt (le_max_left _ _) hF
  have h4 : 4<Fintype.card F := lt_of_le_of_lt (le_max_right _ _) hF
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  choose c a phi eps haction using fun i =>
    SLnFullGroup.sl_bare_full_group_diagonal_field_graph (ringChar F) (by omega) h4 (beta i)
  have hd : ∀ i, MulAut.conj (c i)*beta i=
      PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i) := by
    intro i
    exact MulEquiv.ext (haction i)
  exact transport_inner beta _ c hd e (hprod F hC k a phi eps e)

/-- Intrinsic bare PSLn scalar PRODUCT in the same uniform large-field
branch. Classification and correction live in PSLn; alpha is never lifted. -/
theorem actual_uniform_bare_PSLn_scalar_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ beta : Fin N → MulAut (ProjectiveSpecialLinearGroup (Fin (k+4)) F),
      ∀ e : Fin N → ℕ, PartIIScalarProductInput q N beta e := by
  obtain ⟨N,C,hN,hprod⟩ := PartIIPSLnLargeFieldProduct.actual_uniform_PSLn_DFG_scalar_product q hq
  refine ⟨N,max C 4,hN,?_⟩
  intro F _ _ _ hF k beta e
  have hC : C<Fintype.card F := lt_of_le_of_lt (le_max_left _ _) hF
  have h4 : 4<Fintype.card F := lt_of_le_of_lt (le_max_right _ _) hF
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  choose c a phi eps haction using fun i =>
    PSLnFullGroup.psl_bare_full_group_diagonal_field_graph (ringChar F) (by omega) h4 (beta i)
  have hd : ∀ i, MulAut.conj (c i)*beta i=
      PartIIPSLnLargeFieldProduct.projectiveAction
        (PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)) := by
    intro i
    apply MulEquiv.ext
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin (k+4)) F)) x
    exact haction i g
  exact transport_inner beta _ c hd e (hprod F hC k a phi eps e)
end NikolovSegal.PartIISLnBareLargeFieldProduct
