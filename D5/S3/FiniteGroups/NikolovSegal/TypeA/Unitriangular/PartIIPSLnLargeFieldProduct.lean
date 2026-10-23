/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPSLnLargeFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPSLnLargeFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIISLnLargeFieldProduct
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
/-! Part II p255: actual central-quotient consumption, for prescribed
DΦΓ actions. No lift/classification of arbitrary PSL automorphisms is assumed. -/
namespace NikolovSegal.PartIIPSLnLargeFieldProduct
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}
private abbrev pi : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
/-- Actual induced automorphism of the central quotient; characteristic
invariance of the center is native group theory, not a lifting premise. -/
def projectiveAction (beta : MulAut (SpecialLinearGroup (Fin n) F)) :
    MulAut (ProjectiveSpecialLinearGroup (Fin n) F) :=
  QuotientGroup.congr _ _ beta (Subgroup.characteristic_iff_map_eq.mp inferInstance beta)
private theorem action_pi (beta : MulAut (SpecialLinearGroup (Fin n) F))
    (g : SpecialLinearGroup (Fin n) F) : projectiveAction beta (pi g)=pi (beta g) := rfl
private theorem corrected_pi (beta : MulAut (SpecialLinearGroup (Fin n) F))
    (y g : SpecialLinearGroup (Fin n) F) :
    (projectiveAction beta*MulAut.conj ((pi y)⁻¹)) (pi g)=
      pi ((beta*MulAut.conj (y⁻¹)) g) := by
  simp only [MulAut.mul_apply,MulAut.conj_apply,← map_mul,← map_inv,action_pi]
private theorem corrected_power_pi (beta : MulAut (SpecialLinearGroup (Fin n) F))
    (y : SpecialLinearGroup (Fin n) F) (d : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    ((projectiveAction beta*MulAut.conj ((pi y)⁻¹))^d) (pi g)=
      pi (((beta*MulAut.conj (y⁻¹))^d) g) := by
  induction d generalizing g with
  | zero => rfl
  | succ d ih =>
    calc
      _ = (projectiveAction beta*MulAut.conj ((pi y)⁻¹))
        (((projectiveAction beta*MulAut.conj ((pi y)⁻¹))^d) (pi g)) := by rw [pow_succ']; rfl
      _ = (projectiveAction beta*MulAut.conj ((pi y)⁻¹))
        (pi (((beta*MulAut.conj (y⁻¹))^d) g)) := congrArg _ (ih g)
      _ = pi ((beta*MulAut.conj (y⁻¹)) (((beta*MulAut.conj (y⁻¹))^d) g)) := corrected_pi beta y _
      _ = _ := by rw [pow_succ']; rfl
/-- Genuine full actual PSLn scalar PRODUCT for the induced prescribed
DΦΓ family, all ranks k+4 and sufficiently large fields. Uniform N,C are
chosen BEFORE all fields/ranks/tuples, and the same quotient correction
precedes ALL full quotient targets. This does not classify bare PSL autos. -/
theorem actual_uniform_PSLn_DFG_scalar_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ (a : Fin N → Fin (k+4) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (e : Fin N → ℕ),
      PartIIScalarProductInput q N
        (fun i => projectiveAction (PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))) e := by
  obtain ⟨N,C,hN,hSL⟩ := PartIISLnLargeFieldProduct.actual_uniform_SLn_DFG_scalar_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF k a phi eps e he
  let beta := fun i => PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)
  obtain ⟨y,hy⟩ := hSL F hF k a phi eps e he
  refine ⟨fun i => pi (y i),?_⟩
  intro target
  obtain ⟨t,ht⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin (k+4)) F)) target
  obtain ⟨c,hc⟩ := hy t
  refine ⟨fun i => pi (c i),?_⟩
  have hvalues : (fun i => (pi (c i))⁻¹*
      ((projectiveAction (beta i)*MulAut.conj ((pi (y i))⁻¹))^(q/e i)) (pi (c i)))=
      fun i => pi ((c i)⁻¹*((beta i*MulAut.conj ((y i)⁻¹))^(q/e i)) (c i)) := by
    funext i
    rw [corrected_power_pi,map_mul]
    simp only [map_inv]
  change NikolovSegal.orderedProduct (fun i => (pi (c i))⁻¹*
    ((projectiveAction (beta i)*MulAut.conj ((pi (y i))⁻¹))^(q/e i)) (pi (c i)))=target
  rw [hvalues]
  have hp := congrArg (fun g => pi g) hc
  have he : NikolovSegal.orderedProduct (fun i => pi ((c i)⁻¹*
      ((beta i*MulAut.conj ((y i)⁻¹))^(q/e i)) (c i)))=pi t := by
    simpa only [NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,beta] using hp
  exact he.trans ht
end NikolovSegal.PartIIPSLnLargeFieldProduct
