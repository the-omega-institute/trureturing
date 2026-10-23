/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnLargeFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnLargeFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnipotentDuality
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnipotentWidth
import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoverage
import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoordinates
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
/-! Full untwisted SL(k+4) PRODUCT, using the accepted actual ULUL
width and the p255 central-Levi/radical reconstruction. -/
namespace NikolovSegal.PartIISLnLargeFieldProduct
open Matrix PartIIUnitriangularLayers PartIIUnipotentDuality
universe u
variable {A B : ℕ}
private abbrev Total (A B : ℕ) := A+(B+(A+B))
private def join4 {T : Type*} (x0 x2 : Fin A → T) (x1 x3 : Fin B → T) : Fin (Total A B) → T :=
  Fin.append x0 (Fin.append x1 (Fin.append x2 x3))
private def j0 (i : Fin A) : Fin (Total A B) := i.castAdd _
private def j1 (i : Fin B) : Fin (Total A B) := (i.castAdd _).natAdd A
private def j2 (i : Fin A) : Fin (Total A B) := ((i.castAdd B).natAdd B).natAdd A
private def j3 (i : Fin B) : Fin (Total A B) := ((i.natAdd A).natAdd B).natAdd A
private theorem product_join4 {G : Type*} [Group G]
    (v0 v2 : Fin A → G) (v1 v3 : Fin B → G) :
    NikolovSegal.orderedProduct (join4 v0 v2 v1 v3)=
      NikolovSegal.orderedProduct v0*NikolovSegal.orderedProduct v1*
      NikolovSegal.orderedProduct v2*NikolovSegal.orderedProduct v3 := by
  simp only [join4,NikolovSegal.orderedProduct,List.ofFn_fin_append,List.prod_append]
  group
/-- Genuine uniform-in-rank full-group product for every prescribed DΦΓ
and original positive divisor tuple, over fields beyond the uniform cutoff.
N,C precede every field/rank/tuple. ONE inner tuple precedes ALL SL targets.
No scalar/twisted coverage assumption is used. Bare classification, small
fields, other simple families and the original all-simple supplier remain. -/
theorem actual_uniform_inner_SLn_DFG_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ (a : Fin N → Fin (k+4) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (d : Fin N → ℕ), (∀ i, 0<d i ∧ d i ∣ q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (k+4)) F,
        ∀ b : SpecialLinearGroup (Fin (k+4)) F,
          ∃ x : Fin N → SpecialLinearGroup (Fin (k+4)) F,
            NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
              ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=b := by
  obtain ⟨A,CU,hA,hU⟩ := PartIIAmbientUnipotentProduct.actual_uniform_inner_ambient_U_product q hq
  obtain ⟨B,CL,hB,hL⟩ := actual_uniform_inner_ambient_L_product q hq
  refine ⟨Total A B,max CU CL,by dsimp only [Total]; omega,?_⟩
  intro F _ _ _ hF k a phi eps d hd
  have hFU : CU<Fintype.card F := lt_of_le_of_lt (le_max_left _ _) hF
  have hFL : CL<Fintype.card F := lt_of_le_of_lt (le_max_right _ _) hF
  obtain ⟨h0,hcover0⟩ := hU F hFU k (fun i => a (j0 i)) (fun i => phi (j0 i))
    (fun i => eps (j0 i)) (fun i => d (j0 i)) (fun i => hd _)
  obtain ⟨h1,hcover1⟩ := hL F hFL k (fun i => a (j1 i)) (fun i => phi (j1 i))
    (fun i => eps (j1 i)) (fun i => d (j1 i)) (fun i => hd _)
  obtain ⟨h2,hcover2⟩ := hU F hFU k (fun i => a (j2 i)) (fun i => phi (j2 i))
    (fun i => eps (j2 i)) (fun i => d (j2 i)) (fun i => hd _)
  obtain ⟨h3,hcover3⟩ := hL F hFL k (fun i => a (j3 i)) (fun i => phi (j3 i))
    (fun i => eps (j3 i)) (fun i => d (j3 i)) (fun i => hd _)
  let h := join4 h0 h2 h1 h3
  refine ⟨h,?_⟩
  intro b
  obtain ⟨b0,b1,b2,b3,hb0,hb1,hb2,hb3,hprod⟩ := SLnUnipotentWidth.four_factor (k+4) b
  obtain ⟨x0,hx0,hp0⟩ := hcover0 b0 ((actual_unitriangular_upper_iff b0).mpr hb0)
  obtain ⟨x1,hp1⟩ := hcover1 b1 hb1
  obtain ⟨x2,hx2,hp2⟩ := hcover2 b2 ((actual_unitriangular_upper_iff b2).mpr hb2)
  obtain ⟨x3,hp3⟩ := hcover3 b3 hb3
  let x := join4 x0 x2 x1 x3
  let v0 := fun i => (x0 i)⁻¹*((MulAut.conj (h0 i)*PartIIProposition6_5.diagonalFieldGraph (a (j0 i)) (phi (j0 i)) (eps (j0 i)))^(d (j0 i))) (x0 i)
  let v1 := fun i => (x1 i)⁻¹*((MulAut.conj (h1 i)*PartIIProposition6_5.diagonalFieldGraph (a (j1 i)) (phi (j1 i)) (eps (j1 i)))^(d (j1 i))) (x1 i)
  let v2 := fun i => (x2 i)⁻¹*((MulAut.conj (h2 i)*PartIIProposition6_5.diagonalFieldGraph (a (j2 i)) (phi (j2 i)) (eps (j2 i)))^(d (j2 i))) (x2 i)
  let v3 := fun i => (x3 i)⁻¹*((MulAut.conj (h3 i)*PartIIProposition6_5.diagonalFieldGraph (a (j3 i)) (phi (j3 i)) (eps (j3 i)))^(d (j3 i))) (x3 i)
  have hvalues : (fun i => (x i)⁻¹*((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=
      join4 v0 v2 v1 v3 := by
    funext i
    simp only [x,h,join4,v0,v1,v2,v3]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left,j0]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left,Fin.append_right,j1]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [Fin.append_left,Fin.append_right,j2]
        · simp only [Fin.append_right,j3]
  refine ⟨x,?_⟩
  rw [hvalues,product_join4]
  change NikolovSegal.orderedProduct v0*NikolovSegal.orderedProduct v1*
    NikolovSegal.orderedProduct v2*NikolovSegal.orderedProduct v3=b
  rw [show NikolovSegal.orderedProduct v0=b0 from hp0,
    show NikolovSegal.orderedProduct v1=b1 from hp1,
    show NikolovSegal.orderedProduct v2=b2 from hp2,
    show NikolovSegal.orderedProduct v3=b3 from hp3]
  exact hprod
/-- The full group construction supplies the exact consumed q/e scalar
interface for the prescribed DΦΓ family. This is proved coverage, not an
unproved scalar input; it does not classify every bare automorphism. -/
theorem actual_uniform_SLn_DFG_scalar_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ (a : Fin N → Fin (k+4) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (e : Fin N → ℕ),
      PartIIScalarProductInput q N
        (fun i => PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)) e := by
  obtain ⟨N,C,hN,hfull⟩ := actual_uniform_inner_SLn_DFG_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF k a phi eps e he
  let beta := fun i => PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)
  have hd : ∀ i, 0<q/e i ∧ q/e i ∣ q := by
    intro i
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq (he i).2) (he i).1,Nat.div_dvd_of_dvd (he i).2⟩
  obtain ⟨h,hcover⟩ := hfull F hF k a phi eps (fun i => q/e i) hd
  let y := fun i => (beta i).symm ((h i)⁻¹)
  have hcorrection : ∀ i, beta i*MulAut.conj (y i)⁻¹=MulAut.conj (h i)*beta i := by
    intro i
    apply MulEquiv.ext; intro g
    simp only [y,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
      MulEquiv.apply_symm_apply,inv_inv]
  refine ⟨y,?_⟩
  intro target
  obtain ⟨x,hx⟩ := hcover target
  refine ⟨x,?_⟩
  simpa only [hcorrection,beta] using hx
end NikolovSegal.PartIISLnLargeFieldProduct
