/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLeviProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLeviProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIICentralLevi
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIICentralLeviProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIICentralLevi
universe u
variable {F : Type u} [Field F] {n : ℕ}
private def extendDiagonal (eta : Fin n → Fˣ) : Fin (n+2) → Fˣ :=
  Fin.cons (∏ i, eta i)⁻¹ (Fin.snoc eta 1)
private theorem extend_product (eta : Fin n → Fˣ) : ∏ i, extendDiagonal eta i=1 := by
  simp [extendDiagonal,Fin.prod_cons,Fin.prod_snoc]
private theorem extend_middle (eta : Fin n → Fˣ) (i : Fin n) :
    extendDiagonal eta (middle i)=eta i := by simp [extendDiagonal,middle]
private theorem diagonal_mul (a b : Fin n → Fˣ) :
    (unitOdd% diagonalAut) a*(unitOdd% diagonalAut) b=
      (unitOdd% diagonalAut) (fun i => a i*b i) := by
  apply MulEquiv.ext; intro g
  apply SpecialLinearGroup.ext; intro i j
  rw [MulAut.mul_apply,(unitOdd% diagonal_entry),(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
  simp only [Units.val_mul,_root_.mul_inv_rev,Units.val_inv_eq_inv_val]
  ring
/-- Printed p255 central-Levi consumption of actual Proposition6.5.
Every arbitrary central diagonal correction is implemented by an actual
ambient determinant-one element. The ambient inner tuple is fixed before
ALL targets, and the exact prescribed-power commutator VALUES equal the
actual embedded target. This is central U, not yet full ambient U or SL. -/
theorem actual_uniform_inner_central_levi_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ n : ℕ,
      ∀ (a : Fin N → Fin (n+2) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (d : Fin N → ℕ), (∀ i, 0<d i ∧ d i ∣ q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (n+2)) F,
        ∀ b : SpecialLinearGroup (Fin n) F, LayerDepth 1 (b.val-1) →
          ∃ x : Fin N → SpecialLinearGroup (Fin n) F,
            (∀ i, LayerDepth 1 ((x i).val-1)) ∧
            NikolovSegal.orderedProduct (fun i => (embed (x i))⁻¹*
              ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (embed (x i)))=embed b := by
  classical
  obtain ⟨N,C,hN,hcover⟩ := PartIIProposition6_5.actual_proposition6_5_uniform_diagonal_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF n a phi eps d hd
  let a' : Fin N → Fin n → Fˣ := fun j i => a j (middle i)
  obtain ⟨eta,u,hu,hU⟩ := hcover F hF n a' phi eps d hd
  let B : Fin N → Fin (n+2) → Fˣ := fun j i => extendDiagonal (eta j) i*a j i
  have hB : ∀ j, ∏ i, B j i=∏ i, a j i := by
    intro j; simp only [B,Finset.prod_mul_distrib,extend_product,one_mul]
  have hD : ∀ j, ∃ h : SpecialLinearGroup (Fin (n+2)) F,
      (∀ r c : Fin (n+2), r≠c → h r c=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) (eps j)=
        PartIIProposition6_5.diagonalFieldGraph (B j) (phi j) (eps j) := by
    intro j
    exact PartIIRadicalInnerTorus.actual_diagonal_inner_normalization
      (a j) (B j) (hB j) (phi j) (eps j)
  choose hD hhD heD using hD
  let h : Fin N → SpecialLinearGroup (Fin (n+2)) F := fun j => embed (u j)*hD j
  let alpha : Fin N → MulAut (SpecialLinearGroup (Fin n) F) := fun j =>
    MulAut.conj (u j)*(unitOdd% diagonalAut) (eta j)*PartIIProposition6_5.diagonalFieldGraph (a' j) (phi j) (eps j)
  let alphaA : Fin N → MulAut (SpecialLinearGroup (Fin (n+2)) F) := fun j =>
    MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) (eps j)
  have hstep : ∀ j g, alphaA j (embed g)=embed (alpha j g) := by
    intro j g
    have hbc : (fun i => B j (middle i))=fun i => eta j i*a' j i := by
      funext i; simp only [B,extend_middle,a']
    have hac : alpha j=MulAut.conj (u j)*PartIIProposition6_5.diagonalFieldGraph
        (fun i => eta j i*a' j i) (phi j) (eps j) := by
      dsimp only [alpha,PartIIProposition6_5.diagonalFieldGraph]
      rw [mul_assoc,← mul_assoc ((unitOdd% diagonalAut) (eta j)),diagonal_mul]
    dsimp only [alphaA,h]
    rw [map_mul,mul_assoc,heD j,MulAut.mul_apply,actual_central_levi_action,hbc,hac]
    simp only [MulAut.mul_apply,MulAut.conj_apply,← map_inv,← map_mul]
  have hpower : ∀ j e g, (alphaA j^e) (embed g)=embed ((alpha j^e) g) := by
    intro j e
    induction e with
    | zero => intro g; rfl
    | succ e ih =>
      intro g
      calc
        _ = alphaA j ((alphaA j^e) (embed g)) := by rw [pow_succ',MulAut.mul_apply]
        _ = alphaA j (embed ((alpha j^e) g)) := congrArg (alphaA j) (ih g)
        _ = embed (alpha j ((alpha j^e) g)) := hstep j _
        _ = _ := by rw [pow_succ']; rfl
  refine ⟨h,?_⟩
  intro b hb
  obtain ⟨x,hx,hxe⟩ := hU b hb
  refine ⟨x,hx,?_⟩
  change NikolovSegal.orderedProduct (fun i => (embed (x i))⁻¹*(alphaA i^(d i)) (embed (x i)))=embed b
  simp only [hpower,← map_inv,← map_mul]
  have he := congrArg (fun g => embed g) hxe
  simpa only [alpha,NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def] using he
end NikolovSegal.PartIICentralLeviProduct
