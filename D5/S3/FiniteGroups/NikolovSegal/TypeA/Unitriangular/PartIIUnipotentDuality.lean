/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnipotentDuality
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnipotentDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIAmbientUnipotentProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace NikolovSegal.PartIIUnipotentDuality
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] {n : ℕ}
private theorem transpose_inverse (g : SpecialLinearGroup (Fin n) F) :
    (g.transpose)⁻¹=(g⁻¹).transpose := by
  apply Subtype.ext
  change Matrix.adjugate g.val.transpose=(Matrix.adjugate g.val).transpose
  exact (Matrix.adjugate_transpose g.val).symm
/-- Genuine inverse-transpose group automorphism, used to transport U to L. -/
def dual : MulAut (SpecialLinearGroup (Fin n) F) where
  toFun g := (g⁻¹).transpose
  invFun g := (g⁻¹).transpose
  left_inv g := by
    change (((g⁻¹).transpose)⁻¹).transpose=g
    rw [transpose_inverse,inv_inv]
    apply Subtype.ext; exact Matrix.transpose_transpose g.val
  right_inv g := by
    change (((g⁻¹).transpose)⁻¹).transpose=g
    rw [transpose_inverse,inv_inv]
    apply Subtype.ext; exact Matrix.transpose_transpose g.val
  map_mul' g h := by
    apply Subtype.ext
    simp only [_root_.mul_inv_rev,SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_transpose,Matrix.transpose_mul]
private theorem dual_entry (g : SpecialLinearGroup (Fin n) F) (i j : Fin n) :
    dual g i j=g⁻¹ j i := rfl
private theorem dual_twice (g : SpecialLinearGroup (Fin n) F) : dual (dual g)=g :=
  dual.left_inv g
private theorem dual_field (phi : RingAut F) (g : SpecialLinearGroup (Fin n) F) :
    dual (fieldAut phi g)=fieldAut phi (dual g) := by
  apply SpecialLinearGroup.ext; intro i j
  rw [dual_entry,← map_inv]; rfl
private theorem dual_diagonal (a : Fin n → Fˣ) (g : SpecialLinearGroup (Fin n) F) :
    dual ((unitOdd% diagonalAut) a g)=
      (unitOdd% diagonalAut) (fun i => (a i)⁻¹) (dual g) := by
  apply SpecialLinearGroup.ext; intro i j
  rw [dual_entry,← map_inv,(unitOdd% diagonal_entry),(unitOdd% diagonal_entry),dual_entry]
  simp only [inv_inv,Units.val_inv_eq_inv_val]
  ring
private theorem dual_raw_graph (g : SpecialLinearGroup (Fin n) F) :
    dual ((unitAction% rawGraph) g)=(unitAction% rawGraph) (dual g) := by
  apply SpecialLinearGroup.ext; intro i j
  rw [dual_entry,← map_inv,(unitAction% rawGraph_entry),(unitAction% rawGraph_entry),← map_inv,dual_entry]
private theorem dual_negative_torus (g : SpecialLinearGroup (Fin n) F) :
    dual (heightTorus (-1:Fˣ) g)=heightTorus (-1:Fˣ) (dual g) := by
  apply SpecialLinearGroup.ext; intro i j
  rw [dual_entry,← map_inv,(unitAction% torus_entry),(unitAction% torus_entry),dual_entry]
  simp only [inv_neg,inv_one,Units.val_neg,Units.val_one]
  ring
private theorem dual_field_graph (phi : RingAut F) (eps : Bool) (g : SpecialLinearGroup (Fin n) F) :
    dual (fieldGraphAut phi eps g)=fieldGraphAut phi eps (dual g) := by
  cases eps
  · exact dual_field phi g
  · change dual (fieldAut phi (heightTorus (-1:Fˣ) ((unitAction% rawGraph) g)))=_
    rw [dual_field,dual_negative_torus,dual_raw_graph]; rfl
/-- Exact tuple-action transport, including positive-graph signs. -/
theorem actual_dual_diagonal_field_graph (a : Fin n → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : SpecialLinearGroup (Fin n) F) :
    dual (PartIIProposition6_5.diagonalFieldGraph a phi eps g)=
      PartIIProposition6_5.diagonalFieldGraph (fun i => (a i)⁻¹) phi eps (dual g) := by
  change dual ((unitOdd% diagonalAut) a (fieldGraphAut phi eps g))=_
  rw [dual_diagonal,dual_field_graph]; rfl
theorem actual_unitriangular_upper_iff (g : SpecialLinearGroup (Fin n) F) :
    LayerDepth 1 (g.val-1) ↔ SLnUnipotentWidth.Upper g := by
  constructor
  · intro hg
    constructor
    · intro i j hij
      have hne : i≠j := ne_of_gt hij
      have he := hg i j (by change j.val < i.val+1; change j.val < i.val at hij; omega)
      simpa only [Matrix.sub_apply,Matrix.one_apply,if_neg hne,sub_zero] using he
    · intro i
      exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true] using hg i i (by omega))
  · intro hg i j hij
    by_cases he : i=j
    · subst j; simp only [Matrix.sub_apply,Matrix.one_apply,ite_true,hg.2 i,sub_self]
    · have hj : j < i := by change j.val < i.val; change j.val < i.val+1 at hij; have hne : i.val≠j.val := Fin.val_ne_of_ne he; omega
      simp only [Matrix.sub_apply,Matrix.one_apply,if_neg he,sub_zero,hg.1 i j hj]
/-- Actual lower target becomes upper under inverse-transpose. -/
theorem actual_dual_lower_target (g : SpecialLinearGroup (Fin n) F)
    (hg : SLnUnipotentWidth.Lower g) : LayerDepth 1 ((dual g).val-1) := by
  have ht : LayerDepth 1 (g.transpose.val-1) := by
    rw [actual_unitriangular_upper_iff]
    exact ⟨fun i j hij => hg.1 j i hij,fun i => hg.2 i⟩
  have he : dual g=(g.transpose)⁻¹ := (transpose_inverse g).symm
  rw [he]
  exact (unitLayer% inverse_unit_depth) _ ht
/-- Lower coverage follows by the actual action transport. Corrections
remain inner SL and precede all lower targets; original divisor powers stay. -/
theorem actual_uniform_inner_ambient_L_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ (a : Fin N → Fin (k+4) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (d : Fin N → ℕ), (∀ i, 0<d i ∧ d i ∣ q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (k+4)) F,
        ∀ b : SpecialLinearGroup (Fin (k+4)) F, SLnUnipotentWidth.Lower b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (k+4)) F,
            NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
              ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=b := by
  obtain ⟨N,C,hN,hU⟩ := PartIIAmbientUnipotentProduct.actual_uniform_inner_ambient_U_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF k a phi eps d hd
  obtain ⟨h',hcover⟩ := hU F hF k (fun j i => (a j i)⁻¹) phi eps d hd
  let h : Fin N → SpecialLinearGroup (Fin (k+4)) F := fun i => dual (h' i)
  let beta' := fun i => MulAut.conj (h' i)*PartIIProposition6_5.diagonalFieldGraph (fun j => (a i j)⁻¹) (phi i) (eps i)
  let beta := fun i => MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)
  have hstep : ∀ i g, dual (beta' i g)=beta i (dual g) := by
    intro i g
    simp only [beta',beta,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
      actual_dual_diagonal_field_graph,inv_inv,h]
  have hpower : ∀ i e g, dual ((beta' i^e) g)=(beta i^e) (dual g) := by
    intro i e
    induction e with
    | zero => intro g; rfl
    | succ e ih =>
      intro g
      calc
        _ = dual (beta' i ((beta' i^e) g)) := by rw [pow_succ']; rfl
        _ = beta i (dual ((beta' i^e) g)) := hstep i _
        _ = beta i ((beta i^e) (dual g)) := congrArg (beta i) (ih g)
        _ = _ := by rw [pow_succ']; rfl
  refine ⟨h,?_⟩
  intro b hb
  obtain ⟨x',hx',hp⟩ := hcover (dual b) (actual_dual_lower_target b hb)
  let x := fun i => dual (x' i)
  refine ⟨x,?_⟩
  have he := congrArg (fun g => dual g) hp
  simp only [NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,
    map_mul,map_inv,dual_twice] at he
  change NikolovSegal.orderedProduct (fun i => (x i)⁻¹*(beta i^(d i)) (x i))=b
  simpa only [NikolovSegal.orderedProduct,beta',hpower,x] using he
end NikolovSegal.PartIIUnipotentDuality
