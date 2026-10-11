/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCenterProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCenterProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalMiddleProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIIRadicalCenterProduct
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularFieldSupply
open PartIIRadicalCoordinates
universe u
variable {F : Type u} [Field F] {k M : ℕ}
private def centerDiagonal (a : Fin (k+3) → Fˣ) (lambda : Fˣ) : Fin (k+3) → Fˣ :=
  Fin.cons 1 (Fin.cons ((∏ i, a i)*lambda) (Fin.snoc (fun _ : Fin k => 1) lambda⁻¹))
private theorem center_product (a : Fin (k+3) → Fˣ) (lambda : Fˣ) :
    ∏ i, centerDiagonal a lambda i=∏ i, a i := by
  simp [centerDiagonal,Fin.prod_cons,Fin.prod_snoc,mul_assoc]
private theorem center_first_last (a : Fin (k+3) → Fˣ) (lambda : Fˣ) :
    centerDiagonal a lambda (first : Fin (k+3))=1 ∧
    centerDiagonal a lambda (last : Fin (k+3))=lambda⁻¹ := by
  constructor
  · simp [centerDiagonal,first]
  · have he : (last : Fin (k+3))=(Fin.last k).succ.succ := by apply Fin.ext; rfl
    rw [he]; simp [centerDiagonal]
private theorem diagonal_same_top (a b : Fin (k+3) → Fˣ)
    (hfirst : a first=b first) (hlast : a last=b last)
    (g : Matrix.SpecialLinearGroup (Fin (k+3)) F) (hg : LayerDepth (k+2) (g.val-1)) :
    (unitOdd% diagonalAut) a g=(unitOdd% diagonalAut) b g := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
  by_cases he : i=j
  · subst j
    have hi := hg i i (by omega)
    simp only [Matrix.sub_apply,Matrix.one_apply,ite_true] at hi
    rw [sub_eq_zero.mp hi]
    simp [mul_assoc]
  · by_cases hf : i=first
    · subst i
      by_cases hl : j=last
      · subst j; rw [hfirst,hlast]
      · have hv : j.val < k+2 := by
          have hh := j.isLt
          have hne : j.val≠k+2 := by intro h; apply hl; apply Fin.ext; exact h
          omega
        have hz := hg first j (by change j.val < 0+(k+2); omega)
        simp only [Matrix.sub_apply,Matrix.one_apply,if_neg he,sub_zero] at hz
        simp [hz]
    · have hv : 0 < i.val := by
        have hne : i.val≠0 := by intro h; apply hf; apply Fin.ext; exact h
        omega
      have hz := hg i j (by have hh := j.isLt; omega)
      simp only [Matrix.sub_apply,Matrix.one_apply,if_neg he,sub_zero] at hz
      simp [hz]
private theorem top_field_graph (phi : RingAut F) (eps : Bool)
    (g : Matrix.SpecialLinearGroup (Fin (k+3)) F) (hg : LayerDepth (k+2) (g.val-1)) :
    LayerDepth (k+2) ((fieldGraphAut phi eps g).val-1) :=
  (unitGraph% field_graph_depth) phi eps (k+2) (by omega) g hg
private theorem center_action (a : Fin (k+3) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (g : Matrix.SpecialLinearGroup (Fin (k+3)) F)
    (hg : LayerDepth (k+2) (g.val-1)) :
    PartIIProposition6_5.diagonalFieldGraph (centerDiagonal a lambda) phi eps g=
      (layerTorus (k+2) lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin (k+3)) F)) g := by
  change (unitOdd% diagonalAut) (centerDiagonal a lambda) (fieldGraphAut phi eps g)=
    (unitOdd% diagonalAut) (fun i => lambda⁻¹^(i.val/(k+2))) (fieldGraphAut phi eps g)
  apply diagonal_same_top
  · simp [center_first_last,first]
  · rw [(center_first_last a lambda).2]
    simp [last,show k+2≠0 by omega]
  · exact top_field_graph phi eps g hg
/-- The actual top layer is the corner subgroup of V. -/
theorem actual_top_layer_radical (g : Matrix.SpecialLinearGroup (Fin (k+3)) F)
    (hg : LayerDepth (k+2) (g.val-1)) : InRadical g := by
  refine ⟨(unitLayer% depth_mono) hg (by omega),?_⟩
  intro i j hi hj
  have hne : i.val≠0 := by intro he; apply hi; apply Fin.ext; exact he
  have hz := hg i j (by have hh := j.isLt; omega)
  exact sub_eq_zero.mp hz
/-- Every radical with zero noncorner coordinates is an actual corner
matrix, retaining its arbitrary corner. -/
theorem actual_zero_noncorner_top (g : Matrix.SpecialLinearGroup (Fin (k+3)) F)
    (hg : InRadical g)
    (hr : ∀ j : Fin (k+3), j≠first → j≠last → g first j=0)
    (hc : ∀ j : Fin (k+3), j≠first → j≠last → g j last=0) :
    LayerDepth (k+2) (g.val-1) := by
  intro i j hij
  by_cases he : i=j
  · subst j; exact hg.1 i i (by omega)
  · by_cases hi : i=first
    · subst i
      have hjl : j≠last := by intro h; subst j; change k+2 < 0+(k+2) at hij; omega
      have hj0 : j≠first := Ne.symm he
      simp only [Matrix.sub_apply,Matrix.one_apply,if_neg he,sub_zero,hr j hj0 hjl]
    · by_cases hj : j=last
      · subst j
        simp only [Matrix.sub_apply,Matrix.one_apply,if_neg he,sub_zero,hc i hi he]
      · exact sub_eq_zero.mpr (hg.2 i j hi hj)
/-- Genuine corner PRODUCT. The accepted highest-layer supplier is
consumed with an actual determinant-one correction, original d powers,
and exact equality (the next layer is zero). -/
theorem actual_inner_radical_center_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q)<Fintype.card F)
    (a : Fin M → Fin (k+3) → Fˣ) (phi : Fin M → RingAut F)
    (eps : Fin M → Bool) (d : Fin M → ℕ) (hd : ∀ i, 0<d i ∧ d i ∣ q) :
    ∃ h : Fin M → Matrix.SpecialLinearGroup (Fin (k+3)) F,
      (∀ i r c, r≠c → h i r c=0) ∧
      ∀ b : Matrix.SpecialLinearGroup (Fin (k+3)) F, LayerDepth (k+2) (b.val-1) →
        ∃ x : Fin M → Matrix.SpecialLinearGroup (Fin (k+3)) F,
          (∀ i, LayerDepth (k+2) ((x i).val-1)) ∧
          NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
            ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=b := by
  classical
  obtain ⟨lambda,hcover⟩ := PartIIUnitriangularGraphFixedLayers.actual_uniform_field_graph_fixed_layer_product
    (n:=k+3) (k+2) (by omega) hq hM hF phi eps d hd
  have hh : ∀ i, ∃ h : Matrix.SpecialLinearGroup (Fin (k+3)) F,
      (∀ r c, r≠c → h r c=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)=
        PartIIProposition6_5.diagonalFieldGraph (centerDiagonal (a i) (lambda i)) (phi i) (eps i) := by
    intro i
    exact PartIIRadicalInnerTorus.actual_diagonal_inner_normalization
      (a i) (centerDiagonal (a i) (lambda i)) (center_product _ _) (phi i) (eps i)
  choose h hh he using hh
  let alpha := fun i => PartIIProposition6_5.diagonalFieldGraph (centerDiagonal (a i) (lambda i)) (phi i) (eps i)
  let beta := fun i => (layerTorus (k+2) (lambda i)*fieldGraphAut (phi i) (eps i) : MulAut (Matrix.SpecialLinearGroup (Fin (k+3)) F))
  have hpower : ∀ i e g, LayerDepth (k+2) (g.val-1) →
      LayerDepth (k+2) (((beta i^e) g).val-1) ∧ (alpha i^e) g=(beta i^e) g := by
    intro i e
    induction e with
    | zero => intro g hg; exact ⟨hg,rfl⟩
    | succ e ih =>
      intro g hg
      obtain ⟨hp,heq⟩ := ih g hg
      have hp' := (unitOdd% diagonal_depth) (fun r : Fin (k+3) => (lambda i)⁻¹^(r.val/(k+2)))
        (k+2) _ (top_field_graph (phi i) (eps i) _ hp)
      constructor
      · simpa only [beta,layerTorus,pow_succ',MulAut.mul_apply] using hp'
      · calc
          _ = alpha i ((alpha i^e) g) := by rw [pow_succ',MulAut.mul_apply]
          _ = alpha i ((beta i^e) g) := congrArg (alpha i) heq
          _ = beta i ((beta i^e) g) := center_action _ _ _ _ _ hp
          _ = _ := by rw [pow_succ']; rfl
  refine ⟨h,hh,?_⟩
  intro b hb
  obtain ⟨x,hx,hres⟩ := hcover b hb
  refine ⟨x,hx,?_⟩
  simp only [he]
  have heq : ∀ i, ((alpha i)^(d i)) (x i)=((beta i)^(d i)) (x i) := fun i => (hpower i (d i) (x i) (hx i)).2
  change NikolovSegal.orderedProduct (fun i => (x i)⁻¹*(alpha i^(d i)) (x i))=b
  simp only [heq]
  let P := NikolovSegal.orderedProduct (fun i => (x i)⁻¹*(beta i^(d i)) (x i))
  have hzero : (P⁻¹*b).val-1=0 := (unitLayer% depth_n_zero) (by simpa only [Nat.add_assoc] using hres)
  have hunit : P⁻¹*b=1 := by apply Subtype.ext; exact sub_eq_zero.mp hzero
  change P=b
  calc
    P=P*(P⁻¹*b) := by rw [hunit,mul_one]
    _ = b := by group
end NikolovSegal.PartIIRadicalCenterProduct
