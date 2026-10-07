/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalMiddleProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalMiddleProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalActions
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIRadicalMiddleProduct
open PartIIRadicalCoordinates PartIIRadicalActions PartIIRadicalInnerTorus
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {k : ℕ}
/-- The actual middle roots of the printed radical quotient. Both
exceptional end pairs are excluded; the corner is not declared zero. -/
def Middle (j : Fin (k+3)) : Prop := 2≤j.val ∧ j.val+2<k+3
private theorem middle_interior (j : Fin (k+3)) (hj : Middle j) :
    j≠(first : Fin (k+3)) ∧ j≠last := by
  constructor <;> intro h <;> have he := congrArg Fin.val h
  · change j.val=0 at he; have hh := hj.1; omega
  · change j.val=k+2 at he; have hh := hj.2; omega
private theorem middle_rev (j : Fin (k+3)) (hj : Middle j) : Middle j.rev := by
  unfold Middle at *; simp only [Fin.val_rev]; omega
private theorem middle_diagonal (a : Fin (k+3) → Fˣ) (lambda : Fˣ)
    (j : Fin (k+3)) (hj : Middle j) : radicalDiagonal a lambda j=1 := by
  let i : Fin k := ⟨j.val-2,by have hh := hj.1; have hh' := hj.2; omega⟩
  have he : j=i.castSucc.succ.succ := by apply Fin.ext; change j.val=(j.val-2)+1+1; have hh := hj.1; omega
  rw [he]
  simp [radicalDiagonal]
private theorem diagonal_first_last (a : Fin (k+3) → Fˣ) (lambda : Fˣ) :
    radicalDiagonal a lambda⁻¹ (first : Fin (k+3))=lambda ∧
      radicalDiagonal a lambda⁻¹ (last : Fin (k+3))=lambda⁻¹ := by
  constructor
  · simp [radicalDiagonal,first]
  · have he : (last : Fin (k+3))=(Fin.last k).succ.succ := by apply Fin.ext; rfl
    rw [he]; simp [radicalDiagonal]
private theorem power_mem (a : Fin (k+3) → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : Matrix.SpecialLinearGroup (Fin (k+3)) F) (hg : InRadical g) (d : ℕ) :
    InRadical (((PartIIProposition6_5.diagonalFieldGraph a phi eps)^d) g) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using hg
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply]
    exact actual_diagonal_field_graph_radical_mem a phi eps _ ih
private theorem middle_doubled_power (a : Fin (k+3) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (g : Matrix.SpecialLinearGroup (Fin (k+3)) F)
    (hg : InRadical g) (j : Fin (k+3)) (hj : Middle j) (d : ℕ) :
    let beta := PartIIProposition6_5.diagonalFieldGraph (radicalDiagonal a lambda⁻¹) phi eps
    (beta^(2*d)) g first j=orbitProduct phi (2*d) (lambda:F)*(phi^(2*d)) (g first j) ∧
      (beta^(2*d)) g j.rev last=orbitProduct phi (2*d) (lambda:F)*(phi^(2*d)) (g j.rev last) := by
  dsimp only
  let beta := PartIIProposition6_5.diagonalFieldGraph (radicalDiagonal a lambda⁻¹) phi eps
  have hi := middle_interior j hj
  have ha := diagonal_first_last a lambda
  induction d with
  | zero => simp [orbitProduct]
  | succ d ih =>
    have hs := actual_radical_middle_square (radicalDiagonal a lambda⁻¹) phi eps lambda
      ((beta^(2*d)) g) (power_mem _ phi eps g hg _) j hi.1 hi.2 ha.1 ha.2
      (middle_diagonal a lambda⁻¹ j hj) (middle_diagonal a lambda⁻¹ j.rev (middle_rev j hj))
    rw [show 2*(d+1)=2+2*d by omega,pow_add,MulAut.mul_apply]
    change (beta^2) ((beta^(2*d)) g) first j=_ ∧ (beta^2) ((beta^(2*d)) g) j.rev last=_
    rw [hs.1,hs.2,ih.1,ih.2]
    have hN : orbitProduct phi (2+2*d) (lambda:F)=
        (lambda:F)*phi (lambda:F)*phi (phi (orbitProduct phi (2*d) (lambda:F))) := by
      rw [show 2+2*d=(2*d+1)+1 by omega,(rootFieldKernel% orbitProduct_succ),
        (rootFieldKernel% orbitProduct_succ),map_mul]; ring
    rw [hN]
    simp only [map_mul,pow_two,pow_add,RingAut.mul_apply]
    constructor <;> ring
/-- Actual original-d-power VALUE: norm witnesses are constructed inside
V, and both real row/column coordinates consume the doubled field map. -/
theorem actual_radical_middle_norm_value (a : Fin (k+3) → Fˣ) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (g : Matrix.SpecialLinearGroup (Fin (k+3)) F)
    (hg : InRadical g) (d : ℕ) :
    let beta := (PartIIProposition6_5.diagonalFieldGraph (radicalDiagonal a lambda⁻¹) phi eps)^d
    let x := g*beta g
    InRadical x ∧ InRadical (x⁻¹*beta x) ∧ ∀ j : Fin (k+3), Middle j →
      (x⁻¹*beta x) first j=fieldValue phi 1 (2*d) 1 (lambda:F) (g first j) ∧
      (x⁻¹*beta x) j.rev last=fieldValue phi 1 (2*d) 1 (lambda:F) (g j.rev last) := by
  dsimp only
  let beta := (PartIIProposition6_5.diagonalFieldGraph (radicalDiagonal a lambda⁻¹) phi eps)^d
  let x := g*beta g
  have hb : InRadical (beta g) := power_mem _ phi eps g hg d
  have hx : InRadical x := actual_radical_product_mem g (beta g) hg hb
  have hbx : InRadical (beta x) := power_mem _ phi eps x hx d
  refine ⟨hx,actual_radical_product_mem _ _ (actual_radical_inverse_mem x hx) hbx,?_⟩
  intro j hj
  have hi := middle_interior j hj
  have hir := middle_interior j.rev (middle_rev j hj)
  have hbb : InRadical (beta (beta g)) := power_mem _ phi eps (beta g) hb d
  have hv := actual_radical_product_row_column x⁻¹ (beta x) (actual_radical_inverse_mem x hx) hbx j hi.1 hi.2
  have hvr := actual_radical_product_row_column x⁻¹ (beta x) (actual_radical_inverse_mem x hx) hbx j.rev hir.1 hir.2
  have hxi := actual_radical_inverse_row_column x hx j hi.1 hi.2
  have hxir := actual_radical_inverse_row_column x hx j.rev hir.1 hir.2
  have hxx := actual_radical_product_row_column g (beta g) hg hb j hi.1 hi.2
  have hxxr := actual_radical_product_row_column g (beta g) hg hb j.rev hir.1 hir.2
  have hbxx := actual_radical_product_row_column (beta g) (beta (beta g)) hb hbb j hi.1 hi.2
  have hbxxr := actual_radical_product_row_column (beta g) (beta (beta g)) hb hbb j.rev hir.1 hir.2
  have he : beta (beta g)=((PartIIProposition6_5.diagonalFieldGraph (radicalDiagonal a lambda⁻¹) phi eps)^(2*d)) g := by
    simp only [beta,← MulAut.mul_apply,← pow_add,show d+d=2*d by omega]
  have hp := middle_doubled_power a lambda phi eps g hg j hj d
  constructor
  · rw [hv.1,hxi.1]
    change -(g*beta g) first j+beta (g*beta g) first j=_
    rw [map_mul,hxx.1,hbxx.1,he,hp.1]
    simp only [fieldValue,one_mul,pow_one]; ring
  · rw [hvr.2,hxir.2]
    change -(g*beta g) j.rev last+beta (g*beta g) j.rev last=_
    rw [map_mul,hxxr.2,hbxxr.2,he,hp.2]
    simp only [fieldValue,one_mul,pow_one]; ring
private theorem ordered_radical {M : ℕ}
    (v : Fin M → Matrix.SpecialLinearGroup (Fin (k+3)) F) (hv : ∀ i, InRadical (v i)) :
    InRadical (NikolovSegal.orderedProduct v) ∧ ∀ j : Fin (k+3), j≠first → j≠last →
      (NikolovSegal.orderedProduct v) first j=∑ i, v i first j ∧
      (NikolovSegal.orderedProduct v) j last=∑ i, v i j last := by
  induction M with
  | zero =>
    simp only [NikolovSegal.orderedProduct,List.ofFn_zero,List.prod_nil]
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i j h; simp
    · intro i j hi hj; rfl
    · intro j hj0 hjl; simp [Matrix.one_apply,Ne.symm hj0,hjl]
  | succ M ih =>
    have ht := ih (fun i => v i.succ) (fun i => hv i.succ)
    have he : NikolovSegal.orderedProduct v=v 0*NikolovSegal.orderedProduct (fun i => v i.succ) := by
      simp only [NikolovSegal.orderedProduct,List.ofFn_succ,List.prod_cons]
    rw [he]
    refine ⟨actual_radical_product_mem _ _ (hv 0) ht.1,?_⟩
    intro j hj0 hjl
    rw [(actual_radical_product_row_column _ _ (hv 0) ht.1 j hj0 hjl).1,
      (actual_radical_product_row_column _ _ (hv 0) ht.1 j hj0 hjl).2,(ht.2 j hj0 hjl).1,(ht.2 j hj0 hjl).2]
    simp only [Fin.sum_univ_succ]
    trivial
/-- Actual p263 middle quotient PRODUCT with determinant-one INNER
corrections. One global h is chosen before every full radical target.
The result matches all actual middle coordinates; it deliberately leaves
boundary and corner residuals for the subsequent original V stages. -/
theorem actual_inner_radical_middle_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q)<Fintype.card F)
    (a : Fin M → Fin (k+3) → Fˣ) (phi : Fin M → RingAut F)
    (eps : Fin M → Bool) (d : Fin M → ℕ) (hd : ∀ i, 0<d i ∧ d i ∣ q) :
    ∃ h : Fin M → Matrix.SpecialLinearGroup (Fin (k+3)) F,
      (∀ i r c, r≠c → h i r c=0) ∧
      ∀ b : Matrix.SpecialLinearGroup (Fin (k+3)) F, InRadical b →
        ∃ x : Fin M → Matrix.SpecialLinearGroup (Fin (k+3)) F,
          (∀ i, InRadical (x i)) ∧
          let P := NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
            ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))
          InRadical P ∧ ∀ j : Fin (k+3), Middle j →
            P first j=b first j ∧ P j.rev last=b j.rev last := by
  classical
  have hq2 : 0<2*q := by omega
  have hd2 : ∀ i, 0<2*d i ∧ 2*d i ∣ 2*q := fun i =>
    ⟨by have hh := (hd i).1; omega,Nat.mul_dvd_mul_left 2 (hd i).2⟩
  obtain ⟨l,hl,hs⟩ := lemma7_1 (c:=1) hq2 (by simpa using hM) (by simpa using hF)
    phi (fun _ => 1) (fun i => 2*d i) (fun _ => 1) (fun _ => one_ne_zero) hd2 (fun _ => by simp)
  let lambda : Fin M → Fˣ := fun i => Units.mk0 (l i) (hl i)
  have hc : ∀ i, ∃ h : Matrix.SpecialLinearGroup (Fin (k+3)) F,
      (∀ r c, r≠c → h r c=0) ∧
      MulAut.conj h*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)=
        PartIIProposition6_5.diagonalFieldGraph (radicalDiagonal (a i) (lambda i)⁻¹) (phi i) (eps i) := by
    intro i
    exact actual_radical_inner_torus (a i) (lambda i)⁻¹ (phi i) (eps i)
  choose h hh he using hc
  refine ⟨h,hh,?_⟩
  intro b hb
  have htR : ∀ j : {j : Fin (k+3) // Middle j}, ∃ t : Fin M → F,
      (∑ i, fieldValue (phi i) 1 (2*d i) 1 (l i) (t i))=b first j.val := fun j => hs _
  have htC : ∀ j : {j : Fin (k+3) // Middle j}, ∃ t : Fin M → F,
      (∑ i, fieldValue (phi i) 1 (2*d i) 1 (l i) (t i))=b j.val.rev last := fun j => hs _
  choose tR htR using htR
  choose tC htC using htC
  let r : Fin M → Fin (k+3) → F := fun i j => if hj : Middle j then tR ⟨j,hj⟩ i else 0
  let c : Fin M → Fin (k+3) → F := fun i j => if hj : Middle j.rev then tC ⟨j.rev,hj⟩ i else 0
  have hr : ∀ i, EndpointZero (r i) := by
    intro i; constructor <;> simp [r,Middle,first,last,Fin.val_rev]
  have hcc : ∀ i, EndpointZero (c i) := by
    intro i; constructor <;> simp [c,Middle,first,last,Fin.val_rev]
  let g := fun i => radical (r i) (c i) (hr i) (hcc i) 0
  have hg : ∀ i, InRadical (g i) := fun i => actual_radical_mem _ _ _ _ _
  let beta := fun i => (PartIIProposition6_5.diagonalFieldGraph
    (radicalDiagonal (a i) (lambda i)⁻¹) (phi i) (eps i))^(d i)
  let x := fun i => g i*beta i (g i)
  let v := fun i => (x i)⁻¹*beta i (x i)
  have hv := fun i => actual_radical_middle_norm_value (a i) (lambda i) (phi i) (eps i) (g i) (hg i) (d i)
  have hP := ordered_radical v (fun i => (hv i).2.1)
  refine ⟨x,fun i => (hv i).1,?_⟩
  simp only [he]
  change InRadical (NikolovSegal.orderedProduct v) ∧ _
  refine ⟨hP.1,?_⟩
  intro j hj
  have hi := middle_interior j hj
  have hir := middle_interior j.rev (middle_rev j hj)
  rw [(hP.2 j hi.1 hi.2).1,(hP.2 j.rev hir.1 hir.2).2]
  have hvR : ∀ i, v i first j=fieldValue (phi i) 1 (2*d i) 1 (l i) (tR ⟨j,hj⟩ i) := by
    intro i; rw [((hv i).2.2 j hj).1,actual_radical_row _ _ _ _ _ j hi.1 hi.2]
    simp only [r,dif_pos hj]; rfl
  have hvC : ∀ i, v i j.rev last=fieldValue (phi i) 1 (2*d i) 1 (l i) (tC ⟨j,hj⟩ i) := by
    intro i; rw [((hv i).2.2 j hj).2,actual_radical_column _ _ _ _ _ j.rev hir.1 hir.2]
    simp only [c,Fin.rev_rev,dif_pos hj]; rfl
  simp only [hvR,hvC]
  exact ⟨htR ⟨j,hj⟩,htC ⟨j,hj⟩⟩
/-- Exact remaining matrix after the consumed middle quotient PRODUCT.
All middle entries vanish in P^-1*b; its ordered corner and exceptional
boundary coordinates are retained, not silently discarded. -/
theorem actual_middle_residual (P b : Matrix.SpecialLinearGroup (Fin (k+3)) F)
    (hP : InRadical P) (hb : InRadical b)
    (hmatch : ∀ j : Fin (k+3), Middle j → P first j=b first j ∧ P j.rev last=b j.rev last) :
    InRadical (P⁻¹*b) ∧ ∀ j : Fin (k+3), Middle j →
      (P⁻¹*b) first j=0 ∧ (P⁻¹*b) j.rev last=0 := by
  have hPi := actual_radical_inverse_mem P hP
  refine ⟨actual_radical_product_mem _ _ hPi hb,?_⟩
  intro j hj
  have hi := middle_interior j hj
  have hir := middle_interior j.rev (middle_rev j hj)
  have hr := actual_radical_product_row_column P⁻¹ b hPi hb j hi.1 hi.2
  have hc := actual_radical_product_row_column P⁻¹ b hPi hb j.rev hir.1 hir.2
  have hri := actual_radical_inverse_row_column P hP j hi.1 hi.2
  have hci := actual_radical_inverse_row_column P hP j.rev hir.1 hir.2
  rw [hr.1,hc.2,hri.1,hci.2,(hmatch j hj).1,(hmatch j hj).2]
  simp
end NikolovSegal.PartIIRadicalMiddleProduct
