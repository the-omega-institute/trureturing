/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalPrescribedMiddleProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "vPrescribed%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalPrescribedMiddleProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalPrescribedMiddleProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual prescribed V kernel {id} not found"
/-! PartII Proposition6.7 pp262–263: actual two exceptional V* root
pairs. The supported unitary witness retains its true corner; the
chosen row coefficient is u^2 and consumes the proved field lemma.
This is a FIELD-action stage, not a prescribed-D normalization claim. -/
namespace NikolovSegal.PartIIUnitaryRadicalBoundaryFieldProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus PartIIFieldMaps UnitaryField
open PartIIUnitaryRadicalTraceCoordinates PartIIUnitaryRadicalMiddleFieldProduct
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}
def axis (eps : Bool) : Fin (k+4) := if eps then ⟨k+2,by omega⟩ else 1
private def secondWeight (ι : RingAut F) (eps : Bool) (u : Fˣ) : Fˣ :=
  if eps then involutionUnit ι u else u⁻¹
private def weights (ι : RingAut F) (eps : Bool) (u : Fˣ) : Fin (k+4) → Fˣ :=
  (vNormalize% innerWeights) ι u (secondWeight ι eps u)
private theorem weights_product (ι : RingAut F) (hinv : Function.Involutive ι)
    (eps : Bool) (u : Fˣ) : ∏ i, weights (k:=k) ι eps u i=1 := by
  rw [weights,vNormalize% innerWeights_product]
  have hi : involutionUnit ι (involutionUnit ι u)=u := by apply Units.ext; exact hinv (u:F)
  cases eps <;> simp [secondWeight,hi,map_inv,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
private theorem axis_interior (eps : Bool) : (axis (k:=k) eps)≠first ∧ axis (k:=k) eps≠last := by
  cases eps <;> constructor <;> simp [axis,first,last,Fin.ext_iff] <;> omega
private theorem weights_axis (ι : RingAut F) (hinv : Function.Involutive ι)
    (eps : Bool) (u : Fˣ) : weights ι eps u (axis (k:=k) eps)=u⁻¹ := by
  cases eps
  · rfl
  · have he : (⟨k+2,by omega⟩:Fin (k+4))=(Fin.last (k+1)).castSucc.succ := by apply Fin.ext; rfl
    simp only [weights,axis,ite_true,secondWeight]
    change (unitaryCentral% extendWeights) ι
      ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1) (involutionUnit ι u)) u _=u⁻¹
    rw [he]
    change (Fin.cons u (Fin.snoc (Fin.cons (involutionUnit ι u)
      (Fin.snoc (fun _ : Fin k => (1:Fˣ)) (involutionUnit ι (involutionUnit ι u))⁻¹))
      (involutionUnit ι u)⁻¹) : Fin (k+4) → Fˣ) (Fin.last (k+1)).castSucc.succ=u⁻¹
    rw [Fin.cons_succ,Fin.snoc_castSucc]
    have he2 : (Fin.last (k+1):Fin (k+2))=(Fin.last k).succ := by apply Fin.ext; rfl
    rw [he2,Fin.cons_succ,Fin.snoc_last]
    congr 1
    apply Units.ext; exact hinv (u:F)
private def action (ι : RingAut F) (eps : Bool) (u : Fˣ) (phi : RingAut F) :
    MulAut (SpecialLinearGroup (Fin (k+4)) F) :=
  (vPrescribed% beta) ι u (secondWeight ι eps u) phi
private theorem row_step (ι : RingAut F) (eps : Bool) (u : Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+4)) F) (j : Fin (k+4)) :
    action ι eps u phi g first j=(u:F)*(weights ι eps u j:F)⁻¹*phi (g first j) := by
  change (unitOdd% diagonalAut) (weights ι eps u) (fieldAut phi g) first j=_
  rw [unitOdd% diagonal_entry]
  have h0 : weights ι eps u (first:Fin (k+4))=u := rfl
  simp only [h0,Units.val_inv_eq_inv_val]
  change (u:F)*phi (g first j)*(weights ι eps u j:F)⁻¹=_
  ring
private theorem axis_power (ι : RingAut F) (hinv : Function.Involutive ι)
    (eps : Bool) (u : Fˣ) (phi : RingAut F) (s : ℕ)
    (g : SpecialLinearGroup (Fin (k+4)) F) :
    (action ι eps u phi^s) g first (axis eps)=
      (orbitProduct phi s (u:F))^2*(phi^s) (g first (axis eps)) := by
  induction s with
  | zero => simp [orbitProduct]
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,row_step,weights_axis ι hinv,
      Units.val_inv_eq_inv_val,inv_inv,ih,rootFieldKernel% orbitProduct_succ,
      map_mul,map_pow,pow_succ' phi s,RingAut.mul_apply]
    ring
private theorem zero_power (ι : RingAut F) (eps : Bool) (u : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (j : Fin (k+4))
    (hg : g first j=0) : (action ι eps u phi^s) g first j=0 := by
  induction s with
  | zero => exact hg
  | succ s ih => rw [pow_succ',MulAut.mul_apply,row_step,ih,map_zero,mul_zero]

/-- ONE genuine unitary torus tuple precedes ALL targets. Actual
commutator VALUES reconstruct the chosen exceptional row, vanish on
ALL other noncorner rows, and retain the real ordered corner. Both
boundary orientations and all original positive s|q are included. -/
theorem actual_unitary_radical_boundary_field_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : q*(2*q+1)<M) (hF : 2*(2*q+1)^q<Fintype.card F)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (eps : Bool) (phi : Fin M → RingAut F) (s : Fin M → ℕ)
    (hs : ∀ j, 0<s j ∧ s j∣q) :
    ∃ u : Fin M → Fˣ, ∃ h : Fin M → SpecialLinearGroup (Fin (k+4)) F,
      (∀ j, h j=(radicalTorus% diagonalSL) (weights ι eps (u j)) (weights_product ι hinv eps (u j))) ∧
      (∀ j, steinberg ι (h j)=h j) ∧
      ∀ b : SpecialLinearGroup (Fin (k+4)) F, InRadical b → steinberg ι b=b →
        ∃ x : Fin M → SpecialLinearGroup (Fin (k+4)) F,
          (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
          (∀ i j, j≠first → j≠last → j≠axis eps → x i first j=0) ∧
          let P := orderedProduct (fun j => (x j)⁻¹*
            ((MulAut.conj (h j)*fieldAut (n:=k+4) (phi j))^(s j)) (x j))
          InRadical P ∧ steinberg ι P=P ∧
            ∀ j : Fin (k+4), j≠first → j≠last →
              P first j=if j=axis eps then b first j else 0 := by
  classical
  obtain ⟨lambda,hlambda,hcover⟩ := lemma7_1 (c:=2) hq hM hF phi
    (fun _ => 1) s (fun _ => 2) (fun _ => one_ne_zero) hs (fun _ => ⟨by decide,by decide⟩)
  let u := fun j => Units.mk0 (lambda j) (hlambda j)
  let h := fun j => (radicalTorus% diagonalSL) (weights (k:=k) ι eps (u j))
    (weights_product ι hinv eps (u j))
  have hhu : ∀ j, steinberg ι (h j)=h j := fun j =>
    (unitaryTorus% diagonal_fixed) ι _ _
      ((vNormalize% innerWeights_unitary) ι hinv (u j) (secondWeight ι eps (u j)))
  have he : ∀ j, MulAut.conj (h j)*fieldAut (n:=k+4) (phi j)=action ι eps (u j) (phi j) := by
    intro j
    dsimp only [h]
    rw [radicalTorus% diagonalSL_action]
    rfl
  refine ⟨u,h,fun _ => rfl,hhu,?_⟩
  intro b hb hbu
  obtain ⟨t,ht⟩ := hcover (b first (axis eps))
  let r : Fin M → Fin (k+4) → F := fun i j => if j=axis eps then t i else 0
  have hi := axis_interior (k:=k) eps
  have hr : ∀ i, EndpointZero (r i) := by
    intro i; constructor <;> simp [r,Ne.symm hi.1,Ne.symm hi.2]
  have hl := fun i => actual_unitary_radical_row_lift ι hinv hne (r i) (hr i)
  choose col hc z hcol htrace hxV hxU using hl
  let x : Fin M → SpecialLinearGroup (Fin (k+4)) F := fun i => radical (r i) (col i) (hr i) (hc i) (z i)
  let values : Fin M → SpecialLinearGroup (Fin (k+4)) F := fun i => (x i)⁻¹*(action ι eps (u i) (phi i)^(s i)) (x i)
  have hxV' : ∀ i, InRadical (x i) := hxV
  have hxU' : ∀ i, steinberg ι (x i)=x i := hxU
  have haV : ∀ i, InRadical ((action ι eps (u i) (phi i)^(s i)) (x i)) := by
    intro i
    exact (vPrescribed% beta_radical) ι (u i) (secondWeight ι eps (u i)) (phi i) (s i) (x i) (hxV' i)
  have haU : ∀ i, steinberg ι ((action ι eps (u i) (phi i)^(s i)) (x i))=
      (action ι eps (u i) (phi i)^(s i)) (x i) := by
    intro i
    exact (vPrescribed% beta_unitary) ι hinv hne (u i) (secondWeight ι eps (u i)) (phi i) (s i) (x i) (hxU' i)
  have hvV : ∀ i, InRadical (values i) := fun i => actual_radical_product_mem _ _
    (actual_radical_inverse_mem _ (hxV' i)) (haV i)
  have hvU : ∀ i, steinberg ι (values i)=values i := by
    intro i
    change steinberg ι ((x i)⁻¹*(action ι eps (u i) (phi i)^(s i)) (x i))=_
    rw [map_mul,map_inv,hxU' i,haU i]
  have hP := (radicalMiddle% ordered_radical) values hvV
  refine ⟨x,fun i => ⟨hxV i,hxU i⟩,?_,?_,?_,?_⟩
  · intro i j hj0 hjl hja
    rw [actual_radical_row _ _ _ _ _ j hj0 hjl]
    simp only [r,if_neg hja]
  · simpa only [he] using hP.1
  · simp only [he]
    change steinberg ι (orderedProduct values)=orderedProduct values
    simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,hvU]
  · intro j hj0 hjl
    simp only [he]
    change orderedProduct values first j=_
    rw [(hP.2 j hj0 hjl).1]
    by_cases hj : j=axis eps
    · subst j
      have hv : ∀ i, values i first (axis eps)=fieldValue (phi i) 1 (s i) 2 (lambda i) (t i) := by
        intro i
        change ((x i)⁻¹*(action ι eps (u i) (phi i)^(s i)) (x i)) first (axis eps)=_
        rw [(actual_radical_product_row_column _ _ (actual_radical_inverse_mem _ (hxV' i)) (haV i)
          (axis eps) hi.1 hi.2).1,
          (actual_radical_inverse_row_column _ (hxV' i) (axis eps) hi.1 hi.2).1,
          axis_power ι hinv,actual_radical_row _ _ _ _ _ _ hi.1 hi.2]
        simp only [r,ite_true,u,Units.val_mk0,fieldValue,one_mul]
        ring
      simp only [hv,ite_true]
      exact ht
    · have hv : ∀ i, values i first j=0 := by
        intro i
        have hz : x i first j=0 := by rw [actual_radical_row _ _ _ _ _ j hj0 hjl]; simp [r,hj]
        change ((x i)⁻¹*(action ι eps (u i) (phi i)^(s i)) (x i)) first j=0
        rw [(actual_radical_product_row_column _ _ (actual_radical_inverse_mem _ (hxV' i)) (haV i)
          j hj0 hjl).1,(actual_radical_inverse_row_column _ (hxV' i) j hj0 hjl).1,
          zero_power ι eps (u i) (phi i) (s i) _ j hz,hz,neg_zero,add_zero]
      simp only [hv,Finset.sum_const_zero,if_neg hj]
end NikolovSegal.PartIIUnitaryRadicalBoundaryFieldProduct
