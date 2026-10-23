/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalMiddleFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalMiddleFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalTraceCoordinates
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "unitaryRadicalSupply%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalSupply"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalSupply"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual accepted unitary radical torus kernel {id} not found"
open Lean Elab Term in
elab "radicalMiddle%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIRadicalMiddleProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalMiddleProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual accepted ordered radical kernel {id} not found"
/-! PartII pp262–263 actual prescribed-field V* middle quotient. The
actual unitary row lifts and determinant-one four-entry unitary torus
are consumed. No squaring of powers, arbitrary SL witness, discarded
corner or supplied quotient/whole-block coverage is used. -/
namespace NikolovSegal.PartIIUnitaryRadicalMiddleFieldProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus PartIIFieldMaps UnitaryField
open PartIIUnitaryRadicalTraceCoordinates
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}

def Middle (j : Fin (k+4)) : Prop := 2≤j.val ∧ j.val+2<k+4
private theorem middle_interior (j : Fin (k+4)) (hj : Middle j) : j≠first ∧ j≠last := by
  have h0 : j.val≠0 := by have hh := hj.1; omega
  have hl : j.val≠k+3 := by have hh := hj.2; omega
  constructor
  · intro hh; exact h0 (congrArg Fin.val hh)
  · intro hh; exact hl (congrArg Fin.val hh)
private theorem field_unitary (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : SpecialLinearGroup (Fin (k+4)) F)
    (hg : steinberg ι g=g) : steinberg ι (fieldAut phi g)=fieldAut phi g := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,← map_inv]
  change ι (phi (g⁻¹ j.rev i.rev))=phi (g i j)
  have he := congrArg (fun a : SpecialLinearGroup (Fin (k+4)) F => a i j) hg
  rw [steinberg_entry] at he
  rw [← he,involution_eq_pow ι hinv hne,involution_eq_pow ι hinv hne,map_pow]

private def torus (ι : RingAut F) (u : Fˣ) : SpecialLinearGroup (Fin (k+4)) F :=
  (radicalTorus% diagonalSL) ((unitaryRadicalSupply% weights) ι u)
    ((unitaryRadicalSupply% weights_product) ι u)
private theorem torus_unitary (ι : RingAut F) (hinv : Function.Involutive ι) (u : Fˣ) :
    steinberg ι (torus (k:=k) ι u)=torus ι u :=
  (unitaryTorus% diagonal_fixed) ι _ _ ((unitaryRadicalSupply% weights_unitary) ι hinv u)
private def action (ι : RingAut F) (u : Fˣ) (phi : RingAut F) :
    MulAut (SpecialLinearGroup (Fin (k+4)) F) := MulAut.conj (torus ι u)*fieldAut phi
private theorem action_radical (ι : RingAut F) (u : Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+4)) F) (hg : InRadical g) : InRadical (action ι u phi g) := by
  have he : action (k:=k) ι u phi=PartIIProposition6_5.diagonalFieldGraph
      ((unitaryRadicalSupply% weights) ι u) phi false := by
    rw [action,torus,radicalTorus% diagonalSL_action]
    rfl
  rw [he]
  exact PartIIRadicalActions.actual_diagonal_field_graph_radical_mem _ _ _ g hg
private theorem action_power_radical (ι : RingAut F) (u : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (hg : InRadical g) :
    InRadical ((action ι u phi^s) g) := by
  induction s with
  | zero => exact hg
  | succ s ih => rw [pow_succ',MulAut.mul_apply]; exact action_radical ι u phi _ ih
private theorem action_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (u : Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+4)) F) (hg : steinberg ι g=g) :
    steinberg ι (action ι u phi g)=action ι u phi g := by
  rw [action,MulAut.mul_apply,MulAut.conj_apply]
  rw [map_mul,map_mul,map_inv,torus_unitary ι hinv,field_unitary ι phi hinv hne g hg]
private theorem action_power_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (u : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (hg : steinberg ι g=g) :
    steinberg ι ((action ι u phi^s) g)=(action ι u phi^s) g := by
  induction s with
  | zero => exact hg
  | succ s ih => rw [pow_succ',MulAut.mul_apply]; exact action_unitary ι hinv hne u phi _ ih
private theorem middle_step (ι : RingAut F) (u : Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+4)) F) (j : Fin (k+4)) (hj : Middle j) :
    action ι u phi g first j=(u:F)*phi (g first j) := by
  have h0 : ((unitaryRadicalSupply% weights) ι u (first:Fin (k+4)))=u := by
    rw [unitaryRadicalSupply% weights_entry]; simp only [first,Fin.val_zero,ite_true]
  have hjw : ((unitaryRadicalSupply% weights) ι u j)=1 := by
    rw [unitaryRadicalSupply% weights_entry]
    have hh := hj.1; have hh' := hj.2
    simp only [show j.val≠0 by omega,show j.val≠1 by omega,
      show j.val≠k+2 by omega,show j.val≠k+3 by omega,ite_false]
  rw [action,MulAut.mul_apply,torus,radicalTorus% diagonalSL_action,unitOdd% diagonal_entry,h0,hjw]
  simp
  rfl
private theorem middle_power (ι : RingAut F) (u : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (j : Fin (k+4)) (hj : Middle j) :
    (action ι u phi^s) g first j=orbitProduct phi s (u:F)*(phi^s) (g first j) := by
  induction s with
  | zero => simp [orbitProduct]
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,middle_step ι u phi _ j hj,ih,
      rootFieldKernel% orbitProduct_succ,map_mul,pow_succ',RingAut.mul_apply]
    ring
private theorem middle_value (ι : RingAut F) (u : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (hg : InRadical g)
    (j : Fin (k+4)) (hj : Middle j) :
    (g⁻¹*(action ι u phi^s) g) first j=fieldValue phi 1 s 1 (u:F) (g first j) := by
  have hi := middle_interior j hj
  rw [(actual_radical_product_row_column _ _ (actual_radical_inverse_mem g hg)
      (action_power_radical ι u phi s g hg) j hi.1 hi.2).1,
    (actual_radical_inverse_row_column g hg j hi.1 hi.2).1,middle_power ι u phi s g j hj]
  simp only [fieldValue,one_mul,pow_one]; ring

/-- Actual uniform original-s-power FIELD-action middle quotient
PRODUCT. One determinant-one UNITARY h precedes ALL radical targets;
witnesses are in V*, and the full corner is retained in P. The two
boundary root pairs and central corner coverage remain later stages. -/
theorem actual_unitary_radical_middle_field_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : q*(q+1)<M) (hF : (q+1)^q<Fintype.card F)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (phi : Fin M → RingAut F) (s : Fin M → ℕ) (hs : ∀ j, 0<s j ∧ s j∣q) :
    ∃ h : Fin M → SpecialLinearGroup (Fin (k+4)) F,
      (∀ j, steinberg ι (h j)=h j) ∧
      ∀ b : SpecialLinearGroup (Fin (k+4)) F, InRadical b → steinberg ι b=b →
        ∃ x : Fin M → SpecialLinearGroup (Fin (k+4)) F,
          (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
          let P := NikolovSegal.orderedProduct (fun j => (x j)⁻¹*
            ((MulAut.conj (h j)*fieldAut (n:=k+4) (phi j))^(s j)) (x j))
          InRadical P ∧ steinberg ι P=P ∧ ∀ j : Fin (k+4), Middle j → P first j=b first j := by
  classical
  obtain ⟨a,ha,hcover⟩ := lemma7_1 (c:=1) hq (by simpa using hM) (by simpa using hF)
    phi (fun _ => 1) s (fun _ => 1) (fun _ => one_ne_zero) hs (fun _ => ⟨by decide,by decide⟩)
  let u := fun j => Units.mk0 (a j) (ha j)
  let h := fun j => torus (k:=k) ι (u j)
  refine ⟨h,fun j => torus_unitary ι hinv _,?_⟩
  intro b hb hbu
  have ht : ∀ j : {j : Fin (k+4) // Middle j}, ∃ t : Fin M → F,
      (∑ i, fieldValue (phi i) 1 (s i) 1 (a i) (t i))=b first j.val := fun j => hcover _
  choose t ht using ht
  let r : Fin M → Fin (k+4) → F := fun i j => if hj : Middle j then t ⟨j,hj⟩ i else 0
  have hr : ∀ i, EndpointZero (r i) := by
    intro i; constructor <;> simp [r,Middle,first,last]
  have hl := fun i => actual_unitary_radical_row_lift ι hinv hne (r i) (hr i)
  choose c hc z hcol htrace hxV hxU using hl
  let x := fun i => radical (r i) (c i) (hr i) (hc i) (z i)
  let v := fun i => (x i)⁻¹*(action ι (u i) (phi i)^(s i)) (x i)
  have hvV : ∀ i, InRadical (v i) := fun i => actual_radical_product_mem _ _
    (actual_radical_inverse_mem _ (hxV i)) (action_power_radical ι (u i) (phi i) _ _ (hxV i))
  have hvU : ∀ i, steinberg ι (v i)=v i := by
    intro i
    change steinberg ι ((x i)⁻¹*(action ι (u i) (phi i)^(s i)) (x i))=_
    rw [map_mul,map_inv,hxU i,action_power_unitary ι hinv hne _ _ _ _ (hxU i)]
  have hP := (radicalMiddle% ordered_radical) v hvV
  refine ⟨x,fun i => ⟨hxV i,hxU i⟩,hP.1,?_,?_⟩
  · change steinberg ι (NikolovSegal.orderedProduct v)=NikolovSegal.orderedProduct v
    simp only [NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,hvU]
  · intro j hj
    have hi := middle_interior j hj
    change NikolovSegal.orderedProduct v first j=b first j
    rw [(hP.2 j hi.1 hi.2).1]
    have hv : ∀ i, v i first j=fieldValue (phi i) 1 (s i) 1 (a i) (t ⟨j,hj⟩ i) := by
      intro i
      rw [middle_value ι (u i) (phi i) _ _ (hxV i) j hj,
        actual_radical_row _ _ _ _ _ j hi.1 hi.2]
      simp only [r,dif_pos hj,u,Units.val_mk0]
    simp only [hv]
    exact ht ⟨j,hj⟩
private theorem unitary_reflected_column (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin (k+4)) F) (hg : InRadical g) (hgu : steinberg ι g=g)
    (j : Fin (k+4)) (hj0 : j≠first) (hjl : j≠last) :
    g j.rev last= -ι (g first j) := by
  have hr0 : j.rev≠first := by
    intro he; apply hjl; have hh := congrArg Fin.rev he; simpa [first,last] using hh
  have hrl : j.rev≠last := by
    intro he; apply hj0; have hh := congrArg Fin.rev he; simpa [first,last] using hh
  have hfirst : (first:Fin (k+4)).rev=last := by apply Fin.ext; simp [first,last]
  have he := congrArg (fun a : SpecialLinearGroup (Fin (k+4)) F => a first j) hgu
  rw [steinberg_entry,hfirst,(actual_radical_inverse_row_column g hg j.rev hr0 hrl).2] at he
  have hh := congrArg ι he
  simp only [map_neg,hinv (g j.rev last)] at hh
  exact neg_eq_iff_eq_neg.mp hh

/-- The ACTUAL ordered residual after the middle V* PRODUCT: all
middle row AND reflected column entries vanish. It stays unitary and
in V; both exceptional root pairs and the corner remain unconstrained. -/
theorem actual_unitary_middle_residual (ι : RingAut F) (hinv : Function.Involutive ι)
    (P b : SpecialLinearGroup (Fin (k+4)) F)
    (hP : InRadical P) (hPu : steinberg ι P=P) (hb : InRadical b) (hbu : steinberg ι b=b)
    (hmatch : ∀ j, Middle j → P first j=b first j) :
    InRadical (P⁻¹*b) ∧ steinberg ι (P⁻¹*b)=P⁻¹*b ∧
      ∀ j, Middle j → (P⁻¹*b) first j=0 ∧ (P⁻¹*b) j.rev last=0 := by
  have hm : ∀ j : Fin (k+4), PartIIRadicalMiddleProduct.Middle j →
      P first j=b first j ∧ P j.rev last=b j.rev last := by
    intro j hj
    have hj' : Middle j := hj
    have hi := middle_interior j hj'
    refine ⟨hmatch j hj',?_⟩
    rw [unitary_reflected_column ι hinv P hP hPu j hi.1 hi.2,
      unitary_reflected_column ι hinv b hb hbu j hi.1 hi.2,hmatch j hj']
  have hR := PartIIRadicalMiddleProduct.actual_middle_residual P b hP hb hm
  exact ⟨hR.1,by rw [map_mul,map_inv,hPu,hbu],fun j hj => hR.2 j hj⟩
end NikolovSegal.PartIIUnitaryRadicalMiddleFieldProduct
