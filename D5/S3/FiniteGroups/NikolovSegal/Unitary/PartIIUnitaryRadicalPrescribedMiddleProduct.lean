/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedMiddleProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedMiddleProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalDiagonalNormalization
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalMiddleFieldProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "vMiddle%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalMiddleFieldProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalMiddleFieldProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual V middle kernel {id} not found"
open Lean Elab Term in
elab "vNormalize%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalDiagonalNormalization"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalDiagonalNormalization"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual V diagonal kernel {id} not found"
/-! Genuine D Phi middle branch of Proposition6.7, PartII pp262–263.
The diagonal similitude is normalized by actual ambient SU inner
matrices. Its determinant is absorbed at a boundary pair, not discarded.
Original positive divisor powers and correction-before-target order
are retained. This is the middle quotient, not whole V coverage. -/
namespace NikolovSegal.PartIIUnitaryRadicalPrescribedMiddleProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus PartIIFieldMaps UnitaryField
open PartIIUnitaryRadicalTraceCoordinates PartIIUnitaryRadicalMiddleFieldProduct
open PartIIUnitaryRadicalDiagonalNormalization
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}
private def beta (ι : RingAut F) (u v : Fˣ) (phi : RingAut F) :
    MulAut (SpecialLinearGroup (Fin (k+4)) F) :=
  PartIIProposition6_5.diagonalFieldGraph ((vNormalize% innerWeights) ι u v) phi false
private theorem beta_radical (ι : RingAut F) (u v : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (hg : InRadical g) :
    InRadical ((beta ι u v phi^s) g) := by
  induction s with
  | zero => exact hg
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply]
    exact PartIIRadicalActions.actual_diagonal_field_graph_radical_mem _ _ _ _ ih
private theorem diagonal_steinberg (ι : RingAut F) (w : Fin (k+4) → Fˣ)
    (hw : ∀ i, ι (w i:F)*(w i.rev:F)=1) (g : SpecialLinearGroup (Fin (k+4)) F) :
    steinberg ι ((unitOdd% diagonalAut) w g)=(unitOdd% diagonalAut) w (steinberg ι g) := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,← map_inv,unitOdd% diagonal_entry,unitOdd% diagonal_entry,steinberg_entry]
  have hi : ι (w i.rev:F)=(w i:F)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [Fin.rev_rev] using hw i.rev)
  have hj : ι (w j.rev:F)=(w j:F)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [Fin.rev_rev] using hw j.rev)
  simp only [Units.val_inv_eq_inv_val,map_mul,map_inv₀,hi,hj,inv_inv]
  ring
private theorem beta_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (u v : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (hg : steinberg ι g=g) :
    steinberg ι ((beta ι u v phi^s) g)=(beta ι u v phi^s) g := by
  induction s with
  | zero => exact hg
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply]
    change steinberg ι ((unitOdd% diagonalAut) ((vNormalize% innerWeights) ι u v)
      (fieldAut phi ((beta ι u v phi^s) g)))=_
    rw [diagonal_steinberg ι _ ((vNormalize% innerWeights_unitary) ι hinv u v),
      (vMiddle% field_unitary) ι phi hinv hne _ ih]
    rfl
private theorem innerWeights_middle (ι : RingAut F) (u v : Fˣ) (j : Fin (k+4))
    (hj : Middle j) : (vNormalize% innerWeights) ι u v j=1 := by
  have hja : 2≤j.val := hj.1
  have hjb : j.val+2<k+4 := hj.2
  have hi : j.val-2<k := by omega
  let t : Fin k := ⟨j.val-2,hi⟩
  have he : j=(PartIICentralLevi.middle (PartIICentralLevi.middle t)) := by
    apply Fin.ext; simp only [PartIICentralLevi.middle,Fin.val_succ,Fin.val_castSucc,t]; omega
  rw [he]
  change (unitaryCentral% extendWeights) ι
    ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1) v) u
    (PartIICentralLevi.middle (PartIICentralLevi.middle t))=1
  rw [unitaryCentral% extend_middle,unitaryCentral% extend_middle]
private theorem beta_row (ι : RingAut F) (u v : Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+4)) F) (j : Fin (k+4)) (hj : Middle j) :
    beta ι u v phi g first j=(u:F)*phi (g first j) := by
  have h0 : (vNormalize% innerWeights) ι u v (first:Fin (k+4))=u := rfl
  change (unitOdd% diagonalAut) ((vNormalize% innerWeights) ι u v) (fieldAut phi g) first j=_
  rw [unitOdd% diagonal_entry,h0,innerWeights_middle ι u v j hj]
  simp
  rfl
private theorem beta_row_power (ι : RingAut F) (u v : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (j : Fin (k+4)) (hj : Middle j) :
    (beta ι u v phi^s) g first j=orbitProduct phi s (u:F)*(phi^s) (g first j) := by
  induction s with
  | zero => simp [orbitProduct]
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,beta_row ι u v phi _ j hj,ih,
      rootFieldKernel% orbitProduct_succ,map_mul,pow_succ',RingAut.mul_apply]
    ring
private theorem beta_value (ι : RingAut F) (u v : Fˣ) (phi : RingAut F)
    (s : ℕ) (g : SpecialLinearGroup (Fin (k+4)) F) (hg : InRadical g)
    (j : Fin (k+4)) (hj : Middle j) :
    (g⁻¹*(beta ι u v phi^s) g) first j=fieldValue phi 1 s 1 (u:F) (g first j) := by
  have hi := (vMiddle% middle_interior) j hj
  rw [(actual_radical_product_row_column _ _ (actual_radical_inverse_mem g hg)
      (beta_radical ι u v phi s g hg) j hi.1 hi.2).1,
    (actual_radical_inverse_row_column g hg j hi.1 hi.2).1,beta_row_power ι u v phi s g j hj]
  simp only [fieldValue,one_mul,pow_one]; ring

/-- Actual prescribed diagonal-SIMILITUDE/field V* middle PRODUCT.
ONE genuine determinant-one unitary inner correction is constructed
before EVERY target. No normalization or commutator-coverage premise
is retained. Boundary pairs/corner remain subsequent stages. -/
theorem actual_unitary_radical_prescribed_middle_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : q*(q+1)<M) (hF : (q+1)^q<Fintype.card F)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (a : Fin M → Fin (k+4) → Fˣ) (c : Fin M → (fixedField ι)ˣ)
    (ha : ∀ i j, ι (a i j:F)*(a i j.rev:F)=((c i:fixedField ι):F))
    (phi : Fin M → RingAut F) (s : Fin M → ℕ) (hs : ∀ j, 0<s j ∧ s j∣q) :
    ∃ h : Fin M → SpecialLinearGroup (Fin (k+4)) F,
      (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
      ∀ b : SpecialLinearGroup (Fin (k+4)) F, InRadical b → steinberg ι b=b →
        ∃ x : Fin M → SpecialLinearGroup (Fin (k+4)) F,
          (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
          let P := orderedProduct (fun j => (x j)⁻¹*
            ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))
          InRadical P ∧ steinberg ι P=P ∧ ∀ j : Fin (k+4), Middle j → P first j=b first j := by
  classical
  obtain ⟨lambda,hlambda,hcover⟩ := lemma7_1 (c:=1) hq (by simpa using hM) (by simpa using hF)
    phi (fun _ => 1) s (fun _ => 1) (fun _ => one_ne_zero) hs (fun _ => ⟨by decide,by decide⟩)
  let u := fun j => Units.mk0 (lambda j) (hlambda j)
  have hn := fun j => actual_unitary_radical_middle_diagonal_inner ι hinv hne (a j) (c j) (ha j) (u j)
  choose h v hdiagonal hhu hact using hn
  have he : ∀ j, MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false=
      beta ι (u j) (v j) (phi j) := by
    intro j; apply MulEquiv.ext; intro g
    exact hact j (fieldAut (phi j) g)
  refine ⟨h,hdiagonal,hhu,?_⟩
  intro b hb hbu
  have ht : ∀ j : {j : Fin (k+4) // Middle j}, ∃ t : Fin M → F,
      (∑ i, fieldValue (phi i) 1 (s i) 1 (lambda i) (t i))=b first j.val := fun j => hcover _
  choose t ht using ht
  let r : Fin M → Fin (k+4) → F := fun i j => if hj : Middle j then t ⟨j,hj⟩ i else 0
  have hr : ∀ i, EndpointZero (r i) := by
    intro i; constructor <;> simp [r,Middle,first,last]
  have hl := fun i => actual_unitary_radical_row_lift ι hinv hne (r i) (hr i)
  choose col hc z hcol htrace hxV hxU using hl
  let x := fun i => radical (r i) (col i) (hr i) (hc i) (z i)
  let values := fun i => (x i)⁻¹*(beta ι (u i) (v i) (phi i)^(s i)) (x i)
  have hvV : ∀ i, InRadical (values i) := fun i => actual_radical_product_mem _ _
    (actual_radical_inverse_mem _ (hxV i)) (beta_radical ι (u i) (v i) (phi i) _ _ (hxV i))
  have hvU : ∀ i, steinberg ι (values i)=values i := by
    intro i
    change steinberg ι ((x i)⁻¹*(beta ι (u i) (v i) (phi i)^(s i)) (x i))=_
    rw [map_mul,map_inv,hxU i,beta_unitary ι hinv hne _ _ _ _ _ (hxU i)]
  have hP := (radicalMiddle% ordered_radical) values hvV
  refine ⟨x,fun i => ⟨hxV i,hxU i⟩,?_,?_,?_⟩
  · simpa only [he] using hP.1
  · simp only [he]
    change steinberg ι (orderedProduct values)=orderedProduct values
    simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,hvU]
  · intro j hj
    simp only [he]
    change orderedProduct values first j=b first j
    rw [(hP.2 j ((vMiddle% middle_interior) j hj).1 ((vMiddle% middle_interior) j hj).2).1]
    have hv : ∀ i, values i first j=fieldValue (phi i) 1 (s i) 1 (lambda i) (t ⟨j,hj⟩ i) := by
      intro i
      rw [beta_value ι (u i) (v i) (phi i) _ _ (hxV i) j hj,
        actual_radical_row _ _ _ _ _ j ((vMiddle% middle_interior) j hj).1 ((vMiddle% middle_interior) j hj).2]
      simp only [r,dif_pos hj,u,Units.val_mk0]
    simp only [hv]
    exact ht ⟨j,hj⟩
end NikolovSegal.PartIIUnitaryRadicalPrescribedMiddleProduct
