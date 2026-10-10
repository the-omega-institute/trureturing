/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryPrescribedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryPrescribedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalBoundaryDiagonalNormalization
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalBoundaryFieldProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "vBoundary%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalBoundaryFieldProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalBoundaryFieldProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual boundary V kernel {id} not found"
open Lean Elab Term in
elab "vBoundaryNormalize%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalBoundaryDiagonalNormalization"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalBoundaryDiagonalNormalization"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual boundary determinant kernel {id} not found"
/-! Actual prescribed D Phi exceptional-pair V* product, PartII
pp262–263. A THIRD reflected pair absorbs the determinant before
all targets. Exact whole supported-matrix action equality, including
the corner, transports the already PROVED field product. -/
namespace NikolovSegal.PartIIUnitaryRadicalBoundaryPrescribedProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus UnitaryField
open PartIIUnitaryRadicalBoundaryFieldProduct PartIIUnitaryRadicalBoundaryDiagonalNormalization
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}
private def Supported (ι : RingAut F) (eps : Bool) (g : SpecialLinearGroup (Fin (k+6)) F) : Prop :=
  InRadical g ∧ steinberg ι g=g ∧
    ∀ j, j≠first → j≠last → j≠axis eps → g first j=0
private theorem diagonal_on_supported (ι : RingAut F) (hinv : Function.Involutive ι)
    (eps : Bool) (w0 w1 : Fin (k+6) → Fˣ)
    (hw0 : ∀ i, ι (w0 i:F)*(w0 i.rev:F)=1)
    (hw1 : ∀ i, ι (w1 i:F)*(w1 i.rev:F)=1)
    (hfirst : w1 first=w0 first) (hlast : w1 last=w0 last) (haxis : w1 (axis eps)=w0 (axis eps))
    (g : SpecialLinearGroup (Fin (k+6)) F) (hg : Supported ι eps g) :
    (unitOdd% diagonalAut) w1 g=(unitOdd% diagonalAut) w0 g := by
  have hmate : w1 (axis eps).rev=w0 (axis eps).rev := by
    apply Units.ext
    apply mul_left_cancel₀ (show ι (w0 (axis eps):F)≠0 from (map_ne_zero ι).mpr (Units.ne_zero _))
    calc
      _ = 1 := by rw [← haxis]; exact hw1 (axis eps)
      _ = _ := (hw0 (axis eps)).symm
  apply SpecialLinearGroup.ext
  intro i j
  rw [unitOdd% diagonal_entry,unitOdd% diagonal_entry]
  simp only [Units.val_inv_eq_inv_val]
  by_cases hij : i=j
  · subst j
    field_simp
  · by_cases hi : i=first
    · subst i
      by_cases hjl : j=last
      · subst j; rw [hfirst,hlast]
      · by_cases hja : j=axis eps
        · subst j; rw [hfirst,haxis]
        · have hj0 : j≠first := Ne.symm hij
          rw [hg.2.2 j hj0 hjl hja]
          simp
    · by_cases hj : j=last
      · subst j
        by_cases hia : i=(axis eps).rev
        · subst i; rw [hmate,hlast]
        · have hr0 : i.rev≠first := by intro he; apply hij; have hh := congrArg Fin.rev he; simpa [first,last] using hh
          have hrl : i.rev≠last := by intro he; apply hi; have hh := congrArg Fin.rev he; simpa [first,last] using hh
          have hra : i.rev≠axis eps := by intro he; apply hia; have hh := congrArg Fin.rev he; simpa using hh
          have hh := (vMiddle% unitary_reflected_column) ι hinv g hg.1 hg.2.1 i.rev hr0 hrl
          have hz : g i last=0 := by simpa only [Fin.rev_rev,hg.2.2 i.rev hr0 hrl hra,map_zero,neg_zero] using hh
          rw [hz]; simp
      · rw [hg.1.2 i j hi hj]
        simp [Matrix.one_apply,hij]
private theorem field_supported (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (eps : Bool) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+6)) F) (hg : Supported ι eps g) :
    Supported ι eps (fieldAut phi g) := by
  have hf : InRadical (fieldAut phi g) := by
    refine ⟨(unitOdd% field_depth) phi 1 g hg.1.1,?_⟩
    intro i j hi hj
    change phi (g i j)=(1:Matrix (Fin (k+6)) (Fin (k+6)) F) i j
    rw [hg.1.2 i j hi hj]
    simp [Matrix.one_apply]
  refine ⟨hf,(vMiddle% field_unitary) ι phi hinv hne g hg.2.1,?_⟩
  intro j hj0 hjl hja
  change phi (g first j)=0
  rw [hg.2.2 j hj0 hjl hja,map_zero]
private theorem field_action_supported (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (eps : Bool) (u : Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (k+6)) F) (hg : Supported ι eps g) :
    Supported ι eps ((vBoundary% action) ι eps u phi g) := by
  refine ⟨?_,?_,?_⟩
  · change InRadical (((vPrescribed% beta) ι u ((vBoundary% secondWeight) ι eps u) phi) g)
    simpa only [pow_one] using (vPrescribed% beta_radical) ι u ((vBoundary% secondWeight) ι eps u) phi 1 g hg.1
  · change steinberg ι (((vPrescribed% beta) ι u ((vBoundary% secondWeight) ι eps u) phi) g)=
      ((vPrescribed% beta) ι u ((vBoundary% secondWeight) ι eps u) phi) g
    simpa only [pow_one] using (vPrescribed% beta_unitary) ι hinv hne u ((vBoundary% secondWeight) ι eps u) phi 1 g hg.2.1
  · intro j hj0 hjl hja
    rw [vBoundary% row_step,hg.2.2 j hj0 hjl hja,map_zero,mul_zero]
private theorem extend_last {n : ℕ} (ι : RingAut F) (eta : Fin n → Fˣ) (u : Fˣ) :
    (unitaryCentral% extendWeights) ι eta u (Fin.last (n+1))=(involutionUnit ι u)⁻¹ := by
  change (Fin.cons u (Fin.snoc eta (involutionUnit ι u)⁻¹) : Fin (n+2) → Fˣ) (Fin.last (n+1))=_
  rw [Fin.cons_last,Fin.snoc_last]
private theorem two_pair_entries {n : ℕ} (ι : RingAut F) (eta : Fin n → Fˣ) (u d : Fˣ) :
    let w := (unitaryCentral% extendWeights) ι ((unitaryCentral% extendWeights) ι eta d) u
    w first=u ∧ w last=(involutionUnit ι u)⁻¹ ∧ w 1=d ∧ w (1:Fin (n+4)).rev=(involutionUnit ι d)⁻¹ := by
  refine ⟨rfl,extend_last ι _ u,?_,?_⟩
  · change (unitaryCentral% extendWeights) ι ((unitaryCentral% extendWeights) ι eta d) u
      (PartIICentralLevi.middle (0:Fin (n+2)))=d
    rw [unitaryCentral% extend_middle]
    rfl
  · have he : (1:Fin (n+4)).rev=PartIICentralLevi.middle (Fin.last (n+1)) := by
      apply Fin.ext
      simp only [Fin.val_rev,PartIICentralLevi.middle,Fin.val_last,Fin.val_succ,Fin.val_castSucc]
      have h1 : (1:Fin (n+4)).val=1 := by simp
      rw [h1]
      omega
    change (unitaryCentral% extendWeights) ι ((unitaryCentral% extendWeights) ι eta d) u (1:Fin (n+4)).rev=_
    rw [he,unitaryCentral% extend_middle]
    exact extend_last ι eta d
private theorem boundary_weights_match (ι : RingAut F) (hinv : Function.Involutive ι)
    (eps : Bool) (u w : Fˣ) :
    let B : Fin (k+6) → Fˣ := (vBoundaryNormalize% weights) ι u ((vBoundary% secondWeight) ι eps u) w
    let A := ((vBoundary% weights) ι eps u : Fin (k+6) → Fˣ)
    B first=A first ∧ B last=A last ∧ B (axis eps)=A (axis eps) := by
  let d := (vBoundary% secondWeight) ι eps u
  have hB := two_pair_entries ι ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1) w) u d
  have hA := two_pair_entries ι (fun _ : Fin (k+2) => 1) u d
  refine ⟨hB.1.trans hA.1.symm,hB.2.1.trans hA.2.1.symm,?_⟩
  cases eps
  · exact hB.2.2.1.trans hA.2.2.1.symm
  · have he : (axis (k:=k+2) true)=(1:Fin (k+6)).rev := by
      apply Fin.ext; simp [axis,Fin.val_rev]
    rw [he]
    exact hB.2.2.2.trans hA.2.2.2.symm

/-- True arbitrary prescribed diagonal-SIMILITUDE/field exceptional
pair PRODUCT. The original positive s|q scalar supplier is consumed;
all targets use the SAME pre-target actual unitary h, and witnesses
have genuine axis support with corners retained. -/
theorem actual_unitary_radical_boundary_prescribed_product [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : q*(2*q+1)<M) (hF : 2*(2*q+1)^q<Fintype.card F)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (eps : Bool) (a : Fin M → Fin (k+6) → Fˣ) (c : Fin M → (fixedField ι)ˣ)
    (ha : ∀ i j, ι (a i j:F)*(a i j.rev:F)=((c i:fixedField ι):F))
    (phi : Fin M → RingAut F) (s : Fin M → ℕ) (hs : ∀ j, 0<s j ∧ s j∣q) :
    ∃ h : Fin M → SpecialLinearGroup (Fin (k+6)) F,
      (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
      ∀ b : SpecialLinearGroup (Fin (k+6)) F, InRadical b → steinberg ι b=b →
        ∃ x : Fin M → SpecialLinearGroup (Fin (k+6)) F,
          (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
          let P := orderedProduct (fun j => (x j)⁻¹*
            ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))
          InRadical P ∧ steinberg ι P=P ∧
            ∀ j : Fin (k+6), j≠first → j≠last →
              P first j=if j=axis eps then b first j else 0 := by
  classical
  obtain ⟨u,hF0,hehF0,hhF0,hcover⟩ := actual_unitary_radical_boundary_field_product (k:=k+2)
    hq hM hF ι hinv hne eps phi s hs
  have hn := fun j => actual_unitary_radical_boundary_diagonal_inner ι hinv hne
    (a j) (c j) (ha j) (u j) ((vBoundary% secondWeight) ι eps (u j))
  choose h w hdiagonal hhu hact using hn
  let betaD := fun j => MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false
  let betaF : Fin M → MulAut (SpecialLinearGroup (Fin (k+6)) F) := fun j => (vBoundary% action) ι eps (u j) (phi j)
  have hpow : ∀ j t g, Supported ι eps g → (betaD j^t) g=(betaF j^t) g := by
    intro j t
    have hstep : ∀ g, Supported ι eps g → betaD j g=betaF j g := by
      intro g hg
      change (MulAut.conj (h j)) ((unitOdd% diagonalAut) (a j) (fieldAut (phi j) g))=_
      rw [hact j]
      exact diagonal_on_supported ι hinv eps _ _
        ((vNormalize% innerWeights_unitary) ι hinv _ _)
        ((vBoundaryNormalize% weights_unitary) ι hinv _ _ _)
        (boundary_weights_match ι hinv eps (u j) (w j)).1
        (boundary_weights_match ι hinv eps (u j) (w j)).2.1
        (boundary_weights_match ι hinv eps (u j) (w j)).2.2
        _ (field_supported ι hinv hne eps _ g hg)
    have hkeep : ∀ t g, Supported ι eps g → Supported ι eps ((betaF j^t) g) := by
      intro t g hg
      induction t with
      | zero => exact hg
      | succ t ih => rw [pow_succ',MulAut.mul_apply]; exact field_action_supported ι hinv hne eps _ _ _ ih
    intro g hg
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [pow_succ',pow_succ',MulAut.mul_apply,MulAut.mul_apply,ih]
      exact hstep _ (hkeep t g hg)
  refine ⟨h,hdiagonal,hhu,?_⟩
  intro b hb hbu
  obtain ⟨x,hx,hxsupport,hPV,hPU,hmatch⟩ := hcover b hb hbu
  have hEF : ∀ j, MulAut.conj (hF0 j)*fieldAut (n:=k+6) (phi j)=betaF j := by
    intro j
    rw [hehF0 j,radicalTorus% diagonalSL_action]
    rfl
  have he : ∀ j, ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j)=
      ((MulAut.conj (hF0 j)*fieldAut (n:=k+6) (phi j))^(s j)) (x j) := by
    intro j
    rw [hEF]
    exact hpow j (s j) (x j) ⟨(hx j).1,(hx j).2,hxsupport j⟩
  refine ⟨x,hx,?_,?_,?_⟩
  · simpa only [he] using hPV
  · simpa only [he] using hPU
  · simpa only [he] using hmatch
end NikolovSegal.PartIIUnitaryRadicalBoundaryPrescribedProduct
