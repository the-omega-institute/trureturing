/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalCornerPrescribedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalCornerPrescribedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalCornerFieldProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Lean Elab Term in
elab "vCorner%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryRadicalCornerFieldProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalCornerFieldProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual V corner kernel {id} not found"
/-! PartII Proposition6.7 pp262–263 actual prescribed D Phi trace-zero
corner product. The determinant absorber sits off the corner. Genuine
fixed-field coefficients and one actual SU inner correction precede
all targets; the field scalar supplier is PROVED, not assumed. -/
namespace NikolovSegal.PartIIUnitaryRadicalCornerPrescribedProduct
open Matrix PartIIUnitriangularActions PartIIRadicalCoordinates PartIIUnitaryUpperTorus UnitaryField
open PartIIUnitaryRadicalDiagonalNormalization PartIIUnitaryRadicalCornerFieldProduct
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}
private theorem inner_corner_action (ι : RingAut F) (u : (fixedField ι)ˣ)
    (v : Fˣ) (phi : RingAut F) (z : F) :
    PartIIProposition6_5.diagonalFieldGraph ((vNormalize% innerWeights) ι
      (Units.map (fixedField ι).subtype u) v) phi false ((vCorner% corner) z : SpecialLinearGroup (Fin (k+4)) F)=
      (vCorner% corner) ((((u:fixedField ι):F)^2)*phi z) := by
  rw [vCorner% corner_diagonal_field]
  have h0 : (vNormalize% innerWeights) ι (Units.map (fixedField ι).subtype u) v
      (first:Fin (k+4))=Units.map (fixedField ι).subtype u := rfl
  have hl : (vNormalize% innerWeights) ι (Units.map (fixedField ι).subtype u) v
      (last:Fin (k+4))=(involutionUnit ι (Units.map (fixedField ι).subtype u))⁻¹ := by
    change (Fin.cons (Units.map (fixedField ι).subtype u)
      (Fin.snoc ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1) v)
        (involutionUnit ι (Units.map (fixedField ι).subtype u))⁻¹) : Fin (k+4) → Fˣ) (Fin.last (k+3))=_
    have he : (Fin.last (k+3):Fin (k+4))=(Fin.last (k+2)).succ := by apply Fin.ext; rfl
    rw [he,Fin.cons_succ,Fin.snoc_last]
  rw [h0,hl]
  congr 1
  simp only [Units.val_inv_eq_inv_val,inv_inv,involutionUnit_val]
  change ((u:fixedField ι):F)*ι ((u:fixedField ι):F)*phi z=_
  rw [(mem_fixedField ι _).mp (u:fixedField ι).prop]
  ring

/-- Actual arbitrary prescribed diagonal-SIMILITUDE/field central V*
corner PRODUCT. ONE genuine SU inner tuple precedes ALL trace-zero
targets; original positive s|q and actual central witnesses retained. -/
theorem actual_unitary_radical_corner_prescribed_product {q : ℕ} (hq : 0<q)
    (hM : q*(2*q+1)<M) (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (a : Fin M → Fin (k+4) → Fˣ) (c : Fin M → (fixedField ι)ˣ)
    (ha : ∀ i j, ι (a i j:F)*(a i j.rev:F)=((c i:fixedField ι):F))
    (phi : Fin M → RingAut F) (s : Fin M → ℕ) (hs : ∀ j, 0<s j ∧ s j∣q) :
    ∃ h : Fin M → SpecialLinearGroup (Fin (k+4)) F,
      (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
      ∀ target : F, target+ι target=0 →
        ∃ x : Fin M → SpecialLinearGroup (Fin (k+4)) F,
          (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
          orderedProduct (fun j => (x j)⁻¹*
            ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=
              (vCorner% corner) target := by
  classical
  obtain ⟨u,hF0,hehF0,hhF0,hcover⟩ := actual_unitary_radical_corner_field_product (k:=k)
    hq hM ι hinv hne hK phi s hs
  have hn := fun j => actual_unitary_radical_middle_diagonal_inner ι hinv hne
    (a j) (c j) (ha j) (Units.map (fixedField ι).subtype (u j))
  choose h v hdiagonal hhu hact using hn
  let betaD := fun j => MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false
  have hpower : ∀ j n z, (betaD j^n) ((vCorner% corner) z : SpecialLinearGroup (Fin (k+4)) F)=
      ((vCorner% action) ι (u j) (phi j)^n) ((vCorner% corner) z) := by
    intro j n
    have hstep : ∀ z, betaD j ((vCorner% corner) z : SpecialLinearGroup (Fin (k+4)) F)=
        (vCorner% action) ι (u j) (phi j) ((vCorner% corner) z) := by
      intro z
      change (MulAut.conj (h j)) ((unitOdd% diagonalAut) (a j) (fieldAut (phi j) ((vCorner% corner) z)))=_
      rw [hact j]
      exact (inner_corner_action ι (u j) (v j) (phi j) z).trans
        ((vCorner% corner_step) ι (u j) (phi j) z).symm
    intro z
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ' (betaD j) n,pow_succ' ((vCorner% action) ι (u j) (phi j)) n]
      simp only [MulAut.mul_apply,ih,vCorner% corner_power]
      exact hstep _
  refine ⟨h,hdiagonal,hhu,?_⟩
  intro target ht
  obtain ⟨z,x,hz,hx,hxcorner,he⟩ := hcover target ht
  have hEF : ∀ j, MulAut.conj (hF0 j)*fieldAut (n:=k+4) (phi j)=
      (vCorner% action) ι (u j) (phi j) := by
    intro j
    rw [hehF0 j,radicalTorus% diagonalSL_action]
    rfl
  have hxpow : ∀ j, ((MulAut.conj (h j)*
      PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j)=
      ((MulAut.conj (hF0 j)*fieldAut (n:=k+4) (phi j))^(s j)) (x j) := by
    intro j
    rw [hxcorner j,hEF j]
    exact hpower j (s j) (z j)
  refine ⟨x,hx,?_⟩
  simpa only [hxpow] using he
end NikolovSegal.PartIIUnitaryRadicalCornerPrescribedProduct
