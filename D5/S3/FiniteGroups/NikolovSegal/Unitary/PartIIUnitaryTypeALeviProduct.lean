/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALeviProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALeviProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTypeALevi
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Lean Elab Term in
elab "unitaryTypeA%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryTypeALevi"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTypeALevi"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual unitary type-A Levi kernel {id} not found"
open Lean Elab Term in
elab "unitaryCentral%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryCentralInnerTorus"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryCentralInnerTorus"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual unitary central torus kernel {id} not found"
/-! Part II p255, actual Proposition6.5 consumption on U2. Genuine
type-A diagonal/field actions, ambient unitary inner corrections and
unitary witnesses are constructed. The result is the Levi branch, not
whole SU or arbitrary-bare-unitary-automorphism classification. -/
namespace NikolovSegal.PartIIUnitaryTypeALeviProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open PartIIUnitaryTypeALevi
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}

def levi (ι : RingAut F) : SpecialLinearGroup (Fin d) F →*
    SpecialLinearGroup (Fin (2*d+2)) F := PartIICentralLevi.embed.comp (embed ι)
private theorem levi_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin d) F) : steinberg ι (levi ι g)=levi ι g := by
  change steinberg ι (PartIICentralLevi.embed (embed ι g))=_
  rw [PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,actual_typeA_levi_unitary ι hinv]
  rfl

private def ambientWeights (ι : RingAut F) (a : Fin d → Fˣ) : Fin (2*d+2) → Fˣ :=
  (unitaryCentral% extendWeights) ι ((unitaryTypeA% pairedUnits) ι a) 1

def diagonalField (ι : RingAut F) (a : Fin d → Fˣ) (phi : RingAut F) :
    MulAut (SpecialLinearGroup (Fin (2*d+2)) F) :=
  (unitOdd% diagonalAut) (ambientWeights ι a)*fieldAut phi

private theorem diagonal_steinberg_comm (ι : RingAut F)
    (w : Fin (2*d+2) → Fˣ) (hw : ∀ i, ι (w i:F)*(w i.rev:F)=1)
    (g : SpecialLinearGroup (Fin (2*d+2)) F) :
    steinberg ι ((unitOdd% diagonalAut) w g)=
      (unitOdd% diagonalAut) w (steinberg ι g) := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,← map_inv,(unitOdd% diagonal_entry),(unitOdd% diagonal_entry),steinberg_entry]
  have hi : ι (w i.rev:F)=(w i:F)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [Fin.rev_rev] using hw i.rev)
  have hj : ι (w j.rev:F)=(w j:F)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [Fin.rev_rev] using hw j.rev)
  simp only [Units.val_inv_eq_inv_val,map_mul,map_inv₀,hi,hj,inv_inv]
  ring

/-- The manufactured diagonal/field actions are genuine unitary actions
on the WHOLE actual SU subgroup, not merely on the displayed Levi. -/
theorem actual_diagonalField_preserves_unitary (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (a : Fin d → Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin (2*d+2)) F) (hg : steinberg ι g=g) :
    steinberg ι (diagonalField ι a phi g)=diagonalField ι a phi g := by
  have hf : steinberg ι (fieldAut phi g)=fieldAut phi (steinberg ι g) := by
    apply SpecialLinearGroup.ext
    intro i j
    rw [steinberg_entry,← map_inv]
    change ι (phi (g⁻¹ j.rev i.rev))=phi (steinberg ι g i j)
    rw [steinberg_entry,UnitaryField.involution_eq_pow ι hinv hne,
      UnitaryField.involution_eq_pow ι hinv hne,map_pow]
  have hw : ∀ i, ι (ambientWeights ι a i:F)*(ambientWeights ι a i.rev:F)=1 :=
    (unitaryCentral% extend_unitary) ι hinv _ ((unitaryTypeA% pairedUnits_unitary) ι hinv a) 1
  change steinberg ι ((unitOdd% diagonalAut) (ambientWeights ι a) (fieldAut phi g))=_
  rw [diagonal_steinberg_comm ι (ambientWeights ι a) hw,hf,hg]
  rfl

private theorem actual_levi_action (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fin d → Fˣ) (phi : RingAut F)
    (g : SpecialLinearGroup (Fin d) F) :
    diagonalField ι a phi (levi ι g)=
      levi ι ((unitOdd% diagonalAut) a (fieldAut phi g)) := by
  change (unitOdd% diagonalAut) (ambientWeights ι a)
    (fieldAut phi (PartIICentralLevi.embed (embed ι g)))=_
  rw [centralKernel% field_embed,actual_typeA_levi_field_action ι phi hinv hne,
    centralKernel% diagonal_embed]
  have he : (fun i => ambientWeights ι a (PartIICentralLevi.middle i))=
      (unitaryTypeA% pairedUnits) ι a :=
    funext ((unitaryCentral% extend_middle) ι _ 1)
  rw [he,unitaryTypeA% paired_diagonal_action]
  rfl

/-- Uniform prescribed-power VALUE coverage of the actual U2 inside
SU(2d+2), consuming the PROVED Proposition6.5, not a coverage premise.
N(q),FIELD cutoff precede all groups/ranks/action/divisor tuples. ONE
ambient determinant-one UNITARY correction tuple precedes ALL targets;
every witness is an actual positive UNITARY matrix in the type-A Levi. -/
theorem actual_uniform_unitary_typeA_Levi_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin d → Fˣ) (phi : Fin N → RingAut F)
        (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin d) F, LayerDepth 1 (b.val-1) →
          ∃ x : Fin N → SpecialLinearGroup (Fin d) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ LayerDepth 1 ((levi ι (x j)).val-1) ∧
              steinberg ι (levi ι (x j))=levi ι (x j)) ∧
            NikolovSegal.orderedProduct (fun j => (levi ι (x j))⁻¹*
              ((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (levi ι (x j)))=levi ι b := by
  obtain ⟨N,C,hN,hcover⟩ := PartIIProposition6_5.actual_proposition6_5_uniform_diagonal_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne d a phi s hs
  obtain ⟨eta,u,hu,hU⟩ := hcover F hF d a phi (fun _ => false) s hs
  have hD : ∀ j, ∃ h : SpecialLinearGroup (Fin (2*d+2)) F,
      steinberg ι h=h ∧ ∀ g : SpecialLinearGroup (Fin d) F,
        (MulAut.conj h) (levi ι g)=levi ι ((unitOdd% diagonalAut) (eta j) g) := by
    intro j
    exact actual_typeA_levi_ambient_diagonal_inner ι hinv hne (eta j)
  choose hD hhD heD using hD
  let h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F := fun j => levi ι (u j)*hD j
  let alpha : Fin N → MulAut (SpecialLinearGroup (Fin d) F) := fun j =>
    MulAut.conj (u j)*(unitOdd% diagonalAut) (eta j)*
      PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false
  let alphaA : Fin N → MulAut (SpecialLinearGroup (Fin (2*d+2)) F) := fun j =>
    MulAut.conj (h j)*diagonalField ι (a j) (phi j)
  have hstep : ∀ j g, alphaA j (levi ι g)=levi ι (alpha j g) := by
    intro j g
    dsimp only [alphaA,h]
    rw [map_mul,MulAut.mul_apply,MulAut.mul_apply,actual_levi_action ι hinv hne,
      heD j,MulAut.conj_apply,← map_inv,← map_mul,← map_mul]
    rfl
  have hpower : ∀ j t g, (alphaA j^t) (levi ι g)=levi ι ((alpha j^t) g) := by
    intro j t
    induction t with
    | zero => intro g; rfl
    | succ t ih =>
      intro g
      rw [pow_succ',MulAut.mul_apply,ih,hstep,pow_succ',MulAut.mul_apply]
      rfl
  refine ⟨h,?_,?_⟩
  · intro j
    dsimp only [h]
    rw [map_mul,levi_unitary ι hinv,hhD j]
  · intro b hb
    obtain ⟨x,hx,hxe⟩ := hU b hb
    refine ⟨x,fun j => ⟨hx j,PartIIAmbientUnipotentDecomposition.actual_central_embed_unitriangular
      _ (actual_typeA_levi_upper ι hinv (x j) (hx j)).1,levi_unitary ι hinv _⟩,?_⟩
    change NikolovSegal.orderedProduct (fun j => (levi ι (x j))⁻¹*(alphaA j^(s j)) (levi ι (x j)))=levi ι b
    simp only [hpower,← map_inv,← map_mul]
    have he := congrArg (fun g => levi ι g) hxe
    simpa only [alpha,NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def] using he
end NikolovSegal.PartIIUnitaryTypeALeviProduct
