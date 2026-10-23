/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTorus
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryLeviDecomposition
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Lean Elab Term in
elab "unitaryTorus%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryUpperTorus"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryUpperTorus"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual upper-unitary torus kernel {id} not found"
namespace NikolovSegal.PartIIUnitaryRadicalTorus
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] {k : ℕ}

/-- Definition6.6(ii), with the actual V support and true Steinberg law. -/
def unitaryRadical (ι : RingAut F) : Subgroup (SpecialLinearGroup (Fin (k+2)) F) where
  carrier := {g | InRadical g ∧ steinberg ι g=g}
  one_mem' := ⟨⟨by intro i j hij; simp,by intro i j hi hj; rfl⟩,map_one _⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨actual_radical_product_mem a b ha.1 hb.1,by rw [map_mul,ha.2,hb.2]⟩
  inv_mem' := by
    intro a ha
    exact ⟨actual_radical_inverse_mem a ha.1,by rw [map_inv,ha.2]⟩

private theorem radical_fixed_one (w : Fin (k+2) → Fˣ) (hw : ∏ i, w i=1)
    (s : ℕ)
    (hsep : ∀ i j : Fin (k+2), i≠j → (i=first ∨ j=last) → (w i/w j)^s≠1)
    (g : SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (he : (MulAut.conj (((radicalTorus% diagonalSL) w hw)^s)) g=g) : g=1 := by
  apply SpecialLinearGroup.ext
  intro i j
  by_cases hij : i=j
  · subst j
    exact sub_eq_zero.mp (hg.1 i i (by omega))
  · by_cases hactive : i=first ∨ j=last
    · have hec := congrArg (fun a : SpecialLinearGroup (Fin (k+2)) F => a i j) he
      rw [unitaryTorus% diagonal_power_action] at hec
      have hc : (((w i/w j)^s:Fˣ):F)≠1 := by
        intro hh
        exact hsep i j hij hactive (Units.ext hh)
      have hz : g i j=0 := by
        have hh : ((((w i/w j)^s:Fˣ):F)-1)*g i j=0 := by rw [sub_mul,one_mul,hec,sub_self]
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hc)
      simpa only [SpecialLinearGroup.coe_one,Matrix.one_apply,hij,ite_false] using hz
    · exact hg.2 i j (fun hi => hactive (Or.inl hi)) (fun hj => hactive (Or.inr hj))

/-- Genuine rank-independent-support torus kernel for V*. Separation is
required ONLY on first-row/last-column roots, not every matrix root.
ONE actual determinant-one unitary h precedes ALL targets and all
witnesses remain in V*, including the noncommutative corner coordinate. -/
theorem actual_unitary_radical_regular_torus_values [Finite F]
    (ι : RingAut F) (w : Fin (k+2) → Fˣ) (hw : ∏ i, w i=1)
    (hunit : ∀ i, ι (w i:F)*(w i.rev:F)=1)
    (s : ℕ)
    (hsep : ∀ i j : Fin (k+2), i≠j → (i=first ∨ j=last) → (w i/w j)^s≠1) :
    ∃ h : SpecialLinearGroup (Fin (k+2)) F,
      h.val=diagonal (fun i => (w i:F)) ∧ steinberg ι h=h ∧
      ∀ b : SpecialLinearGroup (Fin (k+2)) F,
        InRadical b → steinberg ι b=b →
        ∃ x : SpecialLinearGroup (Fin (k+2)) F,
          InRadical x ∧ steinberg ι x=x ∧ x⁻¹*h^s*x*(h^s)⁻¹=b := by
  classical
  let h := (radicalTorus% diagonalSL) w hw
  have hh : steinberg ι h=h := (unitaryTorus% diagonal_fixed) ι w hw hunit
  let alpha := MulAut.conj (h^s)
  have ha : ∀ g, g∈unitaryRadical ι → alpha g∈unitaryRadical ι := by
    intro g hg
    refine ⟨⟨?_,?_⟩,?_⟩
    · change LayerDepth 1 (((MulAut.conj (h^s)) g).val-1)
      rw [map_pow,(radicalTorus% diagonalSL_action)]
      have hd : ∀ t : ℕ, LayerDepth 1 (((((unitOdd% diagonalAut) w)^t) g).val-1) := by
        intro t
        induction t with
        | zero => exact hg.1.1
        | succ t ih =>
          rw [pow_succ',MulAut.mul_apply]
          exact (unitOdd% diagonal_depth) w 1 _ ih
      exact hd s
    · intro i j hi hj
      rw [unitaryTorus% diagonal_power_action,hg.1.2 i j hi hj]
      by_cases hij : i=j
      · subst j; simp [Matrix.one_apply]
      · simp [Matrix.one_apply,hij]
    · change steinberg ι (h^s*g*(h^s)⁻¹)=h^s*g*(h^s)⁻¹
      rw [map_mul,map_mul,map_inv,map_pow,hh,hg.2]
  let f : unitaryRadical ι →* unitaryRadical ι :=
    { toFun := fun g => ⟨alpha g.val,ha g.val g.prop⟩
      map_one' := by apply Subtype.ext; exact map_one alpha
      map_mul' := by intro a b; apply Subtype.ext; exact map_mul alpha a.val b.val }
  have hf : MonoidHom.FixedPointFree f := by
    intro g hg
    apply Subtype.ext
    exact radical_fixed_one w hw s hsep g.val g.prop.1 (congrArg Subtype.val hg)
  refine ⟨h,rfl,hh,?_⟩
  intro b hb hbu
  let B : unitaryRadical ι := ⟨b,⟨hb,hbu⟩⟩
  obtain ⟨z,hz⟩ := hf.commutatorMap_surjective B
  refine ⟨z.val⁻¹,actual_radical_inverse_mem _ z.prop.1,
    by rw [map_inv,z.prop.2],?_⟩
  have he := congrArg Subtype.val hz
  change z.val*(alpha z.val)⁻¹=b at he
  simpa only [alpha,MulAut.conj_apply,_root_.mul_inv_rev,inv_inv,mul_assoc] using he
end NikolovSegal.PartIIUnitaryRadicalTorus
