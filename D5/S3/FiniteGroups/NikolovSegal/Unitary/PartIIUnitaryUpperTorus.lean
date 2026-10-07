/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryUpperTorus
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryUpperTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalInnerTorus
import Mathlib.GroupTheory.FixedPointFree
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Lean Elab Term in
elab "radicalTorus%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIRadicalInnerTorus"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalInnerTorus"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique accepted determinant-one torus kernel {id} not found"

/-! Part II Definition6.6 and printed p255: unitary matrices are the
fixed points of the genuine field/inverse-transpose Steinberg action.
Regular torus conjugation is fixed-point-free on their actual upper
unitriangular subgroup. Finite fixed-point-free commutator surjectivity is
reused from Mathlib; it gives unitary witnesses, not merely SL witnesses.
The regular torus arithmetic and arbitrary bare automorphism reduction
are separate obligations, not assumptions of full-block coverage. -/
namespace NikolovSegal.PartIIUnitaryUpperTorus
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] {n : ℕ}

def steinberg (ι : RingAut F) : MulAut (SpecialLinearGroup (Fin n) F) :=
  fieldAut ι*(unitAction% rawGraph)

/-- The true anti-diagonal unitary coordinate law. -/
theorem steinberg_entry (ι : RingAut F) (g : SpecialLinearGroup (Fin n) F)
    (i j : Fin n) : steinberg ι g i j=ι (g⁻¹ j.rev i.rev) := rfl

def unitaryUpper (ι : RingAut F) : Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | LayerDepth 1 (g.val-1) ∧ steinberg ι g=g}
  one_mem' := ⟨by intro i j hij; simp, map_one _⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨(unitRec% product_depth) 1 (by decide) a b ha.1 hb.1,
      by rw [map_mul,ha.2,hb.2]⟩
  inv_mem' := by
    intro a ha
    exact ⟨(unitOdd% inverse_depth) 1 (by decide) a ha.1,
      by rw [map_inv,ha.2]⟩

private theorem diagonal_fixed (ι : RingAut F) (w : Fin n → Fˣ)
    (hw : ∏ i, w i=1) (hunit : ∀ i, ι (w i:F)*(w i.rev:F)=1) :
    steinberg ι ((radicalTorus% diagonalSL) w hw)=
      (radicalTorus% diagonalSL) w hw := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,(radicalTorus% diagonalSL_inverse)]
  change ι ((diagonal fun i => (((w i)⁻¹:Fˣ):F)) j.rev i.rev)=
    (diagonal fun i => (w i:F)) i j
  by_cases hij : i=j
  · subst j
    simp only [diagonal_apply,ite_true,Units.val_inv_eq_inv_val,map_inv₀]
    have hu := hunit i.rev
    rw [Fin.rev_rev] at hu
    exact (eq_inv_of_mul_eq_one_right hu).symm
  · have hr : j.rev≠i.rev := by
      intro he
      exact hij (Fin.rev_injective he).symm
    simp [diagonal_apply,hij,hr]

private theorem diagonal_power_action (w : Fin n → Fˣ) (hw : ∏ i, w i=1)
    (s : ℕ) (g : SpecialLinearGroup (Fin n) F) (i j : Fin n) :
    ((MulAut.conj (((radicalTorus% diagonalSL) w hw)^s)) g) i j=
      (((w i/w j)^s:Fˣ):F)*g i j := by
  rw [map_pow,(radicalTorus% diagonalSL_action)]
  induction s generalizing g with
  | zero => simp
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,(unitOdd% diagonal_entry),ih]
    simp only [pow_succ,Units.val_mul,Units.val_div_eq_div_val,div_eq_mul_inv,
      Units.val_inv_eq_inv_val]
    ring

private theorem upper_fixed_one (w : Fin n → Fˣ) (hw : ∏ i, w i=1)
    (s : ℕ) (hsep : ∀ i j : Fin n, i≠j → (w i/w j)^s≠1)
    (g : SpecialLinearGroup (Fin n) F) (hg : LayerDepth 1 (g.val-1))
    (he : (MulAut.conj (((radicalTorus% diagonalSL) w hw)^s)) g=g) : g=1 := by
  apply SpecialLinearGroup.ext
  intro i j
  by_cases hij : i=j
  · subst j
    have hh := hg i i (by omega)
    simpa only [sub_eq_zero,Matrix.sub_apply,Matrix.one_apply,ite_true,
      SpecialLinearGroup.coe_one] using hh
  · have hec := congrArg (fun a : SpecialLinearGroup (Fin n) F => a i j) he
    rw [diagonal_power_action] at hec
    have hc : (((w i/w j)^s:Fˣ):F)≠1 := by
      intro hh
      apply hsep i j hij
      exact Units.ext hh
    have hz : g i j=0 := by
      have hh : ((((w i/w j)^s:Fˣ):F)-1)*g i j=0 := by rw [sub_mul,one_mul,hec,sub_self]
      exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hc)
    simpa only [SpecialLinearGroup.coe_one,Matrix.one_apply,hij,ite_false] using hz

/-- Actual upper-unitary VALUE coverage by one regular inner torus.
The SAME determinant-one Steinberg-fixed h is chosen before ALL targets.
Every witness remains upper-unitriangular and Steinberg fixed; the result
is the exact unshifted noncommutative VALUE x^-1 h^s x h^-s.
This is the concrete fixed-torus kernel, not arbitrary-auto uniformity. -/
theorem actual_unitary_upper_regular_torus_values [Finite F]
    (ι : RingAut F) (w : Fin n → Fˣ) (hw : ∏ i, w i=1)
    (hunit : ∀ i, ι (w i:F)*(w i.rev:F)=1)
    (s : ℕ) (hsep : ∀ i j : Fin n, i≠j → (w i/w j)^s≠1) :
    ∃ h : SpecialLinearGroup (Fin n) F,
      h.val=diagonal (fun i => (w i:F)) ∧ steinberg ι h=h ∧
      ∀ b : SpecialLinearGroup (Fin n) F,
        LayerDepth 1 (b.val-1) → steinberg ι b=b →
        ∃ x : SpecialLinearGroup (Fin n) F,
          LayerDepth 1 (x.val-1) ∧ steinberg ι x=x ∧
          x⁻¹*h^s*x*(h^s)⁻¹=b := by
  classical
  let h := (radicalTorus% diagonalSL) w hw
  have hh : steinberg ι h=h := diagonal_fixed ι w hw hunit
  let alpha := MulAut.conj (h^s)
  have ha : ∀ g, g∈unitaryUpper ι → alpha g∈unitaryUpper ι := by
    intro g hg
    refine ⟨?_,?_⟩
    · change LayerDepth 1 (((MulAut.conj (h^s)) g).val-1)
      rw [map_pow,(radicalTorus% diagonalSL_action)]
      have hd : ∀ t : ℕ, LayerDepth 1 (((((unitOdd% diagonalAut) w)^t) g).val-1) := by
        intro t
        induction t with
        | zero => exact hg.1
        | succ t ih =>
          rw [pow_succ',MulAut.mul_apply]
          exact (unitOdd% diagonal_depth) w 1 _ ih
      exact hd s
    · change steinberg ι (h^s*g*(h^s)⁻¹)=h^s*g*(h^s)⁻¹
      rw [map_mul,map_mul,map_inv,map_pow,hh,hg.2]
  let f : unitaryUpper ι →* unitaryUpper ι :=
    { toFun := fun g => ⟨alpha g.val,ha g.val g.prop⟩
      map_one' := by apply Subtype.ext; exact map_one alpha
      map_mul' := by intro a b; apply Subtype.ext; exact map_mul alpha a.val b.val }
  have hf : MonoidHom.FixedPointFree f := by
    intro g hg
    apply Subtype.ext
    exact upper_fixed_one w hw s hsep g.val g.prop.1 (congrArg Subtype.val hg)
  refine ⟨h,rfl,hh,?_⟩
  intro b hb hbu
  let B : unitaryUpper ι := ⟨b,⟨hb,hbu⟩⟩
  obtain ⟨z,hz⟩ := hf.commutatorMap_surjective B
  refine ⟨z.val⁻¹,(unitOdd% inverse_depth) 1 (by decide) _ z.prop.1,
    by rw [map_inv,z.prop.2],?_⟩
  have he := congrArg Subtype.val hz
  change z.val*(alpha z.val)⁻¹=b at he
  simpa only [alpha,MulAut.conj_apply,_root_.mul_inv_rev,inv_inv,mul_assoc] using he
end NikolovSegal.PartIIUnitaryUpperTorus
