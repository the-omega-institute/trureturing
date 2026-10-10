/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryPrescribedLowerProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryPrescribedLowerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryPrescribedUProduct
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnipotentDuality
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII Proposition6.2 after p251: actual opposite-U transport.
Inverse-transpose is a group automorphism, so the noncommutative ordered
product is preserved, with genuine unitary corrections and witnesses. -/
open Lean Elab Term in
elab "unitaryDual%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnipotentDuality"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) => n.toString.endsWith suffix && match env.getModuleIdxFor? n with
    | none => false
    | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnipotentDuality"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Accepted actual inverse-transpose kernel {id} not found"
namespace NikolovSegal.PartIIUnitaryPrescribedLowerProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open PartIIUnipotentDuality UnitaryField
universe u
variable {F : Type u} [Field F] {n : ℕ}
private theorem dual_unitary (ι : RingAut F) (g : SpecialLinearGroup (Fin n) F)
    (hg : steinberg ι g=g) : steinberg ι (dual g)=dual g := by
  change fieldAut ι ((unitAction% rawGraph) (dual g))=dual g
  rw [← unitaryDual% dual_raw_graph,← unitaryDual% dual_field]
  exact congrArg dual hg
private theorem dual_upper_to_lower (g : SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1)) : SLnUnipotentWidth.Lower (dual g) := by
  have hi := (unitLayer% inverse_unit_depth) g hg
  have hh := actual_unitriangular_upper_iff g⁻¹ |>.mp hi
  exact ⟨fun i j hij => hh.1 j i hij,fun i => hh.2 i⟩

/-- ONE uniform length/cutoff precedes every field/rank/genuine prescribed
D/Phi tuple. Actual lower unitary targets have genuine lower unitary
witnesses; ONE global SU correction precedes ALL targets, with exact
ordered original divisor powers. No opposite transport is assumed. -/
theorem actual_uniform_all_rank_unitary_lower_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin n) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin n) F, SLnUnipotentWidth.Lower b → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin n) F,
            (∀ j, SLnUnipotentWidth.Lower (x j) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=b := by
  obtain ⟨N,C,hN,hU⟩ := PartIIUnitaryPrescribedUProduct.actual_uniform_all_rank_unitary_U_prescribed_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi s hs
  have hi : ∀ j i, ι (((a j i)⁻¹:Fˣ):F)*(((a j i.rev)⁻¹:Fˣ):F)=(((c j)⁻¹: (fixedField ι)ˣ):fixedField ι) := by
    intro j i
    simp only [Units.val_inv_eq_inv_val,map_inv₀]
    rw [← mul_inv,ha j i]
    rfl
  obtain ⟨h0,hh0,hcover⟩ := hU F hF ι hinv hne n hn (fun j i => (a j i)⁻¹)
    (fun j => (c j)⁻¹) hi phi s hs
  let h := fun j => dual (h0 j)
  let alpha := fun j => MulAut.conj (h0 j)*PartIIProposition6_5.diagonalFieldGraph (fun i => (a j i)⁻¹) (phi j) false
  let beta := fun j => MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false
  have step : ∀ j g, dual (alpha j g)=beta j (dual g) := by
    intro j g
    simp only [alpha,beta,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
      actual_dual_diagonal_field_graph,inv_inv,h]
  have power : ∀ j t g, dual ((alpha j^t) g)=(beta j^t) (dual g) := by
    intro j t
    induction t with
    | zero => intro g; rfl
    | succ t ih => intro g; rw [pow_succ',MulAut.mul_apply,step,ih,pow_succ',MulAut.mul_apply]; rfl
  refine ⟨h,fun j => dual_unitary ι _ (hh0 j),?_⟩
  intro b hb hu
  obtain ⟨x0,hx0,he0⟩ := hcover (dual b) (actual_dual_lower_target b hb) (dual_unitary ι b hu)
  let x := fun j => dual (x0 j)
  refine ⟨x,fun j => ⟨dual_upper_to_lower _ (hx0 j).1,dual_unitary ι _ (hx0 j).2⟩,?_⟩
  have he := congrArg (fun g => dual g) he0
  simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,map_mul,map_inv,
    unitaryDual% dual_twice] at he
  change orderedProduct (fun j => (x j)⁻¹*(beta j^(s j)) (x j))=b
  simpa only [orderedProduct,alpha,power,x] using he
end NikolovSegal.PartIIUnitaryPrescribedLowerProduct
