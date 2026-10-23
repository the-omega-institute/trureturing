/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryDiagonalNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryDiagonalNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalPrescribedMiddleProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
/-! Actual D normalization at either exceptional V* pair, pp262–263.
The accepted norm/Hilbert90 middle normal form is consumed. Its free
determinant absorber is MOVED to a third reflected pair by a true SU
inner torus. The desired boundary coefficient is u^2; all corrections
precede targets, and no determinant-one diagonal form is assumed. -/
namespace NikolovSegal.PartIIUnitaryRadicalBoundaryDiagonalNormalization
open Matrix PartIIUnitriangularActions PartIIUnitaryUpperTorus UnitaryField
open PartIIUnitaryRadicalDiagonalNormalization
universe u
variable {F : Type u} [Field F] [Finite F] {k : ℕ}
private def weights (ι : RingAut F) (u d w : Fˣ) : Fin (k+6) → Fˣ :=
  (unitaryCentral% extendWeights) ι
    ((unitaryCentral% extendWeights) ι
      ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1) w) d) u
private theorem weights_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (u d w : Fˣ) (i : Fin (k+6)) :
    ι (weights ι u d w i:F)*(weights ι u d w i.rev:F)=1 :=
  (unitaryCentral% extend_unitary) ι hinv _
    ((unitaryCentral% extend_unitary) ι hinv _
      ((unitaryCentral% extend_unitary) ι hinv _ (fun _ => by simp) w) d) u i
private theorem weights_product (ι : RingAut F) (u d w : Fˣ) :
    ∏ i, weights (k:=k) ι u d w i=
      (u/involutionUnit ι u)*(d/involutionUnit ι d)*(w/involutionUnit ι w) := by
  change (∏ i, Fin.cons u (Fin.snoc (Fin.cons d (Fin.snoc
    (Fin.cons w (Fin.snoc (fun _ : Fin k => (1:Fˣ)) (involutionUnit ι w)⁻¹))
    (involutionUnit ι d)⁻¹)) (involutionUnit ι u)⁻¹) i)=_
  simp only [Fin.prod_cons,Fin.prod_snoc,Finset.prod_const_one,one_mul,div_eq_mul_inv]
  simp [mul_assoc,mul_comm,mul_left_comm]

/-- Actual boundary diagonal normalization. Rank k+6 provides a third
reflected pair to absorb the determinant independently of the selected
boundary coefficient. The exact adjusted action holds on ALL matrices. -/
theorem actual_unitary_radical_boundary_diagonal_inner (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (a : Fin (k+6) → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F)) (u d : Fˣ) :
    ∃ h : SpecialLinearGroup (Fin (k+6)) F, ∃ w : Fˣ,
      (∀ i j, i≠j → h i j=0) ∧ steinberg ι h=h ∧ ∀ g : SpecialLinearGroup (Fin (k+6)) F,
        (MulAut.conj h) ((unitOdd% diagonalAut) a g)=
          (unitOdd% diagonalAut) (weights ι u d w) g := by
  classical
  obtain ⟨h0,v,hdiag0,hh0,hact0⟩ := actual_unitary_radical_middle_diagonal_inner (k:=k+2)
    ι hinv hne a c ha u
  let B0 : Fin (k+6) → Fˣ := (vNormalize% innerWeights) ι u v
  let w : Fˣ := v/d
  let B1 := weights (k:=k) ι u d w
  have hprod : ∏ i, B1 i=∏ i, B0 i := by
    rw [weights_product,vNormalize% innerWeights_product]
    dsimp only [w]
    rw [map_div]
    apply Units.ext
    simp only [Units.val_mul,Units.val_div_eq_div_val]
    field_simp
  let ratio := fun i => B1 i/B0 i
  have hp : ∏ i, ratio i=1 := by
    rw [Finset.prod_div_distrib,hprod]
    exact div_self' _
  have hru : ∀ i, ι (ratio i:F)*(ratio i.rev:F)=1 := by
    intro i
    simp only [ratio,Units.val_div_eq_div_val,map_div₀]
    calc
      _ = (ι (B1 i:F)*(B1 i.rev:F))/(ι (B0 i:F)*(B0 i.rev:F)) := by ring
      _ = 1 := by rw [weights_unitary ι hinv,(vNormalize% innerWeights_unitary) ι hinv]; simp
  let h1 := (radicalTorus% diagonalSL) ratio hp
  have hh1 : steinberg ι h1=h1 := (unitaryTorus% diagonal_fixed) ι ratio hp hru
  have hact1 : ∀ g : SpecialLinearGroup (Fin (k+6)) F,
      (MulAut.conj h1) ((unitOdd% diagonalAut) B0 g)=(unitOdd% diagonalAut) B1 g := by
    intro g
    rw [radicalTorus% diagonalSL_action]
    apply SpecialLinearGroup.ext
    intro i j
    rw [unitOdd% diagonal_entry,unitOdd% diagonal_entry,unitOdd% diagonal_entry]
    simp only [ratio,Units.val_div_eq_div_val,Units.val_inv_eq_inv_val]
    field_simp
  have hdiag1 : ∀ i j, i≠j → h1 i j=0 := by
    intro i j hij
    change Matrix.diagonal (fun t => (ratio t:F)) i j=0
    simp [Matrix.diagonal_apply,hij]
  refine ⟨h1*h0,w,?_,by rw [map_mul,hh1,hh0],?_⟩
  · intro i j hij
    change (∑ t, h1 i t*h0 t j)=0
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hit : i=t
    · subst t; rw [hdiag0 i j hij,mul_zero]
    · rw [hdiag1 i t hit,zero_mul]
  · intro g
    change (h1*h0)*((unitOdd% diagonalAut) a g)*(h1*h0)⁻¹=_
    calc
      _ = (MulAut.conj h1) ((MulAut.conj h0) ((unitOdd% diagonalAut) a g)) := by
        simp only [MulAut.conj_apply,_root_.mul_inv_rev,mul_assoc]
      _ = (unitOdd% diagonalAut) B1 g := by rw [hact0,hact1]
end NikolovSegal.PartIIUnitaryRadicalBoundaryDiagonalNormalization
