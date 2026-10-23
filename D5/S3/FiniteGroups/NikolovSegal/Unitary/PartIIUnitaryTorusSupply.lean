/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTorusSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTorusSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryUpperTorus
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryAntidiagonalCoordinates
set_option autoImplicit false
set_option maxHeartbeats 1400000
/-! Actual unitary witnesses for the regular torus supplied by the
independently proved quadratic finite-field arithmetic. The Hermitian
equation is identified with the real Steinberg fixed-point law.
The field bounds depend on rank here; they are not an all-rank supplier. -/
namespace NikolovSegal.PartIIUnitaryTorusSupply
open Matrix PartIIUnitriangularLayers PartIIUnitaryUpperTorus UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {n : ℕ}

private theorem adjoint_antidiagonal_entry (ι : RingAut F)
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (UnitaryField.adjoint ι A*antiDiagonal (F:=F) n) i j=ι (A j.rev i) := by
  classical
  rw [Matrix.mul_apply,Finset.sum_eq_single j.rev]
  · simp [adjoint,antiDiagonal,hermitianForm]
  · intro t ht hne
    have hr : t.rev≠j := by
      intro he
      apply hne
      simpa only [Fin.rev_rev] using congrArg Fin.rev he
    simp [antiDiagonal,hermitianForm,hr]
  · simp
private theorem antidiagonal_entry (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (antiDiagonal (F:=F) n*A) i j=A i.rev j := by
  classical
  rw [Matrix.mul_apply,Finset.sum_eq_single i.rev]
  · simp [antiDiagonal,hermitianForm]
  · intro t ht hne
    simp [antiDiagonal,hermitianForm,Ne.symm hne]
  · simp

/-- The literal anti-diagonal Hermitian matrix equation is equivalent to
Fix(field/inverse-transpose); neither presentation assumes unitary
coverage. This connects the torus arithmetic to actual SU witnesses. -/
theorem actual_steinberg_iff_hermitian (ι : RingAut F)
    (hinv : Function.Involutive ι) (g : SpecialLinearGroup (Fin n) F) :
    steinberg ι g=g ↔ UnitaryField.adjoint ι g.val*antiDiagonal (F:=F) n*g.val=antiDiagonal (F:=F) n := by
  have hi : g.val*(g⁻¹).val=1 := congrArg Subtype.val (mul_inv_cancel g)
  have hir : (g⁻¹).val*g.val=1 := congrArg Subtype.val (inv_mul_cancel g)
  have hcancel : UnitaryField.adjoint ι g.val*antiDiagonal (F:=F) n*g.val=antiDiagonal (F:=F) n ↔
      UnitaryField.adjoint ι g.val*antiDiagonal (F:=F) n=antiDiagonal (F:=F) n*(g⁻¹).val := by
    constructor
    · intro hh
      have he := congrArg (fun A : Matrix (Fin n) (Fin n) F => A*(g⁻¹).val) hh
      simpa only [mul_assoc,hi,mul_one] using he
    · intro hh
      rw [hh,mul_assoc,hir,mul_one]
  rw [hcancel]
  constructor
  · intro hg
    ext i j
    rw [adjoint_antidiagonal_entry,antidiagonal_entry]
    have hin : steinberg ι g⁻¹=g⁻¹ := by rw [map_inv,hg]
    have he := congrArg (fun a : SpecialLinearGroup (Fin n) F => a i.rev j) hin
    simpa only [steinberg_entry,inv_inv,Fin.rev_rev] using he
  · intro hg
    apply SpecialLinearGroup.ext
    intro i j
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) F => A j i.rev) hg
    rw [adjoint_antidiagonal_entry,antidiagonal_entry,Fin.rev_rev] at he
    rw [steinberg_entry,← he,hinv]

private theorem reflected_transport {I : Type*} (e : I ≃ Fin n) (τ : I ≃ I)
    (href : ∀ i, e (τ i)=(e i).rev) (i : Fin n) :
    e.symm i.rev=τ (e.symm i) := by
  apply e.injective
  simp only [e.apply_symm_apply,href]

/-- One genuine SU torus before every upper SU target, even ranks>=4.
The complete finite-field separation proof is consumed, not assumed. -/
theorem actual_even_unitary_upper_torus_values (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (m s : ℕ) (hs : 0<s)
    (hQ : 2*s*(m+2)^2+2<Nat.card (fixedField ι)) :
    ∃ h : SpecialLinearGroup (Fin (2*(m+2))) F,
      UnitaryField.adjoint ι h.val*antiDiagonal (F:=F) (2*(m+2))*h.val=antiDiagonal (F:=F) (2*(m+2)) ∧
      ∀ b : SpecialLinearGroup (Fin (2*(m+2))) F,
        LayerDepth 1 (b.val-1) →
        UnitaryField.adjoint ι b.val*antiDiagonal (F:=F) (2*(m+2))*b.val=antiDiagonal (F:=F) (2*(m+2)) →
        ∃ x : SpecialLinearGroup (Fin (2*(m+2))) F,
          LayerDepth 1 (x.val-1) ∧
          UnitaryField.adjoint ι x.val*antiDiagonal (F:=F) (2*(m+2))*x.val=antiDiagonal (F:=F) (2*(m+2)) ∧
          x⁻¹*h^s*x*(h^s)⁻¹=b := by
  obtain ⟨u,D,hD,hDu,hsep,hact⟩ := regular_even_antidiagonal_torus ι hinv hne m s hs hQ
  let e := evenLabel (m+2)
  let w := fun i => pairedEntries ι (evenWeight m) u (e.symm i)
  have hw : ∏ i, w i=1 := by
    rw [e.symm.prod_comp]
    rw [prod_pairedEntries,evenWeight_sum,zpow_zero]
  have hu : ∀ i, ι (w i:F)*(w i.rev:F)=1 := by
    intro i
    have he := reflected_transport e (pairSwap _) (evenLabel_reflection _) i
    have hh := pairedEntries_hermitian ι hinv (evenWeight m) u (e.symm i)
    have hh' := congrArg (fun z : Fˣ => (z:F)) hh
    simpa only [w,he,Units.val_mul,involutionUnit_val,Units.val_one] using hh'
  obtain ⟨h,hh,hhu,hcover⟩ := actual_unitary_upper_regular_torus_values ι w hw hu s hsep
  refine ⟨h,(actual_steinberg_iff_hermitian ι hinv h).mp hhu,?_⟩
  intro b hb hbu
  obtain ⟨x,hx,hxu,hxe⟩ := hcover b hb ((actual_steinberg_iff_hermitian ι hinv b).mpr hbu)
  exact ⟨x,hx,(actual_steinberg_iff_hermitian ι hinv x).mp hxu,hxe⟩

/-- The same actual full-upper-unitary kernel in every odd rank>=3.
The central norm-one diagonal correction is the proved arithmetic one. -/
theorem actual_odd_unitary_upper_torus_values (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (d s : ℕ) (hd : 0<d) (hs : 0<s)
    (hQ : 2*s*(d+1)^2+2<Nat.card (fixedField ι)) :
    ∃ h : SpecialLinearGroup (Fin (2*d+1)) F,
      UnitaryField.adjoint ι h.val*antiDiagonal (F:=F) (2*d+1)*h.val=antiDiagonal (F:=F) (2*d+1) ∧
      ∀ b : SpecialLinearGroup (Fin (2*d+1)) F,
        LayerDepth 1 (b.val-1) →
        UnitaryField.adjoint ι b.val*antiDiagonal (F:=F) (2*d+1)*b.val=antiDiagonal (F:=F) (2*d+1) →
        ∃ x : SpecialLinearGroup (Fin (2*d+1)) F,
          LayerDepth 1 (x.val-1) ∧
          UnitaryField.adjoint ι x.val*antiDiagonal (F:=F) (2*d+1)*x.val=antiDiagonal (F:=F) (2*d+1) ∧
          x⁻¹*h^s*x*(h^s)⁻¹=b := by
  obtain ⟨u,D,hD,hDu,hsep,hact⟩ := regular_odd_antidiagonal_torus ι hinv hne d s hd hs hQ
  let e := oddLabel d
  let w := fun i => oddEntries ι (positiveWeight d) u (e.symm i)
  have hw : ∏ i, w i=1 := by rw [e.symm.prod_comp,prod_oddEntries]
  have hu : ∀ i, ι (w i:F)*(w i.rev:F)=1 := by
    intro i
    have he := reflected_transport e (oddSwap _) (oddLabel_reflection _) i
    have hh := oddEntries_hermitian ι hinv (positiveWeight d) u (e.symm i)
    have hh' := congrArg (fun z : Fˣ => (z:F)) hh
    simpa only [w,he,Units.val_mul,involutionUnit_val,Units.val_one] using hh'
  obtain ⟨h,hh,hhu,hcover⟩ := actual_unitary_upper_regular_torus_values ι w hw hu s hsep
  refine ⟨h,(actual_steinberg_iff_hermitian ι hinv h).mp hhu,?_⟩
  intro b hb hbu
  obtain ⟨x,hx,hxu,hxe⟩ := hcover b hb ((actual_steinberg_iff_hermitian ι hinv b).mpr hbu)
  exact ⟨x,hx,(actual_steinberg_iff_hermitian ι hinv x).mp hxu,hxe⟩
end NikolovSegal.PartIIUnitaryTorusSupply
