/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthEndpointStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRowClearing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

/-- Fixing a literal coordinate row also fixes that row in the actual inverse. -/
theorem inverse_coordinate_row (g : specialUnitary n ι) (r : Fin n)
    (hrow : ∀ j, g.val.val r j=(1:Matrix (Fin n) (Fin n) F) r j) (j : Fin n) :
    (g.val⁻¹).val r j=(1:Matrix (Fin n) (Fin n) F) r j := by
  have hh := congrArg (fun A : SpecialLinearGroup (Fin n) F => A r j) (mul_inv_cancel g.val)
  change (∑ t, g.val.val r t*(g.val⁻¹).val t j)=(1:Matrix (Fin n) (Fin n) F) r j at hh
  simp only [hrow,Matrix.one_apply,ite_mul,one_mul,zero_mul] at hh
  simpa [Matrix.one_apply] using hh

/-- The other endpoint is forced by actual SU fixedness, not a flag premise. -/
theorem reflected_coordinate_column (g : specialUnitary n ι) (r : Fin n)
    (hrow : ∀ j, g.val.val r j=(1:Matrix (Fin n) (Fin n) F) r j) (i : Fin n) :
    g.val.val i r.rev=(1:Matrix (Fin n) (Fin n) F) i r.rev := by
  have hh := congrArg (fun A : SpecialLinearGroup (Fin n) F => A i r.rev) g.prop
  rw [steinberg_entry,Fin.rev_rev,inverse_coordinate_row g r hrow] at hh
  by_cases hi : i=r.rev
  · subst i
    simpa [Matrix.one_apply] using hh.symm
  · have hr : r≠i.rev := by
      intro he
      apply hi
      have he' := congrArg Fin.rev he
      simpa using he'.symm
    simpa [Matrix.one_apply,hi,hr] using hh.symm

/-- One absolute four-operation Hermitian elimination puts every actual SU
matrix of dimension≥4 in the two-endpoint stabilizer. Both endpoint equalities
are derived. This is a rank-reduction bridge, not a full width theorem. -/
theorem four_operations_endpoint_stabilizer [Finite F] {k : ℕ}
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (g : specialUnitary (k+4) ι) :
    ∃ u l v m : specialUnitary (k+4) ι,
      Positive u ∧ Negative l ∧ Positive v ∧ Negative m ∧
      (∀ j : Fin (k+4), (g*u*l*v*m).val.val last j=
        (1:Matrix (Fin (k+4)) (Fin (k+4)) F) last j) ∧
      (∀ i : Fin (k+4), (g*u*l*v*m).val.val i first=
        (1:Matrix (Fin (k+4)) (Fin (k+4)) F) i first) := by
  obtain ⟨u,l,v,m,hu,hl,hv,hm,hrow⟩ := last_row_reduction hinv hne g
  refine ⟨u,l,v,m,hu,hl,hv,hm,hrow,?_⟩
  intro i
  simpa only [Matrix.one_apply,rev_last] using reflected_coordinate_column (g*u*l*v*m) last hrow i

end NikolovSegal.UnitaryWholeGroupWidth
