/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTraceCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTraceCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryCentralEvenProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Actual V* trace constraint, PartII Proposition6.7 pp262–263.
The last column is forced by the genuine reflected first row. The
noncommutative corner is a relative-trace constraint, never set to zero. -/
namespace NikolovSegal.PartIIUnitaryRadicalTraceCoordinates
open Matrix PartIIUnitriangularLayers PartIIRadicalCoordinates
open PartIIUnitaryUpperTorus UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {k : ℕ}
private theorem first_ne_last : (first:Fin (k+2))≠last := by
  intro he; have hh := congrArg Fin.val he
  simp only [first,last,Fin.val_zero,Fin.val_last] at hh; omega
private theorem rev_first : (first:Fin (k+2)).rev=last := by
  apply Fin.ext; simp [first,last,Fin.val_rev]
private theorem rev_last : (last:Fin (k+2)).rev=first := by
  apply Fin.ext; simp [first,last,Fin.val_rev]
private theorem rev_interior (i : Fin (k+2)) (hi0 : i≠first) (hil : i≠last) :
    i.rev≠first ∧ i.rev≠last := by
  constructor
  · intro he; apply hil; have hh := congrArg Fin.rev he; simpa only [Fin.rev_rev,rev_first] using hh
  · intro he; apply hi0; have hh := congrArg Fin.rev he; simpa only [Fin.rev_rev,rev_last] using hh
private theorem radical_diag (g : SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (i : Fin (k+2)) : g i i=1 := by
  have hh := hg.1 i i (by omega)
  simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true,sub_eq_zero] using hh

/-- Literal coordinate unitary criterion for the constructed radical.
The column relation and corner trace are exactly those of the TRUE
Steinberg inverse action; no unitary-recognition premise is used. -/
theorem actual_radical_unitary_of_trace (ι : RingAut F) (hinv : Function.Involutive ι)
    (r c : Fin (k+2) → F) (hr : EndpointZero r) (hc : EndpointZero c)
    (hcol : ∀ i, c i= -ι (r i.rev)) (z : F)
    (hz : z+ι z= -(∑ i, r i*ι (r i.rev))) :
    steinberg ι (radical r c hr hc z)=radical r c hr hc z := by
  let g := radical r c hr hc z
  have hg := actual_radical_mem r c hr hc z
  have hgi := actual_radical_inverse_mem g hg
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry]
  by_cases hi : i=first
  · subst i
    by_cases hj : j=last
    · subst j
      rw [rev_last,rev_first,actual_radical_inverse,actual_radical_corner,actual_radical_corner]
      have hsum : (∑ i, r i*c i)= -(∑ i, r i*ι (r i.rev)) := by
        simp only [hcol,mul_neg,Finset.sum_neg_distrib]
      rw [hsum,← hz,map_add,map_neg,map_add,hinv z]
      ring
    · by_cases hj0 : j=first
      · subst j
        rw [rev_first,radical_diag _ hgi,radical_diag _ hg,map_one]
      · have hjr := rev_interior j hj0 hj
        rw [rev_first,(actual_radical_inverse_row_column g hg j.rev hjr.1 hjr.2).2,
          actual_radical_column r c hr hc z j.rev hjr.1 hjr.2,hcol,Fin.rev_rev,
          actual_radical_row r c hr hc z j hj0 hj,map_neg,map_neg,hinv (r j),neg_neg]
  · by_cases hj : j=last
    · subst j
      by_cases hil : i=last
      · subst i
        rw [rev_last,radical_diag _ hgi,radical_diag _ hg,map_one]
      · have hir := rev_interior i hi hil
        rw [rev_last,(actual_radical_inverse_row_column g hg i.rev hir.1 hir.2).1,
          actual_radical_row r c hr hc z i.rev hir.1 hir.2,
          actual_radical_column r c hr hc z i hi hil,map_neg,hcol]
    · have hjr0 : j.rev≠first := by
        intro he; apply hj; have hh := congrArg Fin.rev he; simpa only [Fin.rev_rev,rev_first] using hh
      have hirL : i.rev≠last := by
        intro he; apply hi; have hh := congrArg Fin.rev he; simpa only [Fin.rev_rev,rev_last] using hh
      rw [hgi.2 _ _ hjr0 hirL,hg.2 _ _ hi hj]
      simp [Matrix.one_apply,Fin.rev_inj,eq_comm]

/-- Every genuine first-row quotient parameter has an ACTUAL unitary
radical lift. The corner is constructed by surjective relative trace,
including characteristic two and arbitrary ranks. -/
theorem actual_unitary_radical_row_lift (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (r : Fin (k+2) → F) (hr : EndpointZero r) :
    ∃ c : Fin (k+2) → F, ∃ hc : EndpointZero c, ∃ z : F,
      (∀ i, c i= -ι (r i.rev)) ∧
      z+ι z= -(∑ i, r i*ι (r i.rev)) ∧
      InRadical (radical r c hr hc z) ∧ steinberg ι (radical r c hr hc z)=radical r c hr hc z := by
  let c : Fin (k+2) → F := fun i => -ι (r i.rev)
  have hc : EndpointZero c := by
    constructor
    · simp only [c,rev_first,hr.2,map_zero,neg_zero]
    · simp only [c,rev_last,hr.1,map_zero,neg_zero]
  let S := ∑ i, r i*ι (r i.rev)
  have hfix : ι S=S := by
    dsimp only [S]
    simp only [map_sum,map_mul]
    rw [← Equiv.sum_comp (Fin.revPerm : Fin (k+2)≃Fin (k+2)) (fun i => r i*ι (r i.rev))]
    simp only [Fin.revPerm_apply,Fin.rev_rev]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hinv (r i.rev)]
    ring
  let T : fixedField ι := ⟨-S,by rw [mem_fixedField,map_neg,hfix]⟩
  obtain ⟨z,hz⟩ := trace_surjective ι hinv hne T
  have hz' : z+ι z= -S := hz
  exact ⟨c,hc,z,fun _ => rfl,hz',actual_radical_mem r c hr hc z,
    actual_radical_unitary_of_trace ι hinv r c hr hc (fun _ => rfl) z hz'⟩
end NikolovSegal.PartIIUnitaryRadicalTraceCoordinates
