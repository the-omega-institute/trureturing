/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryLeviDecomposition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryLeviDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryUpperTorus
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIAmbientUnipotentDecomposition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
/-! Part II printed p255, Case2: the actual fixed-point decomposition
U*=U1* V*. The accepted SL decomposition is reused; uniqueness of its
middle block forces BOTH factors to remain Steinberg fixed. -/
namespace NikolovSegal.PartIIUnitaryLeviDecomposition
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIICentralLevi PartIIRadicalCoordinates PartIIUnitaryUpperTorus
open PartIIAmbientUnipotentDecomposition
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem actual_steinberg_central_levi (ι : RingAut F)
    (g : SpecialLinearGroup (Fin n) F) :
    steinberg ι (embed g)=embed (steinberg ι g) := by
  change fieldAut ι ((unitAction% rawGraph) (embed g))=_
  rw [centralKernel% raw_graph_embed,centralKernel% field_embed]
  rfl

private theorem reflected_not_first {i : Fin (n+2)} (hi : i≠last) : i.rev≠first := by
  intro hh
  have he := congrArg Fin.val hh
  simp only [Fin.val_rev,first,Fin.val_zero] at he
  apply hi; apply Fin.ext
  simp only [last,Fin.val_last]; omega
private theorem reflected_not_last {i : Fin (n+2)} (hi : i≠first) : i.rev≠last := by
  intro hh
  have he := congrArg Fin.val hh
  simp only [Fin.val_rev,last,Fin.val_last] at he
  apply hi; apply Fin.ext
  simp only [first,Fin.val_zero]; omega

theorem actual_steinberg_radical_mem (ι : RingAut F)
    (v : SpecialLinearGroup (Fin (n+2)) F) (hv : InRadical v) :
    InRadical (steinberg ι v) := by
  have hi := actual_radical_inverse_mem v hv
  refine ⟨?_,?_⟩
  · exact (unitOdd% field_depth) ι 1 _ ((unitAction% rawGraph_depth) v hv.1)
  · intro i j hi0 hjl
    rw [steinberg_entry,hi.2 j.rev i.rev
      (reflected_not_first hjl) (reflected_not_last hi0)]
    simp [Matrix.one_apply,Fin.rev_inj,eq_comm]

private theorem middle_not_first (i : Fin n) : middle i≠(first : Fin (n+2)) := by
  intro hh
  have he := congrArg Fin.val hh
  simp only [middle,Fin.val_succ,Fin.val_castSucc,first,Fin.val_zero] at he
  omega
private theorem middle_not_last (i : Fin n) : middle i≠(last : Fin (n+2)) := by
  intro hh
  have he := congrArg Fin.val hh
  simp only [middle,Fin.val_succ,Fin.val_castSucc,last,Fin.val_last] at he
  omega

/-- The literal middle block after multiplying by an arbitrary radical
factor. No commutation of the two factors is used. -/
theorem actual_levi_radical_middle (g : SpecialLinearGroup (Fin n) F)
    (v : SpecialLinearGroup (Fin (n+2)) F) (hv : InRadical v)
    (i j : Fin n) : (embed g*v) (middle i) (middle j)=g i j := by
  classical
  rw [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  change embed g (middle i) 0*v 0 (middle j)+
    ((∑ t : Fin n, embed g (middle i) (middle t)*v (middle t) (middle j))+
      embed g (middle i) (Fin.last (n+1))*v (Fin.last (n+1)) (middle j))=_
  have hend : embed g (middle i) 0=0 ∧ embed g (middle i) (Fin.last (n+1))=0 := by
    constructor
    · rw [← (centralKernel% index_middle) i,← centralKernel% index_first,centralKernel% entry]; rfl
    · rw [← (centralKernel% index_middle) i,← centralKernel% index_last,centralKernel% entry]; rfl
  rw [hend.1,hend.2,zero_mul,zero_mul,zero_add,add_zero]
  have hmid : ∀ t : Fin n, v (middle t) (middle j)=(1:Matrix (Fin n) (Fin n) F) t j := by
    intro t
    rw [hv.2 (middle t) (middle j) (middle_not_first t) (middle_not_last j)]
    simp only [Matrix.one_apply]
    congr 1
    apply propext
    constructor
    · intro he
      apply Fin.ext
      have he' := congrArg Fin.val he
      simp only [middle,Fin.val_succ,Fin.val_castSucc] at he'
      omega
    · exact congrArg middle
  simp only [actual_central_levi_middle_entry,hmid]
  exact congrArg (fun A : Matrix (Fin n) (Fin n) F => A i j) (mul_one g.val)

/-- Exact p255 unitary decomposition on the actual central SU(n) and
actual V*=V intersect Fix(Steinberg). The fixed-point facts are DERIVED
from the original target; no off-block/unitary coverage is assumed. -/
theorem actual_unitary_ambient_U_decomposition (ι : RingAut F)
    (b : SpecialLinearGroup (Fin (n+2)) F)
    (hb : LayerDepth 1 (b.val-1)) (hbu : steinberg ι b=b) :
    ∃ g : SpecialLinearGroup (Fin n) F, ∃ v : SpecialLinearGroup (Fin (n+2)) F,
      LayerDepth 1 (g.val-1) ∧ steinberg ι g=g ∧
      InRadical v ∧ steinberg ι v=v ∧ embed g*v=b := by
  obtain ⟨g,v,hg,hv,hgv⟩ := actual_ambient_U_decomposition b hb
  have he : embed (steinberg ι g)*steinberg ι v=embed g*v := by
    rw [← actual_steinberg_central_levi,← map_mul,hgv,hbu]
  have hvs := actual_steinberg_radical_mem ι v hv
  have hgs : steinberg ι g=g := by
    apply SpecialLinearGroup.ext
    intro i j
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (n+2)) F => a (middle i) (middle j)) he
    simpa only [actual_levi_radical_middle _ _ hvs,actual_levi_radical_middle _ _ hv] using hh
  have hve : steinberg ι v=v := by
    rw [hgs] at he
    exact mul_left_cancel he
  exact ⟨g,v,hg,hgs,hv,hve,hgv⟩
end NikolovSegal.PartIIUnitaryLeviDecomposition
