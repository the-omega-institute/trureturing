/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalCoordinates
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIIRadicalActions
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIRadicalCoordinates
universe u
variable {F : Type u} [Field F] {k : ℕ}
private theorem rev_first : (first : Fin (k+2)).rev=last := by
  apply Fin.ext; simp [first,last,Fin.val_rev]
private theorem rev_last : (last : Fin (k+2)).rev=first := by
  apply Fin.ext; simp [first,last,Fin.val_rev]
private theorem rev_ne_first {j : Fin (k+2)} (h : j≠last) : j.rev≠first := by
  intro he; have hh := congrArg Fin.rev he; apply h; simpa [rev_first] using hh
private theorem rev_ne_last {j : Fin (k+2)} (h : j≠first) : j.rev≠last := by
  intro he; have hh := congrArg Fin.rev he; apply h; simpa [rev_last] using hh
private theorem sign_square (t : ℕ) : (-1:F)^t*(-1:F)^t=1 := by
  rw [← pow_two,← pow_mul,mul_comm t 2,pow_mul]; simp
private theorem reflected_sign (j : Fin (k+2)) :
    (-1:F)^j.rev.val*(-1:F)^(k+1)=(-1:F)^j.val := by
  have he : j.val+j.rev.val=k+1 := by simp only [Fin.val_rev]; omega
  rw [← he,pow_add]
  calc
    _ = (-1:F)^j.val*((-1:F)^j.rev.val*(-1:F)^j.rev.val) := by ring
    _ = _ := by rw [sign_square,mul_one]
/-- Derived from actual inverse-transpose and actual radical inverse;
these are not supplied root-action laws. -/
theorem actual_positive_graph_radical_coordinates
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    positiveGraph g first j=(-1:F)^(j.val+1)*g j.rev last ∧
      positiveGraph g j.rev last=(-1:F)^(j.val+1)*g first j := by
  have hr := actual_radical_inverse_row_column g hg j.rev (rev_ne_first hjl) (rev_ne_last hj0)
  have hc := actual_radical_inverse_row_column g hg j hj0 hjl
  constructor
  · change heightTorus (-1:Fˣ) ((unitAction% rawGraph) g) first j=_
    rw [(unitAction% torus_entry),(unitAction% rawGraph_entry),rev_first,hr.2]
    simp only [first,Fin.val_zero,pow_zero,one_mul,Units.val_neg,Units.val_one,pow_succ]
    ring
  · change heightTorus (-1:Fˣ) ((unitAction% rawGraph) g) j.rev last=_
    rw [(unitAction% torus_entry),(unitAction% rawGraph_entry),rev_last,Fin.rev_rev,hc.1]
    simp only [last,Fin.val_last,inv_neg,inv_one,Units.val_neg,Units.val_one]
    rw [show (-1:F)^j.rev.val*(-g first j)*(-1:F)^(k+1)=
      ((-1:F)^j.rev.val*(-1:F)^(k+1))*(-g first j) by ring,reflected_sign,pow_succ]
    ring
private theorem diagonal_mem (a : Fin (k+2) → Fˣ)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g) :
    InRadical ((unitOdd% diagonalAut) a g) := by
  refine ⟨(unitOdd% diagonal_depth) a 1 g hg.1,?_⟩
  intro i j hi hj
  rw [(unitOdd% diagonal_entry),hg.2 i j hi hj]
  by_cases he : i=j
  · subst j; simp [Matrix.one_apply,mul_assoc]
  · simp [Matrix.one_apply,he]
private theorem field_mem (phi : RingAut F)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g) :
    InRadical (fieldAut phi g) := by
  refine ⟨(unitOdd% field_depth) phi 1 g hg.1,?_⟩
  intro i j hi hj
  change phi (g i j)=(1:Matrix (Fin (k+2)) (Fin (k+2)) F) i j
  rw [hg.2 i j hi hj]
  simp [Matrix.one_apply]
private theorem graph_mem (g : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (hg : InRadical g) : InRadical (positiveGraph g) := by
  have hgi := actual_radical_inverse_mem g hg
  refine ⟨?_,?_⟩
  · change LayerDepth 1 ((heightTorus (-1:Fˣ) ((unitAction% rawGraph) g)).val-1)
    exact (unitAction% torus_depth) (-1:Fˣ) 1 ((unitAction% rawGraph) g) ((unitAction% rawGraph_depth) g hg.1)
  · intro i j hi hj
    change heightTorus (-1:Fˣ) ((unitAction% rawGraph) g) i j=_
    rw [(unitAction% torus_entry),(unitAction% rawGraph_entry),
      hgi.2 j.rev i.rev (rev_ne_first hj) (rev_ne_last hi)]
    by_cases he : i=j
    · subst j
      simp only [Matrix.one_apply,ite_true,mul_one]
      rw [← mul_pow]; simp
    · have hne : j.rev≠i.rev := by
        intro h; have hh := congrArg Fin.rev h
        exact he (by simpa only [Fin.rev_rev] using hh.symm)
      simp [Matrix.one_apply,he,hne]
theorem actual_diagonal_field_graph_radical_mem (a : Fin (k+2) → Fˣ)
    (phi : RingAut F) (eps : Bool) (g : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (hg : InRadical g) : InRadical (PartIIProposition6_5.diagonalFieldGraph a phi eps g) := by
  apply diagonal_mem
  cases eps
  · exact field_mem phi g hg
  · exact field_mem phi _ (graph_mem g hg)
/-- Paired coordinates have the SAME sign even when the two directed
root entries are distinct; no inverse-transport assumption is made. -/
private theorem graph_pair (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    PartIIProposition6_5.diagonalFieldGraph a phi eps g first j=
      (a first:F)*(((a j)⁻¹:Fˣ):F)*
        (if eps then (-1:F)^(j.val+1)*phi (g j.rev last) else phi (g first j)) ∧
    PartIIProposition6_5.diagonalFieldGraph a phi eps g j.rev last=
      (a j.rev:F)*(((a last)⁻¹:Fˣ):F)*
        (if eps then (-1:F)^(j.val+1)*phi (g first j) else phi (g j.rev last)) := by
  have h := actual_positive_graph_radical_coordinates g hg j hj0 hjl
  cases eps <;> simp only [PartIIProposition6_5.diagonalFieldGraph,fieldGraphAut,Bool.false_eq_true,ite_false,ite_true,mul_one,MulAut.mul_apply]
  · constructor
    · rw [(unitOdd% diagonal_entry)]
      change (a first:F)*phi (g first j)*(((a j)⁻¹:Fˣ):F)=_
      ring
    · rw [(unitOdd% diagonal_entry)]
      change (a j.rev:F)*phi (g j.rev last)*(((a last)⁻¹:Fˣ):F)=_
      ring
  · constructor
    · rw [(unitOdd% diagonal_entry)]
      change (a first:F)*phi (positiveGraph g first j)*(((a j)⁻¹:Fˣ):F)=_
      rw [h.1,map_mul,map_pow,map_neg,map_one]; ring
    · rw [(unitOdd% diagonal_entry)]
      change (a j.rev:F)*phi (positiveGraph g j.rev last)*(((a last)⁻¹:Fˣ):F)=_
      rw [h.2,map_mul,map_pow,map_neg,map_one]; ring
/-- Actual square on every selected middle root pair. Hypotheses refer
to the concrete diagonal entries; they will be constructed by the
p263 determinant-one inner torus. -/
theorem actual_radical_middle_square (a : Fin (k+2) → Fˣ)
    (phi : RingAut F) (eps : Bool) (lambda : Fˣ)
    (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g)
    (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last)
    (hfirst : a first=lambda) (hlast : a last=lambda⁻¹)
    (hj : a j=1) (hjrev : a j.rev=1) :
    let beta := PartIIProposition6_5.diagonalFieldGraph a phi eps
    (beta^2) g first j=(lambda:F)*phi (lambda:F)*(phi^2) (g first j) ∧
      (beta^2) g j.rev last=(lambda:F)*phi (lambda:F)*(phi^2) (g j.rev last) := by
  dsimp only
  let beta := PartIIProposition6_5.diagonalFieldGraph a phi eps
  have hb := actual_diagonal_field_graph_radical_mem a phi eps g hg
  have h1 := graph_pair a phi eps g hg j hj0 hjl
  have h2 := graph_pair a phi eps (beta g) hb j hj0 hjl
  simp only [hfirst,hlast,hj,hjrev,inv_inv,inv_one,Units.val_one,mul_one,one_mul] at h1 h2
  have hs := sign_square (F:=F) (j.val+1)
  cases eps <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h1 h2
  all_goals
    rw [pow_two,MulAut.mul_apply]
    change beta (beta g) first j=_ ∧ beta (beta g) j.rev last=_
    rw [h2.1,h2.2,h1.1,h1.2]
    simp only [map_mul,map_pow,map_neg,map_one,pow_two,RingAut.mul_apply]
  · constructor <;> ring
  · constructor
    · calc
        _ = (lambda:F)*phi (lambda:F)*((-1:F)^(j.val+1)*(-1:F)^(j.val+1))*phi (phi (g first j)) := by ring
        _ = _ := by rw [hs]; ring
    · calc
        _ = (lambda:F)*phi (lambda:F)*((-1:F)^(j.val+1)*(-1:F)^(j.val+1))*phi (phi (g j.rev last)) := by ring
        _ = _ := by rw [hs]; ring
end NikolovSegal.PartIIRadicalActions
