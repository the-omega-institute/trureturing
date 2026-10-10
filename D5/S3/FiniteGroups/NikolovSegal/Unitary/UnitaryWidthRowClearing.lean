/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRowClearing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthPivot
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthTranspose
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalTraceCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! Literal Hermitian last-row clearing. The constructed lower factor is the
transpose of the accepted actual trace-constrained radical, with corner
chosen from the target's proved isotropy rather than supplied as an oracle. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow PartIIUnitaryUpperTorus PartIIUnitriangularLayers
open PartIIRadicalCoordinates PartIIUnitaryRadicalTraceCoordinates
universe u
variable {F : Type u} [Field F] [Finite F] {k : ℕ} {ι : RingAut F}

abbrev middle (i : Fin (k+2)) : Fin (k+4) := i.castSucc.succ

private theorem middle_ne_first (i : Fin (k+2)) : middle i≠(first : Fin (k+4)) := by
  intro he; have hh := congrArg Fin.val he
  simp only [middle,Fin.val_succ,Fin.val_castSucc,first,Fin.val_zero] at hh; omega
private theorem middle_ne_last (i : Fin (k+2)) : middle i≠(last : Fin (k+4)) := by
  intro he; have hh := congrArg Fin.val he
  simp only [middle,Fin.val_succ,Fin.val_castSucc,last,Fin.val_last] at hh; omega
private theorem middle_inj : Function.Injective (middle (k:=k)) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [middle,Fin.val_succ,Fin.val_castSucc] at hh; omega
private theorem rev_interior {i : Fin (k+4)} (hi0 : i≠first) (hiL : i≠last) :
    i.rev≠first ∧ i.rev≠last := by
  constructor
  · intro he; apply hiL
    have hh := congrArg Fin.rev he; simpa using hh
  · intro he; apply hi0
    have hh := congrArg Fin.rev he; simpa using hh

/-- A unit last pivot permits one genuine lower-SU operation to clear the
entire last row. The central quadratic corner is retained in every characteristic. -/
theorem clear_last_row (hinv : Function.Involutive ι)
    (g : specialUnitary (k+4) ι) (hb : g.val.val last last=1) :
    ∃ l : specialUnitary (k+4) ι, Negative l ∧
      ∀ j : Fin (k+4), (g*l).val.val last j=(1:Matrix (Fin (k+4)) (Fin (k+4)) F) last j := by
  classical
  let w := fun i : Fin (k+4) => g.val.val last i
  let r := fun i : Fin (k+4) => if i=first ∨ i=last then 0 else ι (w i.rev)
  let c := fun i : Fin (k+4) => if i=first ∨ i=last then 0 else -w i
  have hr : EndpointZero r := ⟨by simp [r],by simp [r]⟩
  have hc : EndpointZero c := ⟨by simp [c],by simp [c]⟩
  have hrc : ∀ i, c i= -ι (r i.rev) := by
    intro i
    by_cases hi0 : i=first
    · subst i; simp [r,c]
    by_cases hiL : i=last
    · subst i; simp [r,c]
    have hir := rev_interior hi0 hiL
    simp only [r,c,if_neg (not_or.mpr ⟨hi0,hiL⟩),
      if_neg (not_or.mpr hir),Fin.rev_rev]
    rw [hinv]
  have hm : ∀ i : Fin (k+2), r (middle i)=ι (w (middle i).rev) ∧ c (middle i)= -w (middle i) := by
    intro i
    simp [r,c,middle_ne_first,middle_ne_last]
  have hnorm : (∑ i : Fin (k+4), r i*ι (r i.rev))=
      ∑ i : Fin (k+2), w (middle i)*ι (w (middle i).rev) := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc]
    change r first*ι (r first.rev) + ((∑ i : Fin (k+2), r (middle i)*ι (r (middle i).rev))+
      r last*ι (r last.rev))=_
    rw [hr.1,hr.2,zero_mul,zero_mul,zero_add,add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hir := rev_interior (middle_ne_first i) (middle_ne_last i)
    rw [(hm i).1]
    simp only [r,if_neg (not_or.mpr hir),Fin.rev_rev]
    rw [hinv]
    ring
  have hiso : w first + (∑ i : Fin (k+2), w (middle i)*ι (w (middle i).rev))+ι (w first)=0 := by
    have hh := row_isotropic hinv g (last : Fin (k+4)) (by simp [first_ne_last])
    rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc] at hh
    change w first*ι (w first.rev)+((∑ i : Fin (k+2), w (middle i)*ι (w (middle i).rev))+
      w last*ι (w last.rev))=0 at hh
    have hwL : w last=1 := hb
    simpa only [rev_first,rev_last,hwL,map_one,mul_one,one_mul,add_assoc] using hh
  let z := ι (w first)
  have hz : z+ι z= -(∑ i : Fin (k+4), r i*ι (r i.rev)) := by
    dsimp only [z]
    rw [hnorm,hinv]
    linear_combination hiso
  let v : specialUnitary (k+4) ι :=
    ⟨radical r c hr hc z,actual_radical_unitary_of_trace ι hinv r c hr hc hrc z hz⟩
  have hv := actual_radical_mem r c hr hc z
  have hvU : Positive v := hv.1
  let l := transpose v
  refine ⟨l,?_,?_⟩
  · exact (positive_transpose_iff l).mp (by simpa [l] using hvU)
  intro j
  by_cases hj0 : j=first
  · subst j
    change (g.val.val*(v.val.val).transpose) last first=_
    rw [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_castSucc]
    change w first*v.val.val first first +
      ((∑ i : Fin (k+2), w (middle i)*v.val.val first (middle i))+w last*v.val.val first last)=_
    have hd : v.val.val first first=1 := by
      have hh := hv.1 first first (by omega)
      exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true] using hh)
    rw [hd]
    have hrow : ∀ i : Fin (k+2), v.val.val first (middle i)=r (middle i) := by
      intro i
      exact actual_radical_row r c hr hc z _ (middle_ne_first i) (middle_ne_last i)
    simp only [hrow,mul_one]
    rw [actual_radical_corner]
    have hs : (∑ i : Fin (k+2), w (middle i)*r (middle i))=
        ∑ i : Fin (k+2), w (middle i)*ι (w (middle i).rev) := by
      apply Finset.sum_congr rfl; intro i hi; rw [(hm i).1]
    rw [hs,show w last=1 from hb,one_mul]
    simpa [z,Matrix.one_apply,first_ne_last,add_assoc] using hiso
  by_cases hjL : j=last
  · subst j
    have hrow : ∀ t : Fin (k+4), v.val.val last t=(1:Matrix (Fin (k+4)) (Fin (k+4)) F) last t := by
      intro t
      exact sub_eq_zero.mp (hv.1 last t (by simp [last]; omega))
    change (g.val.val*v.val.val.transpose) last last=_
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply,hrow,Matrix.one_apply]
    simpa using hb
  have h0 : 0<j.val := by
    have hh : j.val≠0 := fun he => hj0 (Fin.ext he)
    omega
  have hL : j.val<k+3 := by
    have hh : j.val≠k+3 := fun he => hjL (Fin.ext he)
    omega
  let j' : Fin (k+2) := ⟨j.val-1,by omega⟩
  have hj : middle j'=j := by apply Fin.ext; simp [j',middle]; omega
  rw [← hj]
  change (g.val.val*v.val.val.transpose) last (middle j')=_
  rw [Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  change w first*v.val.val (middle j') first +
    ((∑ i : Fin (k+2), w (middle i)*v.val.val (middle j') (middle i))+
      w last*v.val.val (middle j') last)=_
  have hstart : v.val.val (middle j') first=0 := by
    rw [hv.2 _ _ (middle_ne_first j') first_ne_last]
    simp [Matrix.one_apply,middle_ne_first]
  have hmid : ∀ i : Fin (k+2), v.val.val (middle j') (middle i)=if j'=i then 1 else 0 := by
    intro i
    rw [hv.2 _ _ (middle_ne_first j') (middle_ne_last i)]
    simp [Matrix.one_apply,middle_inj.eq_iff]
  rw [hstart,mul_zero,zero_add]
  simp only [hmid]
  rw [actual_radical_column _ _ _ _ _ _ (middle_ne_first j') (middle_ne_last j'),(hm j').2]
  rw [Matrix.one_apply,if_neg (middle_ne_last j').symm]
  simp [show w last=1 from hb,eq_comm]

/-- Four alternating actual SU operations put any target into the genuine
last-row stabilizer, uniformly in rank and field. -/
theorem last_row_reduction (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary (k+4) ι) :
    ∃ u l v m : specialUnitary (k+4) ι,
      Positive u ∧ Negative l ∧ Positive v ∧ Negative m ∧
      ∀ j : Fin (k+4), (g*u*l*v*m).val.val last j=(1:Matrix (Fin (k+4)) (Fin (k+4)) F) last j := by
  obtain ⟨u,l,v,hu,hl,hv,hpivot⟩ := unit_last_pivot hinv hne g
  obtain ⟨m,hm,hrow⟩ := clear_last_row hinv (g*u*l*v) hpivot
  exact ⟨u,l,v,m,hu,hl,hv,hm,hrow⟩

end NikolovSegal.UnitaryWholeGroupWidth
