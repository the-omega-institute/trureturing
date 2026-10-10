/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthLeviGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthLeviGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthEndpointStabilizer
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryLeviDecomposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! Actual central SU and its two endpoint radicals. All support conditions
are literal entries. The accepted central SL embedding is used unchanged. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow PartIIUnitaryUpperTorus PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

abbrev leftEnd : Fin (n+2) := 0
abbrev rightEnd : Fin (n+2) := Fin.last (n+1)
abbrev mid (i : Fin n) : Fin (n+2) := PartIICentralLevi.middle i

theorem left_ne_right : (leftEnd : Fin (n+2))≠rightEnd := by
  intro he; have hh := congrArg Fin.val he; simp [leftEnd,rightEnd] at hh

theorem mid_ne_left (i : Fin n) : mid i≠(leftEnd : Fin (n+2)) := by
  intro he; have hh := congrArg Fin.val he
  simp only [mid,PartIICentralLevi.middle,Fin.val_succ,Fin.val_castSucc,leftEnd,Fin.val_zero] at hh
  omega

theorem mid_ne_right (i : Fin n) : mid i≠(rightEnd : Fin (n+2)) := by
  intro he; have hh := congrArg Fin.val he
  simp only [mid,PartIICentralLevi.middle,Fin.val_succ,Fin.val_castSucc,rightEnd,Fin.val_last] at hh
  omega

theorem mid_injective : Function.Injective (mid (n:=n)) := by
  intro i j he; apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [mid,PartIICentralLevi.middle,Fin.val_succ,Fin.val_castSucc] at hh; omega

theorem interior_eq_mid {i : Fin (n+2)} (hi0 : i≠leftEnd) (hiL : i≠rightEnd) :
    ∃ j : Fin n, mid j=i := by
  have h0 : 0 < i.val := by
    have hh : i.val≠0 := fun he => hi0 (Fin.ext he); omega
  have hL : i.val < n+1 := by
    have hh : i.val≠n+1 := fun he => hiL (Fin.ext he); omega
  refine ⟨⟨i.val-1,by omega⟩,?_⟩
  apply Fin.ext; simp [mid,PartIICentralLevi.middle]; omega

def Endpoints (g : SpecialLinearGroup (Fin (n+2)) F) : Prop :=
  (∀ i, g.val i leftEnd=(1:Matrix (Fin (n+2)) (Fin (n+2)) F) i leftEnd) ∧
  (∀ j, g.val rightEnd j=(1:Matrix (Fin (n+2)) (Fin (n+2)) F) rightEnd j)

@[simp] theorem endpoints_one : Endpoints (1 : SpecialLinearGroup (Fin (n+2)) F) := by
  constructor <;> intro i <;> rfl

theorem endpoints_mul {g h : SpecialLinearGroup (Fin (n+2)) F}
    (hg : Endpoints g) (hh : Endpoints h) : Endpoints (g*h) := by
  constructor
  · intro i
    change (∑ t, g.val i t*h.val t leftEnd)=_
    simp only [hh.1,Matrix.one_apply,mul_ite,mul_one,mul_zero]
    simpa [Matrix.one_apply] using hg.1 i
  · intro j
    change (∑ t, g.val rightEnd t*h.val t j)=_
    simp only [hg.2,Matrix.one_apply,ite_mul,one_mul,zero_mul]
    simpa [Matrix.one_apply] using hh.2 j

theorem endpoints_inv {g : SpecialLinearGroup (Fin (n+2)) F}
    (hg : Endpoints g) : Endpoints g⁻¹ := by
  constructor
  · intro i
    have he := congrArg (fun A : SpecialLinearGroup (Fin (n+2)) F => A i leftEnd)
      (inv_mul_cancel g)
    change (∑ t, (g⁻¹).val i t*g.val t leftEnd)=_ at he
    simp only [hg.1,Matrix.one_apply,mul_ite,mul_one,mul_zero] at he
    simpa [Matrix.one_apply] using he
  · intro j
    have he := congrArg (fun A : SpecialLinearGroup (Fin (n+2)) F => A rightEnd j)
      (mul_inv_cancel g)
    change (∑ t, g.val rightEnd t*(g⁻¹).val t j)=_ at he
    simp only [hg.2,Matrix.one_apply,ite_mul,one_mul,zero_mul] at he
    simpa [Matrix.one_apply] using he

/-- Middle blocks multiply on the actual two-endpoint stabilizer. -/
theorem middle_product {g h : SpecialLinearGroup (Fin (n+2)) F}
    (hg : Endpoints g) (hh : Endpoints h) :
    (g*h).val.submatrix mid mid=g.val.submatrix mid mid*h.val.submatrix mid mid := by
  ext i j
  rw [Matrix.submatrix_apply,SpecialLinearGroup.coe_mul,Matrix.mul_apply,
    Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  change g.val (mid i) leftEnd*h.val leftEnd (mid j)+
    ((∑ t : Fin n, g.val (mid i) (mid t)*h.val (mid t) (mid j))+
      g.val (mid i) rightEnd*h.val rightEnd (mid j))=_
  rw [hg.1,hh.2]
  simp only [Matrix.one_apply,if_neg (mid_ne_left i),if_neg (mid_ne_right j).symm,
    zero_mul,mul_zero,zero_add,add_zero]
  rfl

def centralEmbed : specialUnitary n ι →* specialUnitary (n+2) ι where
  toFun g := ⟨PartIICentralLevi.embed g.val,by
    change steinberg ι (PartIICentralLevi.embed g.val)=PartIICentralLevi.embed g.val
    rw [PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,g.prop]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

theorem centralEmbed_entry (g : specialUnitary n ι)
    (i j : Fin 1 ⊕ (Fin n ⊕ Fin 1)) :
    (centralEmbed g).val.val ((centralKernel% indexEquiv) i) ((centralKernel% indexEquiv) j)=
      fromBlocks (1:Matrix (Fin 1) (Fin 1) F) 0 0 (fromBlocks g.val.val 0 0 (1:Matrix (Fin 1) (Fin 1) F)) i j :=
  (centralKernel% entry) g.val i j

theorem slCentral_endpoints (g : SpecialLinearGroup (Fin n) F) :
    Endpoints (PartIICentralLevi.embed g) := by
  have h1 : ∀ i : Fin 1, i=0 := fun i => Subsingleton.elim _ _
  constructor
  · intro i
    obtain ⟨i,rfl⟩ := (centralKernel% indexEquiv).surjective i
    simp only [leftEnd]
    rw [← centralKernel% index_first,centralKernel% entry]
    rcases i with i | (i | i)
    all_goals simp [h1,Matrix.fromBlocks,Matrix.one_apply,centralKernel% index_first,
      centralKernel% index_middle,centralKernel% index_last,
      Fin.ext_iff,PartIICentralLevi.middle,leftEnd,rightEnd]
    all_goals omega
  · intro j
    obtain ⟨j,rfl⟩ := (centralKernel% indexEquiv).surjective j
    simp only [rightEnd]
    rw [← centralKernel% index_last,centralKernel% entry]
    rcases j with j | (j | j)
    all_goals simp [h1,Matrix.fromBlocks,Matrix.one_apply,centralKernel% index_first,
      centralKernel% index_middle,centralKernel% index_last,
      Fin.ext_iff,PartIICentralLevi.middle,leftEnd,rightEnd]
    all_goals omega

theorem centralEmbed_endpoints (g : specialUnitary n ι) : Endpoints (centralEmbed g).val :=
  slCentral_endpoints g.val

@[simp] theorem slCentral_middle (g : SpecialLinearGroup (Fin n) F) :
    (PartIICentralLevi.embed g).val.submatrix mid mid=g.val := by
  ext i j
  exact PartIICentralLevi.actual_central_levi_middle_entry g i j

@[simp] theorem centralEmbed_middle (g : specialUnitary n ι) :
    (centralEmbed g).val.val.submatrix mid mid=g.val.val := by
  ext i j
  exact PartIICentralLevi.actual_central_levi_middle_entry g.val i j

abbrev UpRadical (g : specialUnitary (n+2) ι) : Prop := PartIIRadicalCoordinates.InRadical g.val
abbrev DownRadical (g : specialUnitary (n+2) ι) : Prop := UpRadical (transpose g)

theorem upRadical_positive {g : specialUnitary (n+2) ι} (hg : UpRadical g) : Positive g := hg.1

theorem downRadical_negative {g : specialUnitary (n+2) ι} (hg : DownRadical g) : Negative g :=
  (positive_transpose_iff g).mp hg.1

theorem upRadical_endpoints {g : specialUnitary (n+2) ι} (hg : UpRadical g) : Endpoints g.val := by
  constructor
  · intro i
    exact sub_eq_zero.mp (hg.1 i leftEnd (by simp [leftEnd]))
  · intro j
    exact sub_eq_zero.mp (hg.1 rightEnd j (by simp [rightEnd]; omega))

theorem upRadical_middle {g : specialUnitary (n+2) ι} (hg : UpRadical g) :
    g.val.val.submatrix mid mid=(1:Matrix (Fin n) (Fin n) F) := by
  ext i j
  rw [Matrix.submatrix_apply,hg.2 _ _ (mid_ne_left i) (mid_ne_right j)]
  simp only [Matrix.one_apply,mid_injective.eq_iff]

/-- Support recognition is proved from entries, not assumed as a group oracle. -/
theorem slRadical_of_endpoints_middle {g : SpecialLinearGroup (Fin (n+2)) F}
    (he : Endpoints g) (hm : g.val.submatrix mid mid=(1:Matrix (Fin n) (Fin n) F)) :
    PartIIRadicalCoordinates.InRadical g := by
  have hout : ∀ i j : Fin (n+2), i≠leftEnd → j≠rightEnd →
      g.val i j=(1:Matrix (Fin (n+2)) (Fin (n+2)) F) i j := by
    intro i j hi hj
    by_cases hiL : i=rightEnd
    · subst i; exact he.2 j
    by_cases hj0 : j=leftEnd
    · subst j; exact he.1 i
    obtain ⟨i,rfl⟩ := interior_eq_mid hi hiL
    obtain ⟨j,rfl⟩ := interior_eq_mid hj0 hj
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) F => A i j) hm
    simpa only [Matrix.submatrix_apply,Matrix.one_apply,mid_injective.eq_iff] using h
  refine ⟨?_,hout⟩
  intro i j hij
  by_cases hi : i=leftEnd
  · subst i
    have hj : j=leftEnd := by
      apply Fin.ext; change j.val=0; change j.val < 0+1 at hij; omega
    subst j
    exact sub_eq_zero.mpr (he.1 leftEnd)
  by_cases hj : j=rightEnd
  · subst j
    have hi : i=rightEnd := by
      apply Fin.ext; change i.val=n+1; change n+1 < i.val+1 at hij; omega
    subst i
    exact sub_eq_zero.mpr (he.2 rightEnd)
  exact sub_eq_zero.mpr (hout i j hi hj)

theorem upRadical_of_endpoints_middle {g : specialUnitary (n+2) ι}
    (he : Endpoints g.val) (hm : g.val.val.submatrix mid mid=(1:Matrix (Fin n) (Fin n) F)) :
    UpRadical g := slRadical_of_endpoints_middle he hm

/-- Arbitrary actual central SU conjugation preserves the genuine upper radical. -/
theorem central_conjugate_upRadical (b : specialUnitary n ι)
    {g : specialUnitary (n+2) ι} (hg : UpRadical g) :
    UpRadical (centralEmbed b*g*(centralEmbed b)⁻¹) := by
  have hb := centralEmbed_endpoints b
  have hgE := upRadical_endpoints hg
  refine upRadical_of_endpoints_middle
    (endpoints_mul (endpoints_mul hb hgE) (endpoints_inv hb)) ?_
  change ((centralEmbed b).val*g.val*(centralEmbed b).val⁻¹).val.submatrix mid mid=_
  rw [middle_product (endpoints_mul hb hgE) (endpoints_inv hb),middle_product hb hgE,
    upRadical_middle hg,centralEmbed_middle,Matrix.mul_one]
  change b.val.val*((PartIICentralLevi.embed b.val)⁻¹).val.submatrix mid mid=_
  rw [← map_inv,slCentral_middle]
  exact congrArg Subtype.val (mul_inv_cancel b.val)

end NikolovSegal.UnitaryWholeGroupWidth
