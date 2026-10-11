/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalInnerTorus
set_option autoImplicit false
set_option maxHeartbeats 1800000
/-! Actual radical of the first-row/last-column parabolic, Part II pp262–263.
The corner is retained, including its ordered cross term. -/
namespace NikolovSegal.PartIIRadicalCoordinates
open PartIIUnitriangularLayers PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] {k : ℕ}
abbrev first : Fin (k+2) := 0
abbrev last : Fin (k+2) := Fin.last (k+1)
def EndpointZero (x : Fin (k+2) → F) : Prop := x first=0 ∧ x last=0
private theorem first_ne_last : (first : Fin (k+2)) ≠ last := by
  intro h; have h' := congrArg Fin.val h; simp only [first,last,Fin.val_zero,Fin.val_last] at h'; omega
private def radicalN (r c : Fin (k+2) → F) (z : F) : Matrix (Fin (k+2)) (Fin (k+2)) F :=
  fun i j => if i=first then (if j=last then z else r j) else if j=last then c i else 0
private theorem radicalN_upper (r c : Fin (k+2) → F) (hr : EndpointZero r)
    (hc : EndpointZero c) (z : F) : LayerDepth 1 (radicalN r c z) := by
  intro i j hij
  change j.val < i.val+1 at hij
  by_cases hi : i=first
  · subst i
    have hj : j=first := by
      apply Fin.ext
      change j.val=0
      change j.val < 0+1 at hij
      omega
    subst j
    simp [radicalN,first_ne_last,hr.1]
  · by_cases hj : j=last
    · subst j
      have hi' : i=last := by apply Fin.ext; change i.val=k+1; simp only [last,Fin.val_last] at hij; omega
      subst i
      simp [radicalN,Ne.symm first_ne_last,hc.2]
    · simp [radicalN,hi,hj]
private theorem radical_det (r c : Fin (k+2) → F) (hr : EndpointZero r)
    (hc : EndpointZero c) (z : F) : Matrix.det (1+radicalN r c z)=1 := by
  classical
  have hn := radicalN_upper r c hr hc z
  have ht : Matrix.IsUpperTriangular (1+radicalN r c z) := by
    intro i j hij
    have hne : i≠j := by intro h; subst j; exact lt_irrefl _ hij
    simp only [Matrix.add_apply,Matrix.one_apply,if_neg hne,zero_add]
    exact hn i j (by change j.val < i.val+1; change j.val < i.val at hij; omega)
  rw [Matrix.det_of_isUpperTriangular ht]
  apply Finset.prod_eq_one
  intro i hi
  rw [Matrix.add_apply,Matrix.one_apply,if_pos rfl,hn i i (by omega),add_zero]
/-- Genuine determinant-one radical matrix with all three coordinates. -/
def radical (r c : Fin (k+2) → F) (hr : EndpointZero r)
    (hc : EndpointZero c) (z : F) : Matrix.SpecialLinearGroup (Fin (k+2)) F :=
  ⟨1+radicalN r c z,radical_det r c hr hc z⟩
private theorem N_mul (r c r' c' : Fin (k+2) → F)
    (hr : EndpointZero r) (hc' : EndpointZero c') (z z' : F) :
    radicalN r c z*radicalN r' c' z'=
      radicalN (fun _ => 0) (fun _ => 0) (∑ t, r t*c' t) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i=first
  · subst i
    by_cases hj : j=last
    · subst j
      change (∑ t, radicalN r c z first t*radicalN r' c' z' t last)=_
      simp only [radicalN,ite_true]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases ht0 : t=first
      · subst t; simp [first_ne_last,hr.1]
      · by_cases htl : t=last
        · subst t; simp [Ne.symm first_ne_last,hr.2,hc'.2]
        · simp [ht0,htl]
    · have hs : ∀ t : Fin (k+2), radicalN r c z first t*radicalN r' c' z' t j=0 := by
        intro t
        by_cases ht : t=first
        · subst t; simp [radicalN,first_ne_last,hr.1]
        · simp [radicalN,ht,hj]
      rw [Finset.sum_eq_zero (fun t _ => hs t)]
      simp only [radicalN,ite_true,if_neg hj]
  · have hs : ∀ t : Fin (k+2), radicalN r c z i t*radicalN r' c' z' t j=0 := by
      intro t
      by_cases ht : t=last
      · subst t
        by_cases hj : j=last
        · subst j; simp [radicalN,hi,Ne.symm first_ne_last,hc'.2]
        · simp [radicalN,hi,Ne.symm first_ne_last,hj]
      · simp [radicalN,hi,ht]
    rw [Finset.sum_eq_zero (fun t _ => hs t)]
    simp only [radicalN,if_neg hi,ite_self]
private theorem endpoints_add {r r' : Fin (k+2) → F}
    (hr : EndpointZero r) (hr' : EndpointZero r') : EndpointZero (fun i => r i+r' i) := by
  exact ⟨by simp [hr.1,hr'.1],by simp [hr.2,hr'.2]⟩
private theorem endpoints_neg {r : Fin (k+2) → F}
    (hr : EndpointZero r) : EndpointZero (fun i => -r i) := by
  exact ⟨by simp [hr.1],by simp [hr.2]⟩
/-- Exact noncommutative radical multiplication: only the first row of
THE LEFT factor pairs with the last column of THE RIGHT factor. -/
theorem actual_radical_mul (r c r' c' : Fin (k+2) → F)
    (hr : EndpointZero r) (hc : EndpointZero c)
    (hr' : EndpointZero r') (hc' : EndpointZero c') (z z' : F) :
    radical r c hr hc z*radical r' c' hr' hc' z'=
      radical (fun i => r i+r' i) (fun i => c i+c' i)
        (endpoints_add hr hr') (endpoints_add hc hc') (z+z'+∑ t, r t*c' t) := by
  apply Subtype.ext
  change (1+radicalN r c z)*(1+radicalN r' c' z')=
    1+radicalN (fun i => r i+r' i) (fun i => c i+c' i) (z+z'+∑ t, r t*c' t)
  simp only [add_mul,mul_add,one_mul,mul_one]
  rw [N_mul r c r' c' hr hc' z z']
  ext i j
  simp only [Matrix.add_apply,radicalN]
  split_ifs <;> ring
private theorem radical_zero : radical (fun _ : Fin (k+2) => (0:F)) (fun _ => 0)
    ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ 0=1 := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  simp [radical,radicalN]
/-- Actual inverse, including the central quadratic correction. -/
theorem actual_radical_inverse (r c : Fin (k+2) → F)
    (hr : EndpointZero r) (hc : EndpointZero c) (z : F) :
    (radical r c hr hc z)⁻¹=
      radical (fun i => -r i) (fun i => -c i)
        (endpoints_neg hr) (endpoints_neg hc) (-z+∑ t, r t*c t) := by
  let a := radical r c hr hc z
  let b := radical (fun i => -r i) (fun i => -c i)
    (endpoints_neg hr) (endpoints_neg hc) (-z+∑ t, r t*c t)
  have hab : a*b=1 := by
    rw [actual_radical_mul]
    simp only [add_neg_cancel,mul_neg,Finset.sum_neg_distrib]
    have hz : z+(-z+∑ t, r t*c t)+ -(∑ t, r t*c t)=0 := by ring
    rw [hz]
    exact radical_zero
  change a⁻¹=b
  calc
    a⁻¹=a⁻¹*(a*b) := by rw [hab,mul_one]
    _ = b := by group
/-- Literal first-row/last-column subgroup predicate, with genuine
unitriangularity. This is not an abstract coverage assumption. -/
def InRadical (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) : Prop :=
  LayerDepth 1 (g.val-1) ∧ ∀ i j, i≠first → j≠last → g i j=(1:Matrix (Fin (k+2)) (Fin (k+2)) F) i j
theorem actual_radical_mem (r c : Fin (k+2) → F)
    (hr : EndpointZero r) (hc : EndpointZero c) (z : F) : InRadical (radical r c hr hc z) := by
  constructor
  · change LayerDepth 1 ((1+radicalN r c z)-1)
    rw [add_sub_cancel_left]
    exact radicalN_upper r c hr hc z
  · intro i j hi hj
    simp only [radical,Matrix.add_apply,radicalN,if_neg hi,if_neg hj,add_zero]
/-- Every actual radical target has these genuine matrix coordinates. -/
theorem actual_radical_coordinates (g : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (hg : InRadical g) :
    ∃ (r c : Fin (k+2) → F) (hr : EndpointZero r) (hc : EndpointZero c) (z : F),
      g=radical r c hr hc z := by
  classical
  let r : Fin (k+2) → F := fun j => if j=first ∨ j=last then 0 else g first j
  let c : Fin (k+2) → F := fun i => if i=first ∨ i=last then 0 else g i last
  have hr : EndpointZero r := ⟨by simp [r],by simp [r]⟩
  have hc : EndpointZero c := ⟨by simp [c],by simp [c]⟩
  refine ⟨r,c,hr,hc,g first last,?_⟩
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change g i j=(1:Matrix (Fin (k+2)) (Fin (k+2)) F) i j+radicalN r c (g first last) i j
  by_cases hi : i=first
  · subst i
    by_cases hj : j=last
    · subst j; simp [radicalN,Matrix.one_apply,first_ne_last]
    · by_cases hj0 : j=first
      · subst j
        have h := hg.1 first first (by omega)
        simp only [Matrix.sub_apply,Matrix.one_apply,ite_true] at h
        simp [radicalN,hj,r,sub_eq_zero.mp h]
      · have hne : (first : Fin (k+2))≠j := Ne.symm hj0
        simp [radicalN,hj,r,hj0,Matrix.one_apply,hne]
  · by_cases hj : j=last
    · subst j
      by_cases hil : i=last
      · subst i
        have h := hg.1 last last (by omega)
        simp only [Matrix.sub_apply,Matrix.one_apply,ite_true] at h
        simp [radicalN,hi,c,sub_eq_zero.mp h]
      · simp [radicalN,hi,c,hil,Matrix.one_apply]
    · simp only [radicalN,if_neg hi,if_neg hj,add_zero]
      exact hg.2 i j hi hj
/-- Actual noncorner first-row coordinate. -/
theorem actual_radical_row (r c : Fin (k+2) → F) (hr : EndpointZero r)
    (hc : EndpointZero c) (z : F) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    radical r c hr hc z first j=r j := by
  simp [radical,radicalN,Matrix.one_apply,Ne.symm hj0,hjl]
theorem actual_radical_column (r c : Fin (k+2) → F) (hr : EndpointZero r)
    (hc : EndpointZero c) (z : F) (i : Fin (k+2)) (hi0 : i≠first) (hil : i≠last) :
    radical r c hr hc z i last=c i := by
  simp [radical,radicalN,Matrix.one_apply,hi0,hil]
theorem actual_radical_corner (r c : Fin (k+2) → F) (hr : EndpointZero r)
    (hc : EndpointZero c) (z : F) : radical r c hr hc z first last=z := by
  simp [radical,radicalN,Matrix.one_apply,first_ne_last]
/-- Closure is proved for the literal matrix support, not postulated. -/
theorem actual_radical_product_mem (a b : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (ha : InRadical a) (hb : InRadical b) : InRadical (a*b) := by
  obtain ⟨r,c,hr,hc,z,rfl⟩ := actual_radical_coordinates a ha
  obtain ⟨r',c',hr',hc',z',rfl⟩ := actual_radical_coordinates b hb
  rw [actual_radical_mul]
  exact actual_radical_mem _ _ _ _ _
theorem actual_radical_inverse_mem (a : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (ha : InRadical a) : InRadical a⁻¹ := by
  obtain ⟨r,c,hr,hc,z,rfl⟩ := actual_radical_coordinates a ha
  rw [actual_radical_inverse]
  exact actual_radical_mem _ _ _ _ _
/-- Exact additive quotient coordinates, while the corner still uses
actual_radical_mul's noncommutative cross term. -/
theorem actual_radical_product_row_column (a b : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (ha : InRadical a) (hb : InRadical b) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    (a*b) first j=a first j+b first j ∧ (a*b) j last=a j last+b j last := by
  obtain ⟨r,c,hr,hc,z,rfl⟩ := actual_radical_coordinates a ha
  obtain ⟨r',c',hr',hc',z',rfl⟩ := actual_radical_coordinates b hb
  rw [actual_radical_mul]
  simp only [actual_radical_row _ _ _ _ _ j hj0 hjl,actual_radical_column _ _ _ _ _ j hj0 hjl]
  trivial
theorem actual_radical_inverse_row_column (a : Matrix.SpecialLinearGroup (Fin (k+2)) F)
    (ha : InRadical a) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) :
    a⁻¹ first j= -a first j ∧ a⁻¹ j last= -a j last := by
  obtain ⟨r,c,hr,hc,z,rfl⟩ := actual_radical_coordinates a ha
  rw [actual_radical_inverse]
  simp only [actual_radical_row _ _ _ _ _ j hj0 hjl,actual_radical_column _ _ _ _ _ j hj0 hjl]
  trivial
end NikolovSegal.PartIIRadicalCoordinates
