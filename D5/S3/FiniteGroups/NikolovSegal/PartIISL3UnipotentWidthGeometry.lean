/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentStructure

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Actual SL3 row elimination and its literal lower-unipotent subgroup.
The accepted upper3 chart and subgroup are reused. No finiteness assumption. -/
namespace NikolovSegal.PartIISL3UnipotentWidth
open NikolovSegal.PartIIA2Orbital NikolovSegal.PartIISL3UnipotentSylow
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

/-- The actual lower chart is the transpose of the accepted upper chart. -/
def lower3 (a b c : F) : SL(3,F) := (upper3 a b c).transpose

private theorem transpose_mul (g h : SL(3,F)) :
    (g*h).transpose = h.transpose * g.transpose := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

private theorem transpose_inv (g : SL(3,F)) :
    g⁻¹.transpose = g.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul,mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one

/-- Literal lower unitriangular matrices, transported through actual transpose. -/
def lowerUnipotent : Subgroup SL(3,F) where
  carrier := {g | g.transpose ∈ upperUnipotent}
  one_mem' := by
    change (1 : SL(3,F)).transpose ∈ upperUnipotent
    have ht : (1 : SL(3,F)).transpose = 1 := Subtype.ext Matrix.transpose_one
    rw [ht]
    exact upperUnipotent.one_mem
  mul_mem' := by
    intro g h hg hh
    change (g*h).transpose ∈ upperUnipotent
    rw [transpose_mul]
    exact upperUnipotent.mul_mem hh hg
  inv_mem' := by
    intro g hg
    change g⁻¹.transpose ∈ upperUnipotent
    rw [transpose_inv]
    exact upperUnipotent.inv_mem hg

theorem lower3_mem (a b c : F) : lower3 a b c ∈ lowerUnipotent := by
  change (upper3 a b c).transpose.transpose ∈ upperUnipotent
  have ht : (upper3 a b c).transpose.transpose = upper3 a b c :=
    Subtype.ext (Matrix.transpose_transpose _)
  rw [ht]
  exact ⟨a,b,c,rfl⟩

theorem mem_lowerUnipotent_iff (g : SL(3,F)) :
    g ∈ lowerUnipotent ↔
      (∀ i j : Fin 3, i < j → g i j = 0) ∧ (∀ i : Fin 3, g i i = 1) := by
  change g.transpose ∈ U3 ↔ _
  rw [mem_U3_iff]
  constructor
  · rintro ⟨ht,hd⟩
    exact ⟨fun i j hij => ht j i hij,hd⟩
  · rintro ⟨ht,hd⟩
    exact ⟨fun i j hij => ht j i hij,hd⟩

/-- The actual upper-left SL2 block embedding into SL3. -/
def block01 : SL(2,F) →* SL(3,F) where
  toFun A := ⟨!![A 0 0,A 0 1,0; A 1 0,A 1 1,0; 0,0,1],by
    have h := A.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    apply Subtype.ext
    change (!![(A.val*B.val) 0 0,(A.val*B.val) 0 1,0;
      (A.val*B.val) 1 0,(A.val*B.val) 1 1,0;0,0,1] : Matrix (Fin 3) (Fin 3) F) =
      !![A 0 0,A 0 1,0;A 1 0,A 1 1,0;0,0,1] *
      !![B 0 0,B 0 1,0;B 1 0,B 1 1,0;0,0,1]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply,Fin.sum_univ_succ]

/-- The actual lower-right SL2 block embedding into SL3. -/
def block12 : SL(2,F) →* SL(3,F) where
  toFun A := ⟨!![1,0,0; 0,A 0 0,A 0 1; 0,A 1 0,A 1 1],by
    have h := A.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    apply Subtype.ext
    change (!![1,0,0;0,(A.val*B.val) 0 0,(A.val*B.val) 0 1;
      0,(A.val*B.val) 1 0,(A.val*B.val) 1 1] : Matrix (Fin 3) (Fin 3) F) =
      !![1,0,0;0,A 0 0,A 0 1;0,A 1 0,A 1 1] *
      !![1,0,0;0,B 0 0,B 0 1;0,B 1 0,B 1 1]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem block01_coe (A : SL(2,F)) :
    (block01 A).val = !![A 0 0,A 0 1,0;A 1 0,A 1 1,0;0,0,1] := rfl

@[simp] theorem block12_coe (A : SL(2,F)) :
    (block12 A).val = !![1,0,0;0,A 0 0,A 0 1;0,A 1 0,A 1 1] := rfl

theorem block01_upper (t : F) :
    block01 (transvection (show (0:Fin 2) ≠ 1 by decide) t) = upper3 t 0 0 := by
  apply Subtype.ext
  rw [block01_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe,upper3]

theorem block01_lower (t : F) :
    block01 (transvection (show (1:Fin 2) ≠ 0 by decide) t) = lower3 t 0 0 := by
  apply Subtype.ext
  rw [block01_coe]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [transvection_coe,lower3,upper3,
    Matrix.SpecialLinearGroup.transpose,Matrix.transpose_apply]

theorem block12_upper (t : F) :
    block12 (transvection (show (0:Fin 2) ≠ 1 by decide) t) = upper3 0 t 0 := by
  apply Subtype.ext
  rw [block12_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe,upper3]

theorem block12_lower (t : F) :
    block12 (transvection (show (1:Fin 2) ≠ 0 by decide) t) = lower3 0 t 0 := by
  apply Subtype.ext
  rw [block12_coe]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [transvection_coe,lower3,upper3,
    Matrix.SpecialLinearGroup.transpose,Matrix.transpose_apply]

private theorem upper_row (a b c : F) (g : SL(3,F)) (j : Fin 3) :
    (upper3 a b c * g) 0 j = g 0 j + a*g 1 j + c*g 2 j := by
  change ((upper3 a b c).val*g.val) 0 j = _
  simp [upper3,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

private theorem upper_row1 (a b c : F) (g : SL(3,F)) (j : Fin 3) :
    (upper3 a b c * g) 1 j = g 1 j + b*g 2 j := by
  change ((upper3 a b c).val*g.val) 1 j = _
  simp [upper3,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem upper_row2 (a b c : F) (g : SL(3,F)) (j : Fin 3) :
    (upper3 a b c * g) 2 j = g 2 j := by
  change ((upper3 a b c).val*g.val) 2 j = _
  simp [upper3,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem lower_row1 (a b c : F) (g : SL(3,F)) (j : Fin 3) :
    (lower3 a b c * g) 1 j = a*g 0 j + g 1 j := by
  change ((upper3 a b c).val.transpose*g.val) 1 j = _
  simp [upper3,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]

private theorem lower_row2 (a b c : F) (g : SL(3,F)) (j : Fin 3) :
    (lower3 a b c * g) 2 j = c*g 0 j + b*g 1 j + g 2 j := by
  change ((upper3 a b c).val.transpose*g.val) 2 j = _
  simp [upper3,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]
  ring

/-- A genuine first pivot using at most one upper-unitriangular row addition. -/
theorem first_pivot (g : SL(3,F)) :
    ∃ a c : F, (upper3 a 0 c * g) 0 0 ≠ 0 := by
  by_cases h00 : g 0 0 ≠ 0
  · exact ⟨0,0,by simpa [upper_row] using h00⟩
  have h00z : g 0 0 = 0 := not_ne_iff.mp h00
  by_cases h10 : g 1 0 ≠ 0
  · exact ⟨1,0,by simpa [upper_row,h00z] using h10⟩
  have h20 : g 2 0 ≠ 0 := by
    intro h20
    have hd := g.property
    rw [Matrix.det_fin_three] at hd
    simp [h00z,not_ne_iff.mp h10,h20] at hd
  exact ⟨0,1,by simpa [upper_row,h00z] using h20⟩

/-- Four alternating actual row operations make any SL3 matrix upper triangular. -/
theorem eliminate_to_upper (g : SL(3,F)) :
    ∃ v₀ v₁ v₂ v₃ : SL(3,F),
      v₀ ∈ upperUnipotent ∧ v₁ ∈ lowerUnipotent ∧
      v₂ ∈ upperUnipotent ∧ v₃ ∈ lowerUnipotent ∧
      ∀ i j : Fin 3, j < i → (v₃*(v₂*(v₁*(v₀*g)))) i j = 0 := by
  classical
  obtain ⟨a,c,hpivot⟩ := first_pivot g
  let v₀ := upper3 a 0 c
  let A := v₀*g
  have hA : A 0 0 ≠ 0 := hpivot
  let v₁ := lower3 (-A 1 0/A 0 0) 0 (-A 2 0/A 0 0)
  let B := v₁*A
  have hB10 : B 1 0 = 0 := by
    rw [show B = v₁*A from rfl,lower_row1]
    simp [hA]
  have hB20 : B 2 0 = 0 := by
    rw [show B = v₁*A from rfl,lower_row2]
    simp [hA]
  have hp : B 1 1 ≠ 0 ∨ B 2 1 ≠ 0 := by
    by_contra hn
    have hz := not_or.mp hn
    have hd := B.property
    rw [Matrix.det_fin_three] at hd
    simp [hB10,hB20,not_ne_iff.mp hz.1,
      not_ne_iff.mp hz.2] at hd
  let b : F := if B 1 1 = 0 then 1 else 0
  let v₂ := upper3 0 b 0
  let C := v₂*B
  have hC11 : C 1 1 ≠ 0 := by
    rcases hp with hp | hp
    · simpa [C,v₂,upper_row1,b,hp] using hp
    · by_cases h : B 1 1 = 0
      · simpa [C,v₂,upper_row1,b,h] using hp
      · simpa [C,v₂,upper_row1,b,h] using h
  have hC10 : C 1 0 = 0 := by simp [C,v₂,upper_row1,hB10,hB20]
  have hC20 : C 2 0 = 0 := by simp [C,v₂,upper_row2,hB20]
  let v₃ := lower3 0 (-C 2 1/C 1 1) 0
  let D := v₃*C
  have hD10 : D 1 0 = 0 := by simp [D,v₃,lower_row1,hC10]
  have hD20 : D 2 0 = 0 := by simp [D,v₃,lower_row2,hC10,hC20]
  have hD21 : D 2 1 = 0 := by simp [D,v₃,lower_row2,hC11]
  refine ⟨v₀,v₁,v₂,v₃,⟨a,0,c,rfl⟩,lower3_mem _ _ _,⟨0,b,0,rfl⟩,
    lower3_mem _ _ _,?_⟩
  change ∀ i j : Fin 3, j < i → D i j = 0
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end NikolovSegal.PartIISL3UnipotentWidth
