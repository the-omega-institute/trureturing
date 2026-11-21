/- GID: D5/S3/Geometry/Hyperideal/DoubleStarNativeAllSlotsFast
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/DoubleStarNativeAllSlotsFast
   mirror-E: none(waiver:exact-local-real-inequalities)
   anchors: []
   utility: none
   digest: Exact local real inequalities for CFMP opposite-edge transitions; no global geometric realization claimed. -/

import D5.S3.Geometry.Hyperideal.DoubleStarNativeGram

set_option autoImplicit false

/-! Native Gram relabelling by finite vertex permutations, avoiding determinant expansion. -/
noncomputable section
namespace D5.S3.Geometry.Hyperideal.DoubleStarNativeAllSlotsFast

open D5.S3.Geometry.Hyperideal.DoubleStarBernstein
open D5.S3.Geometry.Hyperideal.DoubleStarOpposite
open D5.S3.Geometry.Hyperideal.DoubleStarNativeGram


open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

private theorem strict_of_native_negative (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o) (hc : 1 < c) (hd : 1 < d)
    (hneg : (gram r a b o c d).det < 0) :
    -1 < N r a b o c d / (Real.sqrt (D1 r a d)*Real.sqrt (D2 r b c)) ∧
    N r a b o c d / (Real.sqrt (D1 r a d)*Real.sqrt (D2 r b c)) < 1 := by
  obtain ⟨⟨h₁,h₂⟩,_,hh⟩ := original_cosine_interface r a b o c d hr ha hb ho hc hd
  let μ := Real.sqrt (D1 r a d)*Real.sqrt (D2 r b c)
  have hμ : 0 < μ := mul_pos (Real.sqrt_pos.mpr h₁) (Real.sqrt_pos.mpr h₂)
  have hμsq : μ^2 = D1 r a d * D2 r b c := by
    dsimp [μ]
    rw [mul_pow, Real.sq_sqrt h₁.le, Real.sq_sqrt h₂.le]
  have hsquare : |N r a b o c d|^2 < μ^2 := by
    rw [sq_abs, hμsq]
    linarith only [hh.mp hneg]
  obtain ⟨hlo,hhi⟩ := abs_lt.mp ((sq_lt_sq₀ (abs_nonneg _) hμ.le).mp hsquare)
  exact ⟨(lt_div_iff₀ hμ).mpr (by simpa only [neg_one_mul] using hlo),
      (div_lt_iff₀ hμ).mpr (by simpa only [one_mul] using hhi)⟩

private def perm0 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv := by decide
  right_inv := by decide

private theorem det_perm0 (r a b o c d : ℝ) :
    (gram a r b c o d).det = (gram r a b o c d).det := by
  have h : gram a r b c o d = (gram r a b o c d).submatrix perm0 perm0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_submatrix_equiv_self]

private def perm1 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv := by decide
  right_inv := by decide

private theorem det_perm1 (r a b o c d : ℝ) :
    (gram b r a d o c).det = (gram r a b o c d).det := by
  have h : gram b r a d o c = (gram r a b o c d).submatrix perm1 perm1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_submatrix_equiv_self]

private def perm2 : Equiv.Perm (Fin 4) where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by decide
  right_inv := by decide

private theorem det_perm2 (r a b o c d : ℝ) :
    (gram o a d r c b).det = (gram r a b o c d).det := by
  have h : gram o a d r c b = (gram r a b o c d).submatrix perm2 perm2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_submatrix_equiv_self]

private def perm3 : Equiv.Perm (Fin 4) where
  toFun := ![1,3,0,2]
  invFun := ![2,0,3,1]
  left_inv := by decide
  right_inv := by decide

private theorem det_perm3 (r a b o c d : ℝ) :
    (gram c r d a o b).det = (gram r a b o c d).det := by
  have h : gram c r d a o b = (gram r a b o c d).submatrix perm3 perm3 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_submatrix_equiv_self]

private def perm4 : Equiv.Perm (Fin 4) where
  toFun := ![1,2,0,3]
  invFun := ![2,0,1,3]
  left_inv := by decide
  right_inv := by decide

private theorem det_perm4 (r a b o c d : ℝ) :
    (gram d r c b o a).det = (gram r a b o c d).det := by
  have h : gram d r c b o a = (gram r a b o c d).submatrix perm4 perm4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_submatrix_equiv_self]

/-- Each argument tuple targets one of the six original edges. -/
def nativeRaw (r a b o c d : ℝ) : ℝ :=
  N r a b o c d / (Real.sqrt (D1 r a d)*Real.sqrt (D2 r b c))

def nativeStrictSix (r a b o c d : ℝ) : Prop :=
  -1 < nativeRaw r a b o c d ∧ nativeRaw r a b o c d < 1 ∧
  -1 < nativeRaw a r b c o d ∧ nativeRaw a r b c o d < 1 ∧
  -1 < nativeRaw b r a d o c ∧ nativeRaw b r a d o c < 1 ∧
  -1 < nativeRaw o a d r c b ∧ nativeRaw o a d r c b < 1 ∧
  -1 < nativeRaw c r d a o b ∧ nativeRaw c r d a o b < 1 ∧
  -1 < nativeRaw d r c b o a ∧ nativeRaw d r c b o a < 1

theorem nativeStrictSix_of_det_neg (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o) (hc : 1 < c) (hd : 1 < d)
    (hn : (gram r a b o c d).det < 0) : nativeStrictSix r a b o c d := by
  have q₀ := strict_of_native_negative r a b o c d hr ha hb ho hc hd hn
  have q₁ := strict_of_native_negative a r b c o d ha hr hb hc ho hd (by rwa [det_perm0 r a b o c d])
  have q₂ := strict_of_native_negative b r a d o c hb hr ha hd ho hc (by rwa [det_perm1 r a b o c d])
  have q₃ := strict_of_native_negative o a d r c b ho ha hd hr hc hb (by rwa [det_perm2 r a b o c d])
  have q₄ := strict_of_native_negative c r d a o b hc hr hd ha ho hb (by rwa [det_perm3 r a b o c d])
  have q₅ := strict_of_native_negative d r c b o a hd hr hc hb ho ha (by rwa [det_perm4 r a b o c d])
  exact ⟨q₀.1,q₀.2,q₁.1,q₁.2,q₂.1,q₂.2,q₃.1,q₃.2,q₄.1,q₄.2,q₅.1,q₅.2⟩

theorem first_native_all_slots (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    nativeStrictSix x (101/100) 500 (chosenOpp x (101/100) (3/2) 500 (101/100))
      (101/100) (3/2) := by
  exact nativeStrictSix_of_det_neg _ _ _ _ _ _
    (by linarith only [hl]) (by norm_num) (by norm_num)
    (by linarith only [(first_exact x hl hu).1]) (by norm_num) (by norm_num)
    (first_native_gram_negative x hl hu)

theorem middle_native_all_slots (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    nativeStrictSix x 500 500 (chosenOpp x 500 (101/100) 500 (101/100))
      (101/100) (101/100) := by
  exact nativeStrictSix_of_det_neg _ _ _ _ _ _
    (by linarith only [hl]) (by norm_num) (by norm_num)
    (by linarith only [(middle_exact x hl hu).1]) (by norm_num) (by norm_num)
    (middle_native_gram_negative x hl hu)

theorem last_native_all_slots (x : ℝ) (hl : 12 ≤ x) (hu : x ≤ 20) :
    nativeStrictSix x 500 (101/100) (chosenOpp x 500 (101/100) (101/100) (101/100))
      (101/100) (101/100) := by
  exact nativeStrictSix_of_det_neg _ _ _ _ _ _
    (by linarith only [hl]) (by norm_num) (by norm_num)
    (by linarith only [(last_exact x hl hu).1]) (by norm_num) (by norm_num)
    (last_native_gram_negative x hl hu)


end D5.S3.Geometry.Hyperideal.DoubleStarNativeAllSlotsFast
