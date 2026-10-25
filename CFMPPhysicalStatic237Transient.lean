import CFMPOriginalSupportReadout232Transient
import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
import D5.S3.Geometry.Hyperideal.S4OppositePairAction
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalExteriorNativeNormal435Transient
open CFMPLorentzLiftSurface435Transient

namespace CFMPPhysicalStatic237Transient

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
def J : Mat := Matrix.diagonal ![1,1,1,-1]


def sideNormal (M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : W :=
  fun a => -(![(1 : ℝ),1,1,-1] a) * M⁻¹ a i

def rawNormal (M : Matrix (Fin 4) (Fin 4) ℝ) (cap : Bool) (i : Fin 4) : W :=
  if cap then M i else sideNormal M i

def readout (l : Fin 6 → ℝ) (cap : Bool) (i : Fin 4) (v : W) : ℝ :=
  if cap then ∑ j, lengthGram l i j * v j else -v i

def unitNormal (M : Matrix (Fin 4) (Fin 4) ℝ) (cap : Bool) (i : Fin 4) : W :=
  (Real.sqrt (lorentz (rawNormal M cap i) (rawNormal M cap i)))⁻¹ • rawNormal M cap i

theorem pairing_vecMul (M : Matrix (Fin 4) (Fin 4) ℝ) (v N : W) :
    lorentz (v ᵥ* M) N = ∑ j, v j * lorentz (M j) N := by
  simp [lorentz, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  ring

theorem pairing_smul (a b : ℝ) (X Y : W) :
    lorentz (a • X) (b • Y) = a*b*lorentz X Y := by
  simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
  ring

theorem sideNormal_pair (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (j i : Fin 4) : lorentz (M j) (sideNormal M i) = -(if j=i then 1 else 0) := by
  calc
    _ = -(M*M⁻¹) j i := by
      simp [lorentz,sideNormal,Matrix.mul_apply,Fin.sum_univ_four]
    _ = -(1 : Matrix (Fin 4) (Fin 4) ℝ) j i := by
      rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)]
    _ = _ := by simp [Matrix.one_apply]


theorem inverse_length_gram (l : Fin 6 → ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : M * J * M.transpose = lengthGram l) :
    (lengthGram l)⁻¹ = (M⁻¹).transpose * J * M⁻¹ := by
  have hJ : J * J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [J, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four]
  apply Matrix.inv_eq_left_inv
  calc
    _ = (M⁻¹).transpose * J * (M⁻¹ * M) * J * M.transpose := by
      rw [← hG]
      simp only [Matrix.mul_assoc]
    _ = (M⁻¹).transpose * M.transpose := by
      rw [Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.mul_one,
        Matrix.mul_assoc (M⁻¹).transpose J J, hJ, Matrix.mul_one]
    _ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv M
        (isUnit_iff_ne_zero.mpr hM), Matrix.transpose_one]

theorem raw_side_pair (l : Fin 6 → ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : M * J * M.transpose = lengthGram l) (i j : Fin 4) :
    lorentz (sideNormal M i) (sideNormal M j) = (lengthGram l)⁻¹ i j := by
  rw [inverse_length_gram l M hM hG]
  simp [sideNormal, lorentz, J, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Fin.sum_univ_four]

theorem unit_side_pair (l : Fin 6 → ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : M * J * M.transpose = lengthGram l) (i j : Fin 4) :
    lorentz (unitNormal M false i) (unitNormal M false j) =
      (lengthGram l)⁻¹ i j /
        (Real.sqrt ((lengthGram l)⁻¹ i i) * Real.sqrt ((lengthGram l)⁻¹ j j)) := by
  simp only [unitNormal, rawNormal, Bool.false_eq_true, ite_false]
  rw [pairing_smul, raw_side_pair l M hM hG i i,
    raw_side_pair l M hM hG j j, raw_side_pair l M hM hG i j]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


theorem original_gram_cofactors (r a b o c d : ℝ) :
    (gram r a b o c d).adjugate 2 2 = -D2 r b c ∧
    (gram r a b o c d).adjugate 3 3 = -D1 r a d ∧
    (gram r a b o c d).adjugate 2 3 = N r a b o c d := by
  constructor
  · norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,D2,
      Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,Matrix.det_fin_zero,
      Matrix.submatrix_apply,Fin.sum_univ_succ,Matrix.of_apply,
      Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
      Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
      Nat.succ_eq_add_one,Fin.castLE,Fin.cast]
    ring
  · constructor
    · norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,D1,
        Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,Matrix.det_fin_zero,
        Matrix.submatrix_apply,Fin.sum_univ_succ,Matrix.of_apply,
        Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
        Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
        Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
        Nat.succ_eq_add_one,Fin.castLE,Fin.cast]
      ring
    · norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,N,
        Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,Matrix.det_fin_zero,
        Matrix.submatrix_apply,Fin.sum_univ_succ,Matrix.of_apply,
        Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
        Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
        Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
        Nat.succ_eq_add_one,Fin.castLE,Fin.cast]
      ring

theorem inverse_gram_cosine (r a b o c d : ℝ)
    (h1 : 0 < D1 r a d) (h2 : 0 < D2 r b c)
    (hdet : (gram r a b o c d).det < 0) :
    -((gram r a b o c d)⁻¹ 2 3 /
      (Real.sqrt ((gram r a b o c d)⁻¹ 2 2)*
        Real.sqrt ((gram r a b o c d)⁻¹ 3 3))) = cosine r a b o c d := by
  let G := gram r a b o c d
  let delta := -G.det
  have hd : 0 < delta := neg_pos.mpr hdet
  have hi (i j : Fin 4) : G⁻¹ i j = G.adjugate i j/G.det := by
    rw [Matrix.inv_def]
    simp only [Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
    ring
  obtain ⟨h22,h33,h23⟩ := original_gram_cofactors r a b o c d
  have hi22 : G⁻¹ 2 2 = D2 r b c/delta := by rw [hi,h22];simp [delta, neg_div, div_neg]
  have hi33 : G⁻¹ 3 3 = D1 r a d/delta := by rw [hi,h33];simp [delta, neg_div, div_neg]
  have hi23 : G⁻¹ 2 3 = -N r a b o c d/delta := by rw [hi,h23];simp [delta]
  have hr1 : rad r a d = D1 r a d := by dsimp [rad,D1];ring
  have hr2 : rad r b c = D2 r b c := by dsimp [rad,D2];ring
  have hcos : cosine r a b o c d =
      N r a b o c d/(Real.sqrt (D1 r a d)*Real.sqrt (D2 r b c)) := by
    simp only [cosine,hr1,hr2,div_div]
    rfl
  change -(G⁻¹ 2 3/(Real.sqrt (G⁻¹ 2 2)*Real.sqrt (G⁻¹ 3 3))) = _
  rw [hi22,hi33,hi23,Real.sqrt_div h2.le,Real.sqrt_div h1.le,hcos]
  have hs1 : Real.sqrt (D1 r a d) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hs2 : Real.sqrt (D2 r b c) ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
  have hsd : Real.sqrt delta ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hsq : (Real.sqrt delta)^2 = delta := Real.sq_sqrt hd.le
  field_simp [hd.ne',hs1,hs2,hsd]
  <;> linear_combination (N r a b o c d)*hsq

theorem original_unit_side_cosine (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) :
    -lorentz (unitNormal M false 2) (unitNormal M false 3) =
      cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) := by
  have hmatrix : M * J * M.transpose = lengthGram l := by
    ext i j
    have h : (M * J * M.transpose) i j = lorentz (M i) (M j) := by
      simp [J,Matrix.mul_apply,Matrix.diagonal_apply,Matrix.transpose_apply,
        lorentz,Fin.sum_univ_four]
    exact h.trans (hG i j)
  have hJ : J.det = (-1 : ℝ) := by
    norm_num [J,Matrix.det_diagonal,Fin.prod_univ_four]
  have hdet : (lengthGram l).det < 0 := by
    have hid : (lengthGram l).det = -(M.det)^2 := by
      rw [← hmatrix,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hJ]
      ring
    rw [hid]
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero hM)
  have hg : lengthGram l = gram
      (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
      (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) := rfl
  have hcosh (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (hl k).ne'
  have hp := (original_cosine_interface
    (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
    (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5))
    (hcosh 0) (hcosh 1) (hcosh 2) (hcosh 3) (hcosh 4) (hcosh 5)).1
  rw [unit_side_pair l M hM hmatrix,hg]
  exact inverse_gram_cosine _ _ _ _ _ _ hp.1 hp.2 (hg ▸ hdet)


def relabel (x : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 4)) : Fin 6 → ℝ :=
  ![x (edgeIndex (σ 0) (σ 1)), x (edgeIndex (σ 0) (σ 2)),
    x (edgeIndex (σ 0) (σ 3)), x (edgeIndex (σ 2) (σ 3)),
    x (edgeIndex (σ 1) (σ 3)), x (edgeIndex (σ 1) (σ 2))]

theorem edgeIndex_symm (i j : Fin 4) : edgeIndex i j = edgeIndex j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem gram_relabel (x : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    (gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).submatrix σ σ =
      gram (relabel x σ 0) (relabel x σ 1) (relabel x σ 2)
        (relabel x σ 3) (relabel x σ 4) (relabel x σ 5) := by
  have entry (i j : Fin 4) : gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i j =
      if i = j then 1 else -x (edgeIndex i j) := by
    fin_cases i <;> fin_cases j <;> norm_num [gram,edgeIndex]
  ext i j
  rw [Matrix.submatrix_apply,entry]
  simp only [σ.injective.eq_iff]
  fin_cases i <;> fin_cases j <;>
    simp [gram,relabel,edgeIndex_symm] <;>
    exact congrArg x (edgeIndex_symm (σ 1) (σ 0))

theorem original_all_unit_side_cosines (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (σ : Equiv.Perm (Fin 4)) :
    let y := relabel (fun k => Real.cosh (l k)) σ;
    -lorentz (unitNormal M false (σ 2)) (unitNormal M false (σ 3)) =
      cosine (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) := by
  let x : Fin 6 → ℝ := fun k => Real.cosh (l k)
  let y := relabel x σ
  let G := lengthGram l
  have hmatrix : M * J * M.transpose = G := by
    ext i j
    have h : (M * J * M.transpose) i j = lorentz (M i) (M j) := by
      simp [J,Matrix.mul_apply,Matrix.diagonal_apply,Matrix.transpose_apply,
        lorentz,Fin.sum_univ_four]
    exact h.trans (hG i j)
  have hJ : J.det = (-1 : ℝ) := by
    norm_num [J,Matrix.det_diagonal,Fin.prod_univ_four]
  have hdet : G.det < 0 := by
    have hid : G.det = -(M.det)^2 := by
      rw [← hmatrix,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hJ]
      ring
    rw [hid]
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero hM)
  have hperm : G.submatrix σ σ = gram (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) :=
    gram_relabel x σ
  have hy (k : Fin 6) : 1 < y k := by
    fin_cases k <;> exact Real.one_lt_cosh.mpr (hl _).ne'
  have hpos := (original_cosine_interface _ _ _ _ _ _
    (hy 0) (hy 1) (hy 2) (hy 3) (hy 4) (hy 5)).1
  have hd : (gram (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)).det < 0 := by
    rw [← hperm,Matrix.det_submatrix_equiv_self]
    exact hdet
  have hinv : (gram (y 0) (y 1) (y 2) (y 3) (y 4) (y 5))⁻¹ =
      (G⁻¹).submatrix σ σ := by
    rw [← hperm,Matrix.inv_submatrix_equiv]
  have hc := inverse_gram_cosine _ _ _ _ _ _ hpos.1 hpos.2 hd
  rw [hinv] at hc
  change -lorentz (unitNormal M false (σ 2)) (unitNormal M false (σ 3)) = _
  rw [unit_side_pair l M hM hmatrix]
  exact hc


def scale (l : Fin 6 → ℝ) (n : Fin 20) : ℝ :=
  -|(edgeMatrix l n).det| / support l (facet n) (vertices l n 0)

def physicalRaw (M : Matrix (Fin 4) (Fin 4) ℝ) : Support → Fin 4 → ℝ
  | Sum.inl i => rawNormal M false i
  | Sum.inr i => rawNormal M true i

def physicalUnit (M : Matrix (Fin 4) (Fin 4) ℝ) : Support → Fin 4 → ℝ
  | Sum.inl i => unitNormal M false i
  | Sum.inr i => unitNormal M true i

theorem scale_positive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    0 < scale l n := by
  have hd := abs_pos.mpr (edgeMatrix_det_ne_zero l hl n)
  exact div_pos_of_neg_of_neg (by linarith) (support_at_origin_negative l hl n)


private theorem physical_raw_pair (l : Fin 6 → ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (F : Support) (j : Fin 4) :
    lorentz (M j) (physicalRaw M F) = support l F (Pi.single j 1) := by
  cases F with
  | inl i =>
    change lorentz (M j) (sideNormal M i) =
      support l (Sum.inl i) (Pi.single j 1)
    rw [sideNormal_pair M hM j i]
    simp [support, Pi.single_apply, eq_comm]
  | inr i =>
    change lorentz (M j) (M i) =
      support l (Sum.inr i) (Pi.single j 1)
    rw [lorentz_symm, hG]
    simp [support, Pi.single_apply]

private theorem lorentz_rows_ext (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : M.det ≠ 0) (X Y : Fin 4 → ℝ)
    (h : ∀ i, lorentz (M i) X = lorentz (M i) Y) : X = Y := by
  let sign : Fin 4 → ℝ := ![1,1,1,-1]
  have hm : M *ᵥ (sign * X) = M *ᵥ (sign * Y) := by
    ext i
    simpa [Matrix.mulVec, dotProduct, lorentz, sign, Fin.sum_univ_four] using h i
  have he := congrArg (fun v => M⁻¹ *ᵥ v) hm
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec,
    Matrix.one_mulVec] at he
  ext i
  have hi := congrFun he i
  fin_cases i <;> simpa [sign] using hi

theorem raw_eq_positive_scale (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (n : Fin 20) :
    raw l M n = scale l n • physicalRaw M (facet n) := by
  apply lorentz_rows_ext M hM
  intro j
  have hread := CFMPOriginalSupportReadout232Transient.covector_support_readout
    l hl n (Pi.single j 1) (by simp)
  have hpair := pair_raw l M hM n (Pi.single j 1)
  rw [Matrix.single_one_vecMul] at hpair
  calc
    _ = dotProduct (Pi.single j 1) (exteriorCovector l n) := hpair
    _ = scale l n * support l (facet n) (Pi.single j 1) := hread
    _ = lorentz (M j) (scale l n • physicalRaw M (facet n)) := by
      rw [← physical_raw_pair l M hM hG]
      simpa only [zero_smul, add_zero, zero_mul] using
        (lorentz_right (M j) (physicalRaw M (facet n))
          (physicalRaw M (facet n)) (scale l n) 0).symm

private theorem normalize_positive_scale (a : ℝ) (ha : 0 < a) (X : Fin 4 → ℝ) :
    (Real.sqrt (lorentz (a • X) (a • X)))⁻¹ • (a • X) =
      (Real.sqrt (lorentz X X))⁻¹ • X := by
  have hb : lorentz (a • X) (a • X) = a^2 * lorentz X X := by
    rw [pairing_smul, pow_two]
  have hs : Real.sqrt (a^2 * lorentz X X) = a * Real.sqrt (lorentz X X) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hb, hs, smul_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

theorem unit_eq_physical (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (n : Fin 20) :
    unit l M n = physicalUnit M (facet n) := by
  have he := raw_eq_positive_scale l hl M hM hG n
  unfold unit
  rw [he, normalize_positive_scale (scale l n) (scale_positive l hl n)]
  cases facet n <;> rfl



end CFMPPhysicalStatic237Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in #[``CFMPPhysicalStatic237Transient.original_all_unit_side_cosines,
      ``CFMPPhysicalStatic237Transient.unit_eq_physical] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP568 absent checked static root {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP568 disallowed axiom {ax} in {name}"
    Lean.logInfo m!"CFMP568 CHECKED {name} axioms={axioms}"
