/- GID: D5/S3/Observer/CubicGain/LiteralSylvesterBounds
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/LiteralSylvesterBounds
   mirror-E: none(waiver:literal-elimination-continuation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Observer/CubicGain/LiteralSylvesterBounds.literal_elimination_exact_degrees; premises=D5/S3/Observer/CubicGain/LiteralLeadingCertificates.leading_determinants_ne_zero
   digest: Weighted degree bounds for the original fixed Sylvester and linear-minor determinants. -/

import D5.S3.Observer.CubicGain.LiteralElimination
import Mathlib.LinearAlgebra.Matrix.Polynomial
import D5.S3.Observer.CubicGain.LiteralLeadingCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 150000
set_option maxHeartbeats 4000000
noncomputable section

namespace D5.S3.Observer.CubicGain.LiteralSylvesterBounds

open Polynomial
open scoped BigOperators
open D5.S3.Observer.CubicGain.SelectedRootCommonZero
open D5.S3.Observer.CubicGain.ActualMinorLift
open D5.S3.Observer.CubicGain.LiteralElimination
open D5.S3.Observer.CubicGain.LiteralLeadingCertificates

/-- The coefficient ring is Z[b]; the outer polynomial variable is the original r. -/
def sourcePolynomial (i : Fin 3) : Polynomial (Polynomial ℤ) :=
  ![sourceE0 (X : Polynomial ℤ),sourceE1 (X : Polynomial ℤ),sourceE2 (X : Polynomial ℤ)] i

/-- All thirty rows in the original descending-shift order, independent of specialized degree. -/
def sylvesterRow (k : Fin 2) (i : Fin 30) : Polynomial (Polynomial ℤ) :=
  if i.val < 15 then X^(14-i.val)*sourcePolynomial 0
  else X^(29-i.val)*sourcePolynomial k.succ

/-- Columns are r^29,...,1; k=0 gives R1 and k=1 gives R2. -/
def literalSylvester (k : Fin 2) : Matrix (Fin 30) (Fin 30) (Polynomial ℤ) :=
  fun i j => (sylvesterRow k i).coeff (29-j.val)

def actualResultant (k : Fin 2) : Polynomial ℤ := (literalSylvester k).det

private theorem source_r_degree (i : Fin 3) : (sourcePolynomial i).natDegree ≤ 15 := by
  fin_cases i
  · change (sourceE0 (X : Polynomial ℤ)).natDegree ≤ 15
    unfold sourceE0
    compute_degree!
  · change (sourceE1 (X : Polynomial ℤ)).natDegree ≤ 15
    unfold sourceE1
    compute_degree!
  · change (sourceE2 (X : Polynomial ℤ)).natDegree ≤ 15
    unfold sourceE2
    compute_degree!

private def MonomialBound (p : Polynomial (Polynomial ℤ)) (N : ℕ) : Prop :=
  ∀ j k, (p.coeff j).coeff k ≠ 0 → j+k ≤ N

private theorem monomial_bound_add {p q : Polynomial (Polynomial ℤ)} {N : ℕ}
    (hp : MonomialBound p N) (hq : MonomialBound q N) : MonomialBound (p+q) N := by
  intro j k h
  by_cases hz : (p.coeff j).coeff k = 0
  · apply hq j k
    simpa only [coeff_add,hz,zero_add] using h
  · exact hp j k hz

private theorem monomial_bound_term (q : Polynomial ℤ) (a N : ℕ)
    (ha : a ≤ N) (hq : q.natDegree ≤ N-a) : MonomialBound (C q*X^a) N := by
  intro j k hk
  rw [coeff_C_mul_X_pow] at hk
  split_ifs at hk with hj
  · subst j
    have hh := le_natDegree_of_ne_zero hk
    omega
  · exact (hk rfl).elim

private theorem source_monomial_bound (i : Fin 3) : MonomialBound (sourcePolynomial i) 17 := by
  fin_cases i
  · change MonomialBound (sourceE0 (X : Polynomial ℤ)) 17
    unfold sourceE0
    repeat' first
      | apply monomial_bound_add
      | (apply monomial_bound_term <;> first | norm_num | compute_degree!)
  · change MonomialBound (sourceE1 (X : Polynomial ℤ)) 17
    unfold sourceE1
    repeat' first
      | apply monomial_bound_add
      | (apply monomial_bound_term <;> first | norm_num | compute_degree!)
  · change MonomialBound (sourceE2 (X : Polynomial ℤ)) 17
    unfold sourceE2
    repeat' first
      | apply monomial_bound_add
      | (apply monomial_bound_term <;> first | norm_num | compute_degree!)

private theorem source_coefficient_weight (i : Fin 3) (j : ℕ)
    (hj : (sourcePolynomial i).coeff j ≠ 0) :
    ((sourcePolynomial i).coeff j).natDegree+j ≤ 17 := by
  have h := source_monomial_bound i j ((sourcePolynomial i).coeff j).natDegree
    (leadingCoeff_ne_zero.mpr hj)
  omega

private theorem shifted_coefficient_weight (i : Fin 3) (s c : ℕ)
    (hc : ((X^s*sourcePolynomial i).coeff c) ≠ 0) :
    ((X^s*sourcePolynomial i).coeff c).natDegree+c ≤ 17+s := by
  rw [coeff_X_pow_mul'] at hc ⊢
  split_ifs at hc ⊢ with hs
  · have h := source_coefficient_weight i (c-s) hc
    omega
  · exact (hc rfl).elim

private theorem weighted_det_bound {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial ℤ)) (alpha gamma : n → ℕ) (B : ℕ)
    (hbalance : (∑ i, alpha i) ≤ B+∑ j, gamma j)
    (hentry : ∀ i j, M i j ≠ 0 → (M i j).natDegree+gamma j ≤ alpha i) :
    M.det.natDegree ≤ B := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro sigma _
  apply (natDegree_smul_le _ _).trans
  by_cases hz : (∏ j, M (sigma j) j) = 0
  · simp [hz]
  · have hentries : ∀ j, M (sigma j) j ≠ 0 := by
      intro j hj
      exact hz (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      hentry (sigma j) j (hentries j))
    rw [Finset.sum_add_distrib, Equiv.sum_comp sigma alpha] at hsum
    have hprod := natDegree_prod_le Finset.univ (fun j => M (sigma j) j)
    omega

set_option backward.isDefEq.respectTransparency false in
private theorem uniform_top_coeff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial ℤ)) (K : ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ K) :
    M.det.coeff (Fintype.card n*K) = Matrix.det (fun i j => (M i j).coeff K : Matrix n n ℤ) := by
  classical
  calc
    M.det.coeff (Fintype.card n*K) =
        (∑ sigma : Equiv.Perm n, Equiv.Perm.sign sigma • ∏ i, M (sigma i) i).coeff
          (Fintype.card n*K) :=
      congrArg (fun p : Polynomial ℤ => p.coeff (Fintype.card n*K)) (Matrix.det_apply M)
    _ = ∑ sigma : Equiv.Perm n, Equiv.Perm.sign sigma • ∏ i, (M (sigma i) i).coeff K := by
      rw [finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro sigma _
      rw [coeff_smul]
      congr 1
      simpa using coeff_prod_of_natDegree_le Finset.univ
        (fun j => M (sigma j) j) K (fun j _ => h (sigma j) j)
    _ = _ := (Matrix.det_apply (Matrix.of (fun i j => (M i j).coeff K))).symm


private theorem weighted_top_coeff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial ℤ)) (alpha gamma : n → ℕ) (B K : ℕ)
    (ha : ∀ i, alpha i ≤ K)
    (hbalance : (∑ i, alpha i) = B+∑ j, gamma j)
    (hentry : ∀ i j, M i j ≠ 0 → (M i j).natDegree+gamma j ≤ alpha i) :
    M.det.coeff B =
      Matrix.det (fun i j => if gamma j ≤ alpha i then (M i j).coeff (alpha i-gamma j) else 0 :
        Matrix n n ℤ) := by
  classical
  let N : Matrix n n (Polynomial ℤ) :=
    fun i j => X^(K-alpha i)*(X^(gamma j)*M i j)
  have hN : ∀ i j, (N i j).natDegree ≤ K := by
    intro i j
    by_cases hz : M i j = 0
    · simp [N,hz]
    · have he := hentry i j hz
      have h1 := natDegree_mul_le (p := (X^(K-alpha i) : Polynomial ℤ))
        (q := X^(gamma j)*M i j)
      have h2 := natDegree_mul_le (p := (X^(gamma j) : Polynomial ℤ)) (q := M i j)
      simp only [natDegree_X_pow] at h1 h2
      have hai := ha i
      dsimp [N]
      omega
  have hsum : (∑ i, (K-alpha i))+(∑ j, gamma j)+B = Fintype.card n*K := by
    have h : (∑ i, (K-alpha i))+(∑ i, alpha i) = Fintype.card n*K := by
      calc
        _ = ∑ i, ((K-alpha i)+alpha i) := (Finset.sum_add_distrib).symm
        _ = ∑ _ : n, K := Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (ha i))
        _ = _ := by simp
    omega
  have hd : N.det = X^((∑ i, (K-alpha i))+(∑ j, gamma j))*M.det := by
    have hrow := Matrix.det_mul_column (fun i => (X^(K-alpha i) : Polynomial ℤ))
      (Matrix.of (fun i j => X^(gamma j)*M i j))
    have hcol := Matrix.det_mul_row (fun j => (X^(gamma j) : Polynomial ℤ)) M
    change N.det = _ at hrow
    rw [hrow,hcol]
    simp only [Finset.prod_pow_eq_pow_sum,← mul_assoc,← pow_add]
  have hc := uniform_top_coeff N K hN
  have hl : N.det.coeff (Fintype.card n*K) = M.det.coeff B := by
    rw [hd,← hsum,add_comm _ B,coeff_X_pow_mul]
  rw [hl] at hc
  rw [hc]
  congr 1
  ext i j
  change (X^(K-alpha i)*(X^(gamma j)*M i j)).coeff K = _
  rw [← mul_assoc,← pow_add,coeff_X_pow_mul']
  by_cases hga : gamma j ≤ alpha i
  · have hn : K-alpha i+gamma j ≤ K := by have hai := ha i; omega
    rw [ite_eq_left hn,ite_eq_left hga]
    congr 1
    have hai := ha i
    omega
  · have hn : ¬ K-alpha i+gamma j ≤ K := by have hai := ha i; omega
    rw [ite_eq_right hn,ite_eq_right hga]

private def sylvesterWeight (i : Fin 30) : ℕ :=
  if i.val < 15 then 17+(14-i.val) else 17+(29-i.val)

private theorem sylvester_entry_weight (k : Fin 2) (i j : Fin 30)
    (h : literalSylvester k i j ≠ 0) :
    (literalSylvester k i j).natDegree+(29-j.val) ≤ sylvesterWeight i := by
  unfold literalSylvester sylvesterRow at h ⊢
  unfold sylvesterWeight
  by_cases hi : i.val < 15
  · simp only [ite_eq_left hi] at h ⊢
    exact shifted_coefficient_weight 0 (14-i.val) (29-j.val) h
  · simp only [ite_eq_right hi] at h ⊢
    exact shifted_coefficient_weight k.succ (29-i.val) (29-j.val) h

/-- The actual fixed Sylvester determinants have parameter degree at most 285. -/
theorem literal_resultant_degree_bound (k : Fin 2) :
    (actualResultant k).natDegree ≤ 285 := by
  apply weighted_det_bound (literalSylvester k) sylvesterWeight (fun j => 29-j.val) 285
  · decide +kernel
  · exact sylvester_entry_weight k

private def minorRow (i : Fin 28) : Polynomial (Polynomial ℤ) :=
  if i.val < 14 then X^(13-i.val)*sourcePolynomial 0
  else X^(27-i.val)*sourcePolynomial 1

private def minorMatrix (constant : Bool) : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  fun i j => (minorRow i).coeff (if j.val < 27 then 28-j.val else if constant then 0 else 1)

private def minorWeight (i : Fin 28) : ℕ :=
  if i.val < 14 then 17+(13-i.val) else 17+(27-i.val)

private theorem minor_entry_weight (constant : Bool) (i j : Fin 28)
    (h : minorMatrix constant i j ≠ 0) :
    (minorMatrix constant i j).natDegree+
      (if j.val < 27 then 28-j.val else if constant then 0 else 1) ≤ minorWeight i := by
  unfold minorMatrix minorRow at h ⊢
  unfold minorWeight
  by_cases hi : i.val < 14
  · simp only [ite_eq_left hi] at h ⊢
    exact shifted_coefficient_weight 0 (13-i.val) _ h
  · simp only [ite_eq_right hi] at h ⊢
    exact shifted_coefficient_weight 1 (27-i.val) _ h

private theorem minor_a_bridge : actualMinorA0 = (minorMatrix false).det := by
  unfold actualMinorA0
  congr 1
  ext i j
  by_cases hi : i.val < 14 <;> by_cases hj : j.val < 27 <;>
    simp [fixedMinorRCoeff,literalMatrixCoeff,literalRowCoeff,sourceE0Coeff,
      sourceE1Coeff,minorMatrix,minorRow,sourcePolynomial,hi,hj]

private theorem minor_c_bridge : actualMinorC0 = (minorMatrix true).det := by
  unfold actualMinorC0
  congr 1
  ext i j
  by_cases hi : i.val < 14 <;> by_cases hj : j.val < 27 <;>
    simp [fixedMinorCCoeff,literalMatrixCoeff,literalRowCoeff,sourceE0Coeff,
      sourceE1Coeff,minorMatrix,minorRow,sourcePolynomial,hi,hj]

/-- The original r-column minor has degree at most 252 and the constant-column minor at most 253. -/
theorem literal_minor_degree_bounds :
    actualMinorA0.natDegree ≤ 252 ∧ actualMinorC0.natDegree ≤ 253 := by
  constructor
  · rw [minor_a_bridge]
    apply weighted_det_bound (minorMatrix false) minorWeight
      (fun j => if j.val < 27 then 28-j.val else if false then 0 else 1) 252
    · decide +kernel
    · exact minor_entry_weight false
  · rw [minor_c_bridge]
    apply weighted_det_bound (minorMatrix true) minorWeight
      (fun j => if j.val < 27 then 28-j.val else if true then 0 else 1) 253
    · decide +kernel
    · exact minor_entry_weight true

private def topCoefficients : Fin 3 → Fin 16 → ℤ :=
  ![![155926,398475,-2637039,2649746,-636165,3317251,8687448,-37353091,15571863,47580070,-43923051,-9217971,22459578,-7143760,462240,-102720],![960520,1528984,-12208160,6253720,21928328,-3666480,-17329720,-58757336,61771440,84575416,-105757736,-9870816,48118592,-18426880,2958336,-657408],![2251607,-351575,-14980773,-8602308,125255445,-118813963,-223744074,458973773,-50883779,-488733640,352808543,111286803,-195810009,51490830,2773440,-616320]]

private theorem source_top_coeff (i : Fin 3) (j : Fin 16) :
    ((sourcePolynomial i).coeff j.val).coeff (17-j.val) = topCoefficients i j := by
  fin_cases i
  · change ((sourceE0 (X : Polynomial ℤ)).coeff j.val).coeff (17-j.val) = topCoefficients 0 j
    fin_cases j <;>
      simp only [sourceE0,coeff_add,coeff_C_mul_X_pow] <;>
      norm_num [topCoefficients,coeff_add,coeff_C_mul_X_pow,coeff_mul_X_pow,coeff_C,coeff_X]
  · change ((sourceE1 (X : Polynomial ℤ)).coeff j.val).coeff (17-j.val) = topCoefficients 1 j
    fin_cases j <;>
      simp only [sourceE1,coeff_add,coeff_C_mul_X_pow] <;>
      norm_num [topCoefficients,coeff_add,coeff_C_mul_X_pow,coeff_mul_X_pow,coeff_C,coeff_X]
  · change ((sourceE2 (X : Polynomial ℤ)).coeff j.val).coeff (17-j.val) = topCoefficients 2 j
    fin_cases j <;>
      simp only [sourceE2,coeff_add,coeff_C_mul_X_pow] <;>
      norm_num [topCoefficients,coeff_add,coeff_C_mul_X_pow,coeff_mul_X_pow,coeff_C,coeff_X]

private def topEntry (i : Fin 3) (s c : ℕ) : ℤ :=
  if s ≤ c then if h : c-s < 16 then topCoefficients i ⟨c-s,h⟩ else 0 else 0

private theorem shifted_top_coeff (i : Fin 3) (s c : ℕ) :
    (if c ≤ 17+s then ((X^s*sourcePolynomial i).coeff c).coeff (17+s-c) else 0) =
      topEntry i s c := by
  rw [coeff_X_pow_mul']
  by_cases hs : s ≤ c
  · simp only [ite_eq_left hs,topEntry]
    by_cases hj : c-s < 16
    · rw [dite_eq_left hj,ite_eq_left (show c ≤ 17+s by omega)]
      have he : 17+s-c = 17-(c-s) := by omega
      rw [he]
      exact source_top_coeff i ⟨c-s,hj⟩
    · rw [dite_eq_right hj]
      have hz : (sourcePolynomial i).coeff (c-s) = 0 :=
        coeff_eq_zero_of_natDegree_lt ((source_r_degree i).trans_lt (by omega))
      simp [hz]
  · simp [hs,topEntry]

private def sylvesterTop (k : Fin 2) : Matrix (Fin 30) (Fin 30) ℤ :=
  fun i j => if i.val < 15 then topEntry 0 (14-i.val) (29-j.val)
    else topEntry k.succ (29-i.val) (29-j.val)

private theorem sylvester_top_bridge (k : Fin 2) :
    (fun i j => if 29-j.val ≤ sylvesterWeight i then
      (literalSylvester k i j).coeff (sylvesterWeight i-(29-j.val)) else 0 :
        Matrix (Fin 30) (Fin 30) ℤ) = sylvesterTop k := by
  ext i j
  unfold literalSylvester sylvesterRow sylvesterWeight sylvesterTop
  by_cases hi : i.val < 15
  · simp only [ite_eq_left hi]
    exact shifted_top_coeff 0 (14-i.val) (29-j.val)
  · simp only [ite_eq_right hi]
    exact shifted_top_coeff k.succ (29-i.val) (29-j.val)

private theorem sylvester_top_data (k : Fin 2) :
    sylvesterTop k = ![topR1,topR2] k := by
  fin_cases k <;> decide +kernel

private theorem certificate_top_nonzero (k : Fin 2) : (![topR1,topR2] k).det ≠ 0 := by
  fin_cases k
  · change topR1.det ≠ 0
    exact leading_determinants_ne_zero.1
  · change topR2.det ≠ 0
    exact leading_determinants_ne_zero.2.1

attribute [local irreducible] Matrix.det Polynomial.coeff

set_option maxRecDepth 2000 in
private theorem resultant_top_nonzero (k : Fin 2) :
    (actualResultant k).coeff 285 ≠ 0 := by
  have he : actualResultant k = (literalSylvester k).det := rfl
  have hep := congrArg (fun p : Polynomial ℤ => p.coeff 285) he
  have hc := weighted_top_coeff (literalSylvester k) sylvesterWeight
    (fun j => 29-j.val) 285 31 (by decide +kernel) (by decide +kernel)
    (sylvester_entry_weight k)
  have hb := congrArg (fun M : Matrix (Fin 30) (Fin 30) ℤ => M.det)
    (sylvester_top_bridge k)
  have hd := congrArg (fun M : Matrix (Fin 30) (Fin 30) ℤ => M.det)
    (sylvester_top_data k)
  exact fun hz => certificate_top_nonzero k
    (((hep.trans hc).trans (hb.trans hd)).symm.trans hz)

private def minorTop (constant : Bool) : Matrix (Fin 28) (Fin 28) ℤ :=
  fun i j => topEntry (if i.val < 14 then 0 else 1)
    (if i.val < 14 then 13-i.val else 27-i.val)
    (if j.val < 27 then 28-j.val else if constant then 0 else 1)

private theorem minor_top_bridge (constant : Bool) :
    (fun i j => if (if j.val < 27 then 28-j.val else if constant then 0 else 1) ≤ minorWeight i then
      (minorMatrix constant i j).coeff (minorWeight i-
        (if j.val < 27 then 28-j.val else if constant then 0 else 1)) else 0 :
        Matrix (Fin 28) (Fin 28) ℤ) = minorTop constant := by
  ext i j
  unfold minorMatrix minorRow minorWeight minorTop
  by_cases hi : i.val < 14
  · simp only [ite_eq_left hi]
    exact shifted_top_coeff 0 (13-i.val) _
  · simp only [ite_eq_right hi]
    exact shifted_top_coeff 1 (27-i.val) _

private theorem minor_top_data (constant : Bool) :
    minorTop constant = (if constant then topC else topA) := by
  cases constant <;> decide +kernel

private theorem minor_top_nonzero :
    actualMinorA0.coeff 252 ≠ 0 ∧ actualMinorC0.coeff 253 ≠ 0 := by
  constructor
  · rw [minor_a_bridge]
    have h := weighted_top_coeff (minorMatrix false) minorWeight
      (fun j => if j.val < 27 then 28-j.val else if false then 0 else 1)
      252 30 (by decide +kernel) (by decide +kernel) (minor_entry_weight false)
    have hb := h.trans (congrArg Matrix.det (minor_top_bridge false))
    have hd := congrArg Matrix.det (minor_top_data false)
    exact fun hz => leading_determinants_ne_zero.2.2.1 ((hb.trans hd).symm.trans hz)
  · rw [minor_c_bridge]
    have h := weighted_top_coeff (minorMatrix true) minorWeight
      (fun j => if j.val < 27 then 28-j.val else if true then 0 else 1)
      253 30 (by decide +kernel) (by decide +kernel) (minor_entry_weight true)
    have hb := h.trans (congrArg Matrix.det (minor_top_bridge true))
    have hd := congrArg Matrix.det (minor_top_data true)
    exact fun hz => leading_determinants_ne_zero.2.2.2 ((hb.trans hd).symm.trans hz)

/-- Exact parameter degrees of both original fixed resultants and both original fixed minors. -/
theorem literal_elimination_exact_degrees :
    (∀ k : Fin 2, (actualResultant k).natDegree = 285) ∧
    actualMinorA0.natDegree = 252 ∧ actualMinorC0.natDegree = 253 := by
  refine ⟨fun k => natDegree_eq_of_le_of_coeff_ne_zero
    (literal_resultant_degree_bound k) (resultant_top_nonzero k),?_,?_⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero literal_minor_degree_bounds.1 minor_top_nonzero.1
  · exact natDegree_eq_of_le_of_coeff_ne_zero literal_minor_degree_bounds.2 minor_top_nonzero.2

end D5.S3.Observer.CubicGain.LiteralSylvesterBounds
