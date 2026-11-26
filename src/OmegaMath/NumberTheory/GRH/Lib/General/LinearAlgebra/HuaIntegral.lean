import OmegaMath.NumberTheory.GRH.Lib.General.Groups.ValuationPair
import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.HaarUnique
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Known result: the Ostrowski-Taussky inequality and an upper bound for Hua's determinant integral.
Here the determinant of a complex matrix is bounded below through any positive semidefinite matrix
under twice its hermitian part. Hua's integral is given only as an upper bound, with an affine
change of the rows, in place of the exact value. Source: Ostrowski and Taussky, 1951; Hua, Harmonic
Analysis in the Classical Domains, 1963.

This file: Real Heisenberg bicharacter, Gaussian vacuum, creation and annihilation operators, Lie
algebra action. Euclidean volume normalised by Gaussian integral one; products and powers. Principal
minors: norm bound, multiplicativity, Jacobi's complementary minor theorem. Upper bound for Hua's
determinant integral; beta-type integrals. -/

noncomputable section

open Matrix Complex MvPolynomial MeasureTheory Real GaussianFourier Finset Fintype
variable {ι : Type*} [Fintype ι] (ε : ι → ℤˣ) (x : ι → ℂ) (a b : ι)

/-- For signs ε, the Heisenberg datum on ℂ^ι given by the continuous unit-modulus bicharacter
β(x,y) = exp((y*εx − x*εy)/2) = exp(i Im y*εx). -/
def realHeis : Heisenberg (ι → ℂ) := by
  use fun x y ↦ ((star y ⬝ᵥ signMatrix ε *ᵥ x - star x ⬝ᵥ signMatrix ε *ᵥ y) / 2).exp
  repeat simp [← Complex.exp_add] <;> grind
  simp [signMatrix, dotProduct]; grind; fun_prop

/-- The function on ℂ^ι sending x to exp(−|x|²/2). -/
def realVac := (-(star x ⬝ᵥ x) / 2).exp

/-- The diagonal complex matrix P₊ with entry 1 where ε_i = 1 and 0 elsewhere; for −ε it is the
projection P₋ on the negative coordinates. -/
def posProj := diagonal fun i ↦ ite (ε i = 1) (1 : ℂ) 0

/-- For signs ε and x in ℂ^ι, the vector whose i-th coordinate is the conjugate of xᵢ if εᵢ = 1
and xᵢ otherwise. -/
def holCoord := (1 + (posProj ε).mulVecBilin ℝ ℝ * ((starL' ℝ).1.1 - 1)).toContinuousLinearMap

lemma holCoord_eq : holCoord ε x = fun i ↦
  ite (ε i = 1) (star x i) (x i) := by aesop (add simp [holCoord, posProj])

/-- For signs ε and index a, the linear operator on complex polynomials: multiplication by X_a
if ε_a = 1, otherwise −∂/∂X_a. -/
def raiseOp := ite (ε a = 1) (.mulLeft ℂ (X a)) (-(pderiv a).1)

/-- For signs ε and index a, the linear operator on complex polynomials: ∂/∂X_a if ε_a = 1,
otherwise multiplication by X_a. -/
def lowerOp := ite (ε a = 1) (pderiv a).1 (.mulLeft ℂ (X a))

/-- For indices a, b, the composite A_a∘B_b on polynomials, with A_a = X_a or −∂_a and B_b = ∂_b
or X_b according as the sign is positive or negative. -/
def glOp := raiseOp ε a * lowerOp ε b

/-- For signs ε, the complex-linear map from ι×ι matrices to operators on polynomials, u ↦
Σ_{a,b} u_{ab} A_a B_b. -/
def weilDeriv := ∑ a, ∑ b, (entryLinearMap ℂ ℂ a b).smulRight (glOp ε a b)

/-- With ζ = `holCoord` ε, for x in ℂ^ι the operator Σᵢ (conj(ζᵢ(x))·Xᵢ − ζᵢ(x)·∂/∂Xᵢ) on complex
polynomials. -/
def heisDeriv := ∑ i, (x i • raiseOp ε i - star (x i * ε i) • lowerOp ε i)

variable {V W} [MeasureSpace.{0} V] [MeasureSpace W] {q q'} {a b ι : _} [Fintype ι] [SigmaFinite
  (@volume V _)] [SFinite (@volume W _)]

/-- The volume on V is Gaussian-normalised for the real function q with exponent a: ∫ exp(−t
q(x)) dx = (π/t)^a for all t > 0. -/
class HasGaussianIntegral (a : outParam ℝ) (q : outParam (V → ℝ)) where
  integral_exp_eq {t} : 0 < t → ∫ x, Real.exp (-t * q x) = (π / t) ^ a

variable [h : @HasGaussianIntegral V _ a q]

/-- Let the volume on V be σ-finite, q ≥ 0 measurable, and ∫ exp(−tq) = (π/t)^a for all t > 0.
For c > 0, s > 0, s > a: ∫ (c + q)^{−s} = π^a c^{a−s} Γ(s−a)/Γ(s). -/
lemma lintegral_inv_add_rpow {s c} (hc : 0 < c) (ha : a < s) (h0 : ∀ x, 0 ≤ q x) (hs : 0 < s)
    (hq : Measurable q := by fun_prop) : ∫⁻ x, .ofReal ((c + q x)⁻¹ ^ s) =
    .ofReal (π ^ a / Real.Gamma s * ((1 / c) ^ (s - a) * Real.Gamma (s - a))) := by
  have j {β m ν f c} (e : @integral β _ _ _ m ν f = c) hc :=
    e ▸ ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (e.trans_ne hc))
  have k {a} r c ha hr (_ : 0 < c) := j (@integral_rpow_mul_exp_neg_mul_Ioi a r ha hr ▸
    integral_const_mul c _) (by positivity) (ae_restrict_of_forall_mem (by simp) (by simp; bound))
  rw [lintegral_congr fun x ↦ .trans (by field_simp) (k (c + q x) s.Gamma⁻¹ hs (by grind) ?_),
    lintegral_lintegral_swap (by fun_prop), setLIntegral_congr_fun measurableSet_Ioi
    fun t (p : 0 < t) ↦ (j ?_ ?_ (.of_forall ?_)).symm, k]
  any_goals finiteness
  simp_all [← neg_mul, h.1, mul_comm _ t, mul_add, Real.exp_add, rpow_sub,
    div_rpow, le_of_lt, pi_pos, field]

instance : @HasGaussianIntegral ℝ _ (1 / 2) (· ^ 2) := ⟨by simp [↓integral_gaussian, sqrt_eq_rpow]⟩

instance : @HasGaussianIntegral ℂ _ 1 (‖·‖ ^ 2) := ⟨(by simp [↓integral_rexp_neg_mul_sq_norm ·])⟩

instance [k : HasGaussianIntegral b q'] : HasGaussianIntegral (a + b) fun x : V × W ↦
  q x.1 + q' x.2 := ⟨(by simp [·,
  rpow_add, pi_pos, ← h.1, ← k.1, ← integral_prod_mul, Real.exp_add, mul_add, volume])⟩

instance HasGaussianIntegral.pi : HasGaussianIntegral (a * card ι) fun x : ι → V ↦ ∑ i, q (x i) :=
  ⟨(by simp (disch :=
  bound) [rpow_mul, ← h.1 ·, ← integral_fintype_prod_volume_eq_pow, ← Real.exp_sum, mul_sum])⟩

/-- For a natural number l, real x ≥ 0 and real v: x^l ≤ l!·exp(lv + x·e^{−v}). -/
lemma pow_le_exp_log_factorial_add (l : ℕ) (x : NNReal) v : x ^ l ≤ Real.exp (.log l.factorial + l *
  v + x / .exp v) := by grw [Real.exp_add, ← Real.pow_div_factorial_le_exp (_ / _), Real.exp_add,
  Real.exp_log, Real.exp_nat_mul] <;> simp [field, div_pow, l.factorial_pos]

open CStarAlgebra ComplexConjugate ComplexOrder MatrixOrder Norms.L2Operator Function
variable {n m} [Fintype n] [Fintype m] {x b : Matrix n n ℂ} (y) {p} [@DecidablePred n p]
  {ε : n → _} (g : USign ε)

/-- The principal minor of the complex matrix y on the set of indices satisfying the condition p. -/
def principalMinor p [@DecidablePred n p] : ℂ := (toSquareBlockProp y p).det

/-- A principal minor of size k of x has modulus at most ‖x‖^k (operator norm). -/
lemma norm_principalMinor_le_pow : ‖principalMinor x p‖ ≤ ‖x‖ ^ Fintype.card {i // p i} := by
  simpa [← sq, pow_right_comm, sq_le_sq, toBlock_diagonal_self] using!
    norm_det_le_norm_det_of_posSemidef
    (x.toBlock p p).posSemidef_conjTranspose_mul_self (le_of_add_le_of_nonneg_left
    ((toBlock_mul_eq_add p p p _ x).ge.trans (star_mul_le_algebraMap_norm_sq (a := x).submatrix
    _)) (posSemidef_conjTranspose_mul_self _).nonneg) (Q := toBlock _ p p)

attribute [local aesop 1%] congr

attribute [local simp] Fintype.sum_eq_zero toSquareBlockProp

@[local simp low] lemma principalMinor_eq_det : principalMinor x p =
  (1 - diagonal (if p · then 1 else 0) * (1 - x)).det := by rw [twoBlockTriangular_det₀ _ p,
  principalMinor, (_ : toSquareBlockProp _ (¬p ·) = 1)] <;> aesop

lemma principalMinor_fromBlocks {y p} [@DecidablePred (n ⊕ m) p] :
  principalMinor (fromBlocks x 0 0 y) p = principalMinor x (p <| .inl
  ·) * principalMinor y (p <| .inr ·) := by simp [← det_fromBlocks_zero₂₁' _ _ 0, fromBlocks]; aesop

@[simp] lemma principalMinor_blockDiagonal u p [@DecidablePred (m × n) p] : principalMinor
  ((blockDiagonal u).submatrix .swap .swap) p = ∏ τ, principalMinor (u τ) (p ⟨τ, ·⟩) := by
  simp [← det_blockDiagonal, blockDiagonal, ← det_reindex_self (.prodComm m _)]; aesop

/-- Jacobi's complementary minor identity: for a complex square matrix x with det x ≠ 0, the
principal minor of x⁻¹ on the indices satisfying p equals the principal minor of x on the
complementary indices divided by det x. -/
lemma jacobi_complementary_minor (hx : x.det ≠ 0) : principalMinor x⁻¹ p =
  principalMinor x (¬p ·) / x.det := by simp [field, ← det_mul, mul_sub, sub_mul]; aesop

@[fun_prop] lemma continuous_principalMinor : Continuous (principalMinor · p) := by simp; fun_prop

lemma principalMinor_of_forall (h : ∀ i, p i) : principalMinor x p = x.det := by aesop

lemma principalMinor_of_forall_not (h : ∀ i, ¬p i) : principalMinor x p = 1 := by aesop

@[simp] lemma principalMinor_one : principalMinor 1 p = 1 := by simp

@[simp] lemma principalMinor_transpose : principalMinor xᵀ p = principalMinor x p := det_transpose _

@[simp] lemma principalMinor_conjTranspose : principalMinor xᴴ p = conj (principalMinor x p) :=
  det_conjTranspose _

/-- If x_ij = 0 or b_jk = 0 whenever i and k satisfy p and j does not, the principal minors on p
satisfy Δ_p(xb) = Δ_p(x)Δ_p(b). -/
lemma principalMinor_mul (h : ∀ i j k, p i → ¬p j → p k → x i j = 0 ∨ b j k = 0) :
  principalMinor (x * b) p = principalMinor x p * principalMinor b p := by
  simp [principalMinor, toBlock_mul_eq_add p p, ← det_mul]; congr; aesop (add simp mul_apply)

lemma principalMinor_submatrix (e : m ≃ n) : principalMinor (x.submatrix e e) (p <| e ·) =
  principalMinor x p := .symm (det_submatrix_equiv_self e.subtypeEquivOfSubtype _).symm

/-- For g in U(diag ε), each principal minor of g⁻¹ is the complex conjugate of the same
principal minor of g. -/
lemma U.principalMinor_coe_inv : principalMinor ↑g⁻¹ p = conj
  (principalMinor g p) := by rw [coe_inv, principalMinor_mul, principalMinor_mul, mul_right_comm,
  ← principalMinor_mul] <;> simp [↓signMatrix_mul_self, signMatrix, diagonal] <;> lia

/-- For g in U(diag ε), the principal minor on the complement of p is det g times the conjugate
of the principal minor on p. -/
lemma U.principalMinor_compl : principalMinor g (¬p ·) = g.1.1.det * conj (principalMinor g p) := by
  simp [↓← principalMinor_coe_inv, jacobi_complementary_minor, g.1.det_ne_zero, field]

lemma norm_det_le_norm_pow : ‖x.det‖ ≤ ‖x‖ ^ Fintype.card
  n := by simpa using @norm_principalMinor_le_pow _ _ x ⊤

/-- Euler's beta integral: for Im z > 0 and s > 1/2, the integral over real t of |z + t|^{−2s}
equals √π Γ(s − 1/2)/Γ(s) · (Im z)^{1−2s}. -/
lemma lintegral_norm_add_rpow (z : ℂ) {s} (hz : 0 < z.im) (hs : 1 / 2 < s) : ∫⁻ t : ℝ,
  .ofReal (‖z + t‖ ^ (-2 * s)) = .ofReal (√π * Real.Gamma (s - 1 / 2) / Real.Gamma s * z.im ^
  (-(2 * s - 1))) := by convert! (lintegral_add_left_eq_self _ z.re).trans (lintegral_inv_add_rpow
  (pow_pos hz 2) hs sq_nonneg (by bound)) using 2 <;> simp (disch := bound) [field, ↓rpow_sub,
  ↓← sqrt_eq_rpow, ↓rpow_neg_eq_inv_rpow, rpow_mul, add_comm, Complex.norm_eq_sqrt_sq_add_sq]

/-- Hua's integral bound: for M positive definite and S invertible of size k, c ≥ 0, r ≥ k, y_i
= x_iS + a_i, the integral of c|det(M + Σ_{i∈s} y_iᴴy_i)|^{−(|s|+r)} over rows x_i ∈ ℂ^k, i
∈ s, is at most c(π^k/(k!|det S|²))^{|s|}|det M|^{−r}.

Known result: an upper bound for Hua's determinant integral. -/
lemma hua_integral_le {ι κ : Type} [Fintype κ] {M : Matrix κ κ ℂ} S (hS : det S ≠ 0) (a :
  ι → _) (hM : M.PosDef) {c} (hc : 0 ≤ c) s {r} (hr : Fintype.card κ ≤ r) x :
  (∫⋯∫⁻_s, fun x ↦ .ofReal (c * ‖(M + ∑ i ∈ s,
  vecMulVec (star (x i ᵥ* S + a i)) (x i ᵥ* S + a i)).det‖⁻¹ ^ (s.card + r))) x ≤ .ofReal (c *
  ((π ^ Fintype.card κ / (Fintype.card κ).factorial / ‖S.det‖ ^ 2) ^ s.card * ‖M.det‖⁻¹ ^ r)) := by
  induction' s using Finset.induction with i s hi ih generalizing M r x; simp
  grw [lmarginal_insert _ (by fun_prop) hi, lintegral_mono fun v ↦ (ih (hM.add_posSemidef
    (posSemidef_vecMulVec_star_self (v ᵥ* S + a i))) hr.step (update x i v)).trans' (by
    grind [updateFinset, lmarginal])]
  obtain ⟨C, _, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hM.isStrictlyPositive
  have := by exact_mod_cast lintegral_inv_add_rpow (V := κ → ℂ) one_pos (lt_add_one _)
  simp_all [Real.Gamma_nat_eq_factorial, isUnit_iff_isUnit_det, star_eq_conjTranspose]
  grw [pow_succ' (_ / _), mul_assoc, div_mul_comm, ENNReal.ofReal_mul, ← this, add_le_add_left hr,
    ← lintegral_add_right_eq_self _ (-a i ᵥ* S⁻¹), lintegral_eq_det_mul (C * S⁻¹)ᵀ]
  simp (disch := finiteness) only [← lintegral_const_mul', ← ENNReal.ofReal_mul]; congr! 3
  any_goals simp [vecMulVec_eq Unit, mul_apply, RCLike.mul_conj, mul_pow, ↓mulVec_transpose, *,
    ← conjTranspose_replicateRow, replicateRow_vecMul, Matrix.mul_assoc, det_add_mul, add_vecMul]
  rw_mod_cast [norm_of_nonneg]; field; repeat finiteness
