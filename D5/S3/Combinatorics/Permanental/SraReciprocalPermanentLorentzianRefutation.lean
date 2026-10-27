/- GID: D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.claim; result=D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result; claim=D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.claim
   digest: A positive inverse M matrix refutes reciprocal-permanent Lorentzianity. -/

/-
proof_shape: bind-only (same-delivery helpers expanded).
escape_witness: none.
admission_basis: open-problem-resolution (#21688; Refuted).
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Direct frozen dependencies (declaration statement_id):
PSW.principalPermanent = sha256:66eb65c8ad54754e0b139d35a0ac8a83e47445fd4e065a42e0dcb14ff778d627.
D5.S3.Quantum.Matrix.SpectralPower.posDef_two = sha256:aab0c093aa3d2b2ec35e668b9050f590c2f79cbaf6d347b59632a1280bc73376.
RHLinalg.hermForm = sha256:73fe60400b35034994e7c69515b0b2e4349284066d1b1d60c2cbc066f776f399.
RHLinalg.PosDefOn = sha256:1a3984755339c5111892c7833498f2dfb4d6ad603ae9ee2bfc8abb28498435a6.
RHLinalg.finrank_le_posIndex_of_posDefOn = sha256:0fd86d73064fff5458ac1aea668ee6b97946d76c90bf8ee950b13606ae84ccac.
RHLinalg.posIndex = sha256:42e083edd7325021be91dcfc59120d330216211b11ff02fb4fb87542200e1c0a.
Declarations (all are on a settling result value path):
InverseMMatrix: proof_shape: bind-only; escape_witness: none; consumer: claim, SraSymmetricAlphaPermanentRefutation.claim.
reciprocalPolynomial: proof_shape: bind-only; escape_witness: none; consumer: claim, close_plane_positive, coefficient_cast, result, witness_coeff.
positiveHomogeneous: proof_shape: bind-only; escape_witness: none; consumer: result, strictlyLorentzian.
quadraticHessian: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive, hess_coeff, result, strictlyLorentzian.
strictlyLorentzian: proof_shape: bind-only; escape_witness: none; consumer: Lorentzian, result.
Lorentzian: proof_shape: bind-only; escape_witness: none; consumer: claim, result.
claim: proof_shape: bind-only; escape_witness: none; consumer: result.
A: proof_shape: bind-only; escape_witness: none; consumer: A_cast, A_mul_M, close_plane_positive, coefficient_cast, inverseM, permanent_cast, result, witness_coeff, witness_positive.
M: proof_shape: bind-only; escape_witness: none; consumer: A_mul_M, inverseM.
AQ: proof_shape: bind-only; escape_witness: none; consumer: A_cast, coeffQ, coefficient_cast, coefficient_table, permanent_cast.
A_mul_M: proof_shape: bind-only; escape_witness: none; consumer: inverseM.
witness_positive: proof_shape: bind-only; escape_witness: none; consumer: inverseM.
inverseM: proof_shape: bind-only; escape_witness: none; consumer: result.
deriv3: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive, hess_coeff, result.
A_cast: proof_shape: bind-only; escape_witness: none; consumer: permanent_cast.
permanent_cast: proof_shape: bind-only; escape_witness: none; consumer: coefficient_cast.
plane: proof_shape: bind-only; escape_witness: none; consumer: plane_form, plane_injective, two_plane_excludes_unique.
plane_injective: proof_shape: bind-only; escape_witness: none; consumer: two_plane_excludes_unique.
quadratic_positive: proof_shape: bind-only; escape_witness: none; consumer: two_plane_excludes_unique.
plane_form: proof_shape: bind-only; escape_witness: none; consumer: two_plane_excludes_unique.
two_plane_excludes_unique: proof_shape: bind-only; escape_witness: none; consumer: result.
idx: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive, coefficient_table, expo, expo_degree, hess_coeff.
expo: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive, coefficient_table, expo_degree, hess_coeff, witness_coeff.
expo_degree: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive.
hess_coeff: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive.
subsetExpo: proof_shape: bind-only; escape_witness: none; consumer: coeffQ, coefficient_cast, coefficient_table, term_monomial.
coeffQ: proof_shape: bind-only; escape_witness: none; consumer: coefficient_cast, coefficient_table, witness_coeff.
term_monomial: proof_shape: bind-only; escape_witness: none; consumer: coefficient_cast.
coefficient_cast: proof_shape: bind-only; escape_witness: none; consumer: witness_coeff.
coefficient_table: proof_shape: bind-only; escape_witness: none; consumer: witness_coeff.
witness_coeff: proof_shape: bind-only; escape_witness: none; consumer: close_plane_positive.
close_plane_positive: proof_shape: bind-only; escape_witness: none; consumer: result.
result: proof_shape: bind-only; escape_witness: none; consumer: settling conclusion.
-/


import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Quantum.Matrix.SpectralPower

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsChain

/-! The source assertion and its explicit inverse-M-matrix refutation. -/

noncomputable section
open scoped BigOperators
open Matrix Finset

namespace D5.S3.Combinatorics.Permanental.SraReciprocalPermanentLorentzianRefutation

/-- Sra's introduction: nonnegative, invertible, with inverse off-diagonal nonpositive. -/
def InverseMMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j : Fin n, 0 ≤ A i j) ∧ IsUnit A.det ∧
    ∀ i j : Fin n, i ≠ j → A⁻¹ i j ≤ 0


open MvPolynomial

/-- The variable `none` is x₀ and `some i` is the source variable xᵢ₊₁. -/
def reciprocalPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  ∑ S : Finset (Fin n), C (PSW.principalPermanent A S)⁻¹ *
    X none ^ (n - S.card) * ∏ i ∈ S, X (some i)

/-- P⁽ᵈ⁾: homogeneous of degree d, with every degree-d coefficient positive. -/
def positiveHomogeneous {n : ℕ} (d : ℕ) (f : MvPolynomial (Option (Fin n)) ℝ) : Prop :=
  f.IsHomogeneous d ∧
    ∀ a : Option (Fin n) →₀ ℕ, a.sum (fun _ k => k) = d → 0 < f.coeff a

/-- Constant matrix of second derivatives at the origin (the Hessian for degree two). -/
def quadraticHessian {n : ℕ} (f : MvPolynomial (Option (Fin n)) ℝ) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
  fun i j => (pderiv i (pderiv j f)).coeff 0

/-- Brändén–Huh Definition 2.1, including the degree-zero and degree-one cases. -/
def strictlyLorentzian {n : ℕ} :
    (d : ℕ) → MvPolynomial (Option (Fin n)) ℝ → Prop
  | 0, f => positiveHomogeneous 0 f
  | 1, f => positiveHomogeneous 1 f
  | 2, f => positiveHomogeneous 2 f ∧
      ∃ h : (quadraticHessian f).IsHermitian,
        (∀ i : Option (Fin n), h.eigenvalues i ≠ 0) ∧
        ∃! i : Option (Fin n), 0 < h.eigenvalues i
  | k + 3, f => positiveHomogeneous (k + 3) f ∧
      ∀ i : Option (Fin n), strictlyLorentzian (k + 2) (pderiv i f)

/-- Coefficientwise Euclidean closure in the finite-dimensional degree-d space. -/
def Lorentzian {n : ℕ} (d : ℕ) (f : MvPolynomial (Option (Fin n)) ℝ) : Prop :=
  f.IsHomogeneous d ∧ ∀ ε : ℝ, 0 < ε →
    ∃ g : MvPolynomial (Option (Fin n)) ℝ, strictlyLorentzian d g ∧
      ∀ a : Option (Fin n) →₀ ℕ, a.sum (fun _ k => k) = d →
        |g.coeff a - f.coeff a| < ε

/-- The affirmative assertion asked in Sra, Section 4(d); no symmetry hypothesis. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    InverseMMatrix A → Lorentzian n (reciprocalPolynomial A)


open MvPolynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def A : Matrix (Fin 5) (Fin 5) ℝ :=
  !![13,1,7,7,7; 1,13,7,7,7; 1,1,7,7,7; 1,1,1,7,7; 1,1,1,1,7]
private def M : Matrix (Fin 5) (Fin 5) ℝ :=
  (1/84 : ℝ) • !![7,0,-7,0,0; 0,7,-7,0,0; 0,0,14,-14,0;
     0,0,0,14,-14; -1,-1,0,0,14]
private def AQ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![13,1,7,7,7; 1,13,7,7,7; 1,1,7,7,7; 1,1,1,7,7; 1,1,1,1,7]

private theorem A_mul_M : A * M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, M, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem witness_positive : ∀ i j : Fin 5, 0 < A i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [A]

private theorem inverseM : InverseMMatrix A := by
  refine ⟨?_, Matrix.isUnit_det_of_right_inverse A_mul_M, ?_⟩
  · exact fun i j => (witness_positive i j).le
  · rw [Matrix.inv_eq_right_inv A_mul_M]
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [M] at *

private def deriv3 {R : Type*} [CommSemiring R] (f : MvPolynomial (Option (Fin 5)) R) :=
  pderiv (some 2) (pderiv (some 3) (pderiv (some 4) f))

private theorem A_cast (i j : Fin 5) : A i j = (AQ i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> norm_num [A, AQ]

private theorem permanent_cast (S : Finset (Fin 5)) :
    PSW.principalPermanent A S =
      (((AQ.submatrix (fun i : S => (i : Fin 5))
        (fun i : S => (i : Fin 5))).permanent : ℚ) : ℝ) := by
  simp only [PSW.principalPermanent, Matrix.permanent, Matrix.submatrix_apply,
    Rat.cast_sum, Rat.cast_prod, A_cast]

private def plane : (Fin 2 → ℝ) →ₗ[ℝ] (Option (Fin 5) → ℝ) :=
  LinearMap.pi fun i => match i with
    | none => LinearMap.proj 0
    | some j => if j = 0 ∨ j = 1 then LinearMap.proj 1 else 0

private theorem plane_injective : Function.Injective plane := by
  intro x y h
  have h0 := congrFun h none
  have h1 := congrFun h (some 0)
  ext i
  fin_cases i <;> simpa [plane] using (by assumption)

private theorem quadratic_positive (a b c : ℝ) (ha : 0 < a) (hd : 0 < a*c-b^2)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < a*x^2+2*b*x*y+c*y^2 := by
  have hpd := D5.S3.Quantum.Matrix.SpectralPower.posDef_two a b c ha hd
  have hz : (![ (x : ℂ), (y : ℂ)] : Fin 2 → ℂ) ≠ 0 := by
    intro he
    have hx0 : x = 0 := by
      have hh := congrArg Complex.re (congrFun he 0)
      simpa using hh
    have hy0 : y = 0 := by
      have hh := congrArg Complex.re (congrFun he 1)
      simpa using hh
    exact hxy.elim (fun h => h hx0) (fun h => h hy0)
  have hh := hpd.re_dotProduct_pos hz
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.add_re] at hh
  nlinarith only [hh]

private theorem plane_form (H : Matrix (Option (Fin 5)) (Option (Fin 5)) ℝ)
    (hH : H.IsHermitian) (x : Fin 2 → ℝ) :
    RHLinalg.hermForm H (plane x) =
      H none none*(x 0)^2 + 2*(H none (some 0)+H none (some 1))*(x 0)*(x 1) +
      (H (some 0) (some 0)+2*H (some 0) (some 1)+H (some 1) (some 1))*(x 1)^2 := by
  have hs : ∀ i j, H j i = H i j := fun i j => by
    have hh := congrFun (congrFun hH i) j
    simpa [Matrix.conjTranspose_apply] using hh
  simp [RHLinalg.hermForm, plane, Matrix.mulVec, dotProduct,
    Fintype.sum_option, Fin.sum_univ_succ]
  rw [hs (some 0) none, hs (some 1) none, hs (some 0) (some 1)]
  ring

private theorem two_plane_excludes_unique (H : Matrix (Option (Fin 5)) (Option (Fin 5)) ℝ)
    (hH : H.IsHermitian)
    (ha : 0 < H none none)
    (hd : 0 < H none none *
      (H (some 0) (some 0)+2*H (some 0) (some 1)+H (some 1) (some 1)) -
      (H none (some 0)+H none (some 1))^2) :
    ¬ ∃! i, 0 < hH.eigenvalues i := by
  intro hp
  have hpos : RHLinalg.PosDefOn H (LinearMap.range plane) := by
    rintro _ ⟨x, rfl⟩ hx
    rw [plane_form H hH]
    apply quadratic_positive _ _ _ ha hd
    by_contra h
    push Not at h
    apply hx
    have : x = 0 := by ext i; fin_cases i <;> simp_all
    simp [this]
  have hdim := RHLinalg.finrank_le_posIndex_of_posDefOn hH hpos
  have hdim2 : Module.finrank ℝ (LinearMap.range plane) = 2 := by
    rw [LinearMap.finrank_range_of_inj plane_injective]
    simp
  have hone : RHLinalg.posIndex hH = 1 := by
    obtain ⟨i, hi, hu⟩ := hp
    apply Finset.card_eq_one.mpr
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj => hu j hj, fun hj => hj ▸ hi⟩
  rw [hdim2, hone] at hdim
  omega

private def idx : Fin 3 → Option (Fin 5) := ![none, some 0, some 1]
private def expo (i j : Fin 3) : Option (Fin 5) →₀ ℕ :=
  Finsupp.single (idx i) 1 + Finsupp.single (idx j) 1 +
    Finsupp.single (some 2) 1 + Finsupp.single (some 3) 1 + Finsupp.single (some 4) 1

private theorem expo_degree (i j : Fin 3) : (expo i j).sum (fun _ k => k) = 5 := by
  simp [expo, Finsupp.sum_add_index]

private theorem hess_coeff (f : MvPolynomial (Option (Fin 5)) ℝ) (i j : Fin 3) :
    quadraticHessian (deriv3 f) (idx i) (idx j) =
      f.coeff (expo i j) * (if i = j then 2 else 1) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [quadraticHessian, deriv3, coeff_pderiv, expo, idx, Finsupp.single_apply]


private def subsetExpo (S : Finset (Fin 5)) : Option (Fin 5) →₀ ℕ :=
  Finsupp.single none (5-S.card) + ∑ i ∈ S, Finsupp.single (some i) 1

private def coeffQ (e : Option (Fin 5) →₀ ℕ) : ℚ :=
  ∑ S : Finset (Fin 5), if (∀ v, subsetExpo S v = e v) then
    ((AQ.submatrix (fun i : S => (i : Fin 5)) (fun i : S => (i : Fin 5))).permanent)⁻¹ else 0

private theorem term_monomial (S : Finset (Fin 5)) (c : ℝ) :
    C c * X none ^ (5-S.card) * ∏ i ∈ S, X (some i) =
      monomial (subsetExpo S) c := by
  have hp : (∏ i ∈ S, X (some i) : MvPolynomial (Option (Fin 5)) ℝ) =
      monomial (∑ i ∈ S, Finsupp.single (some i) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [hp, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial]
  simp [subsetExpo]

private theorem coefficient_cast (e : Option (Fin 5) →₀ ℕ) :
    (reciprocalPolynomial A).coeff e = (coeffQ e : ℝ) := by
  simp only [reciprocalPolynomial, coeff_sum, term_monomial, coeff_monomial,
    Finsupp.ext_iff, coeffQ, Rat.cast_sum, apply_ite, Rat.cast_inv, Rat.cast_zero,
    ← permanent_cast]

private theorem coefficient_table : ∀ i j : Fin 3, coeffQ (expo i j) =
    (!![1/546,1/9996,1/9996; 1/9996,0,1/182784; 1/9996,1/182784,0] :
      Matrix (Fin 3) (Fin 3) ℚ) i j := by
  simp only [coeffQ, subsetExpo, expo, Finsupp.add_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem witness_coeff (i j : Fin 3) :
    (reciprocalPolynomial A).coeff (expo i j) =
      (!![1/546,1/9996,1/9996; 1/9996,0,1/182784; 1/9996,1/182784,0] :
        Matrix (Fin 3) (Fin 3) ℝ) i j := by
  rw [coefficient_cast, coefficient_table]
  fin_cases i <;> fin_cases j <;> norm_num

private theorem close_plane_positive (g : MvPolynomial (Option (Fin 5)) ℝ)
    (hg : ∀ e : Option (Fin 5) →₀ ℕ, e.sum (fun _ k => k) = 5 → |g.coeff e - (reciprocalPolynomial A).coeff e| < 1/1000000000000) :
    let H := quadraticHessian (deriv3 g)
    0 < H none none ∧ 0 < H none none *
      (H (some 0) (some 0)+2*H (some 0) (some 1)+H (some 1) (some 1)) -
      (H none (some 0)+H none (some 1))^2 := by
  let H := quadraticHessian (deriv3 g)
  let a := H none none
  let b := H none (some 0) + H none (some 1)
  let c := H (some 0) (some 0)+2*H (some 0) (some 1)+H (some 1) (some 1)
  have h00 := abs_lt.mp (hg (expo 0 0) (expo_degree 0 0))
  have h01 := abs_lt.mp (hg (expo 0 1) (expo_degree 0 1))
  have h02 := abs_lt.mp (hg (expo 0 2) (expo_degree 0 2))
  have h11 := abs_lt.mp (hg (expo 1 1) (expo_degree 1 1))
  have h12 := abs_lt.mp (hg (expo 1 2) (expo_degree 1 2))
  have h22 := abs_lt.mp (hg (expo 2 2) (expo_degree 2 2))
  simp only [witness_coeff] at h00 h01 h02 h11 h12 h22
  norm_num at h00 h01 h02 h11 h12 h22
  have ha_eq : a = 2*g.coeff (expo 0 0) := by simpa [a, H, idx, mul_comm] using hess_coeff g 0 0
  have hb_eq : b = g.coeff (expo 0 1)+g.coeff (expo 0 2) := by
    simpa [b, H, idx] using congrArg₂ (·+·) (hess_coeff g 0 1) (hess_coeff g 0 2)
  have hc_eq : c = 2*g.coeff (expo 1 1)+2*g.coeff (expo 1 2)+2*g.coeff (expo 2 2) := by
    dsimp [c, H]
    change quadraticHessian (deriv3 g) (idx 1) (idx 1) +
      2*quadraticHessian (deriv3 g) (idx 1) (idx 2) + quadraticHessian (deriv3 g) (idx 2) (idx 2) = _
    rw [hess_coeff, hess_coeff, hess_coeff]
    norm_num
    ring
  let amin : ℝ := 1/273-1/1000000000
  let bmax : ℝ := 1/4998+1/1000000000
  let cmin : ℝ := 1/91392-1/1000000000
  have haa : amin < a := by dsimp [amin]; linarith
  have hbb : -bmax < b ∧ b < bmax := by dsimp [bmax]; constructor <;> linarith
  have hcc : cmin < c := by dsimp [cmin]; linarith
  have ha0 : 0 < a := lt_trans (by norm_num [amin]) haa
  have hmul1 := mul_lt_mul_of_pos_left hcc ha0
  have hmul2 := mul_lt_mul_of_pos_right haa (by norm_num [cmin] : 0 < cmin)
  have hn : bmax^2 < amin*cmin := by norm_num [amin,bmax,cmin]
  have hb2 : b^2 < bmax^2 := sq_lt_sq' hbb.1 hbb.2
  change 0 < a ∧ 0 < a*c-b^2
  exact ⟨ha0, by linarith⟩

theorem result : ¬ claim := by
  intro hc
  have hL := hc 5 (by norm_num) A inverseM
  obtain ⟨g, hg, hclose⟩ := hL.2 (1/1000000000000) (by norm_num)
  have hq : strictlyLorentzian 2 (deriv3 g) :=
    (((hg.2 (some 4)).2 (some 3)).2 (some 2))
  obtain ⟨hH, hnonzero, hone⟩ := hq.2
  obtain ⟨ha, hd⟩ := close_plane_positive g hclose
  exact two_plane_excludes_unique _ hH ha hd hone

end D5.S3.Combinatorics.Permanental.SraReciprocalPermanentLorentzianRefutation
