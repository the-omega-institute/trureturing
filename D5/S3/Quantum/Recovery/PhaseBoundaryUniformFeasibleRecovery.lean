/- GID: D5/S3/Quantum/Recovery/PhaseBoundaryUniformFeasibleRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundaryUniformFeasibleRecovery
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Feasible common recovery instruments and uniform spectral estimates. -/
import D5.S3.Quantum.Recovery.PhaseBoundaryCurrentMomentDefect
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
import Mathlib.Tactic
noncomputable section
namespace D5.S3.Quantum.Recovery.PhaseBoundaryUniformFeasibleRecovery
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
open D5.S3.Quantum.Recovery.PhaseBoundaryDiagonalReferenceReduction
open D5.S3.Quantum.Recovery.PhaseBoundaryCurrentMomentDefect
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The closed half disk includes the zero jump-budget boundary. -/
structure FeasiblePoint where
  m : ℝ
  n : ℝ
  m_nonneg : 0 ≤ m
  disk : m ^ 2 + n ^ 2 ≤ 1 / 4

/-- Three physical Kraus operators: one for result zero and two for result one. -/
def branchKraus (a : FeasiblePoint) (s : Qubit) (k : Fin 3) : Matrix Qubit Qubit ℂ :=
  if k = 0 then
    !![(Real.sqrt 2 / 2 : ℝ), Complex.I * (flagSign s * Real.sqrt 2 * a.n : ℝ);
      0, (Real.sqrt 2 * a.m : ℝ)]
  else if k = 1 then
    !![(Real.sqrt 2 / 2 : ℝ), -Complex.I * (flagSign s * Real.sqrt 2 * a.n : ℝ);
      0, (Real.sqrt 2 * a.m : ℝ)]
  else !![0, (Real.sqrt (1 - 4 * a.m ^ 2 - 4 * a.n ^ 2) : ℝ); 0, 0]

private theorem branch_complete (a : FeasiblePoint) (s : Qubit) :
    ∑ k : Fin 3, (branchKraus a s k)ᴴ * branchKraus a s k = 1 := by
  have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hj : (Real.sqrt (1 - 4 * a.m ^ 2 - 4 * a.n ^ 2)) ^ 2 =
      1 - 4 * a.m ^ 2 - 4 * a.n ^ 2 := Real.sq_sqrt (by nlinarith [a.disk])
  have hk20 : (2 : Fin 3) ≠ 0 := by decide
  have hk21 : (2 : Fin 3) ≠ 1 := by decide
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [branchKraus, Fin.sum_univ_three, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, flagSign,
      Complex.mul_re, Complex.mul_im, hk20, hk21, map_ofNat] <;> nlinarith

def resultLabel (k : Fin 3) : Qubit := if k = 0 then 0 else 1

/-- The Kraus index reads an actual flag and writes a result; it never reads the source label. -/
def receiverKraus (a : FeasiblePoint) (k : Qubit × Fin 3) :
    Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ := fun p q =>
  if p.1 = resultLabel k.2 ∧ q.1 = k.1 then branchKraus a k.1 k.2 p.2 q.2 else 0

private theorem receiver_complete (a : FeasiblePoint) :
    ∑ k, (receiverKraus a k)ᴴ * receiverKraus a k = 1 := by
  ext ⟨s,i⟩ ⟨t,j⟩
  have h s := congrArg (fun Z : Matrix Qubit Qubit ℂ => Z i j) (branch_complete a s)
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  fin_cases s <;> fin_cases t
  all_goals first
    | simpa [receiverKraus, resultLabel, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Fin.sum_univ_three, Matrix.one_apply] using h (0 : Qubit)
    | simpa [receiverKraus, resultLabel, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Fin.sum_univ_three, Matrix.one_apply] using h (1 : Qubit)

private def receiver (a : FeasiblePoint) : QuantumChannel (Qubit × Qubit) (Qubit × Qubit) :=
  Classical.choose (finite_kraus_quantum_channel (receiverKraus a) (receiver_complete a))

private theorem receiver_apply (a : FeasiblePoint) (X : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) :
    CStarMatrix.ofMatrix.symm ((receiver a).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ k, receiverKraus a k * X * (receiverKraus a k)ᴴ :=
  Classical.choose_spec (finite_kraus_quantum_channel (receiverKraus a) (receiver_complete a)) X

/-- A common receiver-only instrument; its channel interface is completely positive at every reference. -/
def feasibleInstrument (a : FeasiblePoint) : Instrument := FlagInstrument.extract (receiver a)

private theorem feasible_operation (a : FeasiblePoint) (j s : Qubit)
    (X : CStarMatrix Qubit Qubit ℂ) (i l : Qubit) :
    (feasibleInstrument a).operation j s X i l =
      ∑ k : Fin 3, if resultLabel k = j then
        (branchKraus a s k * CStarMatrix.ofMatrix.symm X * (branchKraus a s k)ᴴ) i l else 0 := by
  have hh := congrArg (fun Y : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ => Y (j,i) (j,l))
    (receiver_apply a (CStarMatrix.ofMatrix.symm (insertBlock s X)))
  change ((receiver a).toCompletelyPositiveMap (insertBlock s X)) (j,i) (j,l) = _
  change ((receiver a).toCompletelyPositiveMap (insertBlock s X)) (j,i) (j,l) = _ at hh
  rw [hh]
  fin_cases s <;> fin_cases j <;>
    simp [receiverKraus, resultLabel, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, insertBlock]

private theorem feasible_sym_operation (a : FeasiblePoint) (j s i l : Qubit)
    (X : CStarMatrix Qubit Qubit ℂ) :
    (symInstrument (feasibleInstrument a)).operation j s X i l =
      (feasibleInstrument a).operation j s X i l := by
  rw [sym_operation_entry]
  simp_rw [feasible_operation]
  have hk20 : (2 : Fin 3) ≠ 0 := by decide
  have hk21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases j <;> fin_cases s <;> fin_cases i <;> fin_cases l <;>
    simp [resultLabel, branchKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, flagSign, phaseInput, hk20, hk21,
      Matrix.diagonal, map_ofNat, Matrix.vecMul, dotProduct] <;> ring

private theorem feasible_moments (a : FeasiblePoint) (j : Qubit) :
    A (symInstrument (feasibleInstrument a)) j = 1 / 2 ∧
    C (symInstrument (feasibleInstrument a)) j = 0 ∧
    B (symInstrument (feasibleInstrument a)) j =
      (if j = 0 then 2 * a.n ^ 2 else 1 - 2 * a.n ^ 2 - 4 * a.m ^ 2) ∧
    D (symInstrument (feasibleInstrument a)) j = 2 * a.m ^ 2 ∧
    M (symInstrument (feasibleInstrument a)) j = (a.m : ℂ) ∧
    N (symInstrument (feasibleInstrument a)) j =
      (if j = 0 then -Complex.I * (a.n : ℂ) else Complex.I * (a.n : ℂ)) ∧
    P (symInstrument (feasibleInstrument a)) j = 0 ∧
    U (symInstrument (feasibleInstrument a)) j = 0 ∧
    V (symInstrument (feasibleInstrument a)) j = 0 ∧
    W (symInstrument (feasibleInstrument a)) j =
      (if j = 0 then Complex.I * (2 * a.m * a.n : ℝ) else
        -Complex.I * (2 * a.m * a.n : ℝ)) := by
  have htwo : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hj : (Real.sqrt (1 - 4 * a.m ^ 2 - 4 * a.n ^ 2)) ^ 2 =
      1 - 4 * a.m ^ 2 - 4 * a.n ^ 2 := Real.sq_sqrt (by nlinarith [a.disk])
  have hk20 : (2 : Fin 3) ≠ 0 := by decide
  have hk21 : (2 : Fin 3) ≠ 1 := by decide
  unfold A B C D M N P U V W choi
  simp_rw [feasible_sym_operation, feasible_operation]
  fin_cases j
  all_goals repeat' apply And.intro
  all_goals first | apply Complex.ext | skip
  all_goals norm_num [resultLabel, branchKraus, unit, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fin.sum_univ_three, flagSign,
      hk20, hk21, map_ofNat, Complex.mul_re, Complex.mul_im,
      Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail]
  all_goals try simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals ring_nf at hj ⊢
  all_goals simp only [htwo,hj]
  all_goals ring

private def signedAlpha (p : Parameters) (a : FeasiblePoint) (j : Qubit) : ℝ :=
  if j = 0 then p.beta * (2 * a.n ^ 2 - 1 / 2) - 2 * p.gamma * a.n
  else p.R * (p.beta * (1 / 2 - 2 * a.n ^ 2 - 4 * a.m ^ 2) + 2 * p.gamma * a.n)

private theorem feasible_coefficients (p : Parameters) (a : FeasiblePoint) (eps : ℝ)
    (j : Qubit) :
    F (symInstrument (feasibleInstrument a)) p.beta p.gamma (rate p.R j * eps) j =
      1 / 2 + eps * signedAlpha p a j ∧
    G (symInstrument (feasibleInstrument a)) p.beta p.gamma (rate p.R j * eps) j =
      2 * a.m ^ 2 * (1 - p.beta * rate p.R j * eps) ∧
    T (symInstrument (feasibleInstrument a)) p.beta p.gamma (rate p.R j * eps) j =
      (a.m * (1 - p.beta * rate p.R j * eps +
        (if j = 0 then -2 else 2) * p.gamma * a.n * rate p.R j * eps) : ℝ) := by
  rcases feasible_moments a j with ⟨hA,hC,hB,hD,hM,hN,hP,hU,hV,hW⟩
  simp only [F,G,T,hA,hC,hB,hD,hM,hN,hP,hU,hV,hW]
  fin_cases j <;> simp [signedAlpha,rate,Complex.mul_re,Complex.mul_im]
  all_goals repeat first | apply And.intro | exact True.intro
  all_goals push_cast
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

private theorem separated_root_remainder {x l k e u v r M : ℝ}
    (hx0 : 1 / 4 ≤ x) (hx1 : x ≤ 1) (hl0 : 1 / 2 ≤ l) (hl1 : l ≤ 3 / 4)
    (hk0 : -1 / 4 ≤ k) (hk1 : k ≤ 0) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hM : 0 ≤ M) (hu : |u| ≤ M) (hr : |r| ≤ M)
    (huv : |u - v| ≤ M * |x - l|)
    (hroot : x ^ 2 * (x - l) * (x - k) + e * u + e ^ 2 * r = 0) :
    |x - l + e * v / (l ^ 2 * (l - k))| ≤
      8 * (4 * (128 * M) ^ 2 + M * (128 * M) + M) * e ^ 2 := by
  have hx : 0 ≤ x := by linarith
  have hl : 0 ≤ l := by linarith
  have hdx : 1 / 64 ≤ x ^ 2 * (x - k) := by
    have hx2 : 1 / 16 ≤ x ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sub_nonneg.mpr (show 1 / 4 ≤ x - k by linarith))]
  have hdl : 1 / 8 ≤ l ^ 2 * (l - k) := by
    have hl2 : 1 / 4 ≤ l ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hl2) (sub_nonneg.mpr (show 1 / 2 ≤ l - k by linarith))]
  have hdx0 : 0 ≤ x ^ 2 * (x - k) := by linarith
  have hdl0 : 0 < l ^ 2 * (l - k) := by linarith
  have hsmall : |x - l| ≤ 128 * M * e := by
    have hh : x ^ 2 * (x - k) * |x - l| ≤ 2 * M * e := calc
      _ = |x ^ 2 * (x - l) * (x - k)| := by
        rw [show x ^ 2 * (x - l) * (x - k) = (x ^ 2 * (x - k)) * (x - l) by ring,
          abs_mul, abs_of_nonneg hdx0]
      _ = |-(e * u + e ^ 2 * r)| := congrArg abs (by linarith [hroot])
      _ ≤ |e * u| + |e ^ 2 * r| := by rw [abs_neg]; exact abs_add_le _ _
      _ ≤ e * M + e ^ 2 * M := by
        rw [abs_mul, abs_mul, abs_of_nonneg he0, abs_of_nonneg (sq_nonneg e)]
        gcongr
      _ ≤ 2 * M * e := by nlinarith [mul_nonneg hM (show 0 ≤ e * (1 - e) by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdx) (abs_nonneg (x - l))]
  have hdif : |l ^ 2 * (l - k) - x ^ 2 * (x - k)| ≤ 4 * |x - l| := by
    have hp0 : 0 ≤ x ^ 2 + x * l + l ^ 2 - k * (x + l) := by
      nlinarith [mul_nonneg hx hl, mul_nonpos_of_nonpos_of_nonneg hk1 (add_nonneg hx hl)]
    have hp1 : x ^ 2 + x * l + l ^ 2 - k * (x + l) ≤ 4 := by
      nlinarith [sq_nonneg (x - l), mul_nonneg (show 0 ≤ 1 - x by linarith)
        (show 0 ≤ 1 + x by linarith), mul_nonneg (show 0 ≤ 1 - l by linarith)
        (show 0 ≤ 1 + l by linarith), mul_nonneg (show 0 ≤ 1 - x by linarith)
        (show 0 ≤ 1 - l by linarith), mul_nonneg (show 0 ≤ k + 1 / 4 by linarith)
        (show 0 ≤ x + l by linarith)]
    rw [show l ^ 2 * (l - k) - x ^ 2 * (x - k) =
      -(x - l) * (x ^ 2 + x * l + l ^ 2 - k * (x + l)) by ring,
      abs_mul, abs_neg, abs_of_nonneg hp0]
    nlinarith [abs_nonneg (x - l)]
  have heq : l ^ 2 * (l - k) * (x - l + e * v / (l ^ 2 * (l - k))) =
      (l ^ 2 * (l - k) - x ^ 2 * (x - k)) * (x - l) + e * (v - u) - e ^ 2 * r := by
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hdl0)]
    nlinarith [hroot]
  have hbound : l ^ 2 * (l - k) * |x - l + e * v / (l ^ 2 * (l - k))| ≤
      (4 * (128 * M) ^ 2 + M * (128 * M) + M) * e ^ 2 := calc
    _ = |l ^ 2 * (l - k) * (x - l + e * v / (l ^ 2 * (l - k)))| := by
      rw [abs_mul, abs_of_pos hdl0]
    _ ≤ |l ^ 2 * (l - k) - x ^ 2 * (x - k)| * |x - l| +
        e * |v - u| + e ^ 2 * |r| := by
      rw [heq]
      calc
        _ ≤ |(l ^ 2 * (l - k) - x ^ 2 * (x - k)) * (x - l) + e * (v - u)| + |e ^ 2 * r| := abs_sub _ _
        _ ≤ _ := by
          grw [abs_add_le]
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0, abs_of_nonneg (sq_nonneg e)]
    _ ≤ 4 * |x - l| ^ 2 + e * (M * |x - l|) + e ^ 2 * M := by
      rw [abs_sub_comm v u]
      nlinarith [mul_nonneg (sub_nonneg.mpr hdif) (abs_nonneg (x - l)),
        mul_nonneg he0 (sub_nonneg.mpr huv), mul_nonneg (sq_nonneg e) (sub_nonneg.mpr hr)]
    _ ≤ _ := by
      have hs2 := sq_le_sq₀ (abs_nonneg (x - l)) (by positivity : 0 ≤ 128 * M * e) |>.mpr hsmall
      nlinarith [mul_nonneg (mul_nonneg he0 hM) (sub_nonneg.mpr hsmall)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hdl)
    (abs_nonneg (x - l + e * v / (l ^ 2 * (l - k))))]

private def alpha0 (p : Parameters) (m n : ℝ) := p.beta * (2 * n ^ 2 - 1 / 2) - 2 * p.gamma * n
private def alpha1 (p : Parameters) (m n : ℝ) := p.R * (p.beta * (1 / 2 - 2 * n ^ 2 - 4 * m ^ 2) + 2 * p.gamma * n)
private def tau0 (p : Parameters) (m n : ℝ) := m * (-p.beta - 2 * p.gamma * n)
private def tau1 (p : Parameters) (m n : ℝ) := p.R * m * (-p.beta + 2 * p.gamma * n)
private def kap0 (p : Parameters) (m : ℝ) := -2 * m ^ 2 * p.beta
private def kap1 (p : Parameters) (m : ℝ) := -2 * m ^ 2 * p.beta * p.R

private def realBlock (r l k d q a0 a1 t0 t1 g0 g1 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(r*q*(1-a0) : ℝ), (k*q*(1-t0) : ℝ), (r*d : ℝ), (k*d : ℝ);
     (k*q*(1-t0) : ℝ), (l*q*(1-g0) : ℝ), (k*d : ℝ), (l*d : ℝ);
     (r*d : ℝ), (k*d : ℝ), (r*(1-q)*(1-a1) : ℝ), (k*(1-q)*(1-t1) : ℝ);
     (k*d : ℝ), (l*d : ℝ), (k*(1-q)*(1-t1) : ℝ), (l*(1-q)*(1-g1) : ℝ)]

/-- The exact even matrix, with the original label first in its coordinate order. -/
def feasibleBlock (p : Parameters) (h m n q e : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  realBlock (1-h*e) (h*e) (Real.sqrt (1-h*e)*Real.sqrt (h*e))
    (Real.sqrt q*Real.sqrt (1-q)) q
    (1/2+e*alpha0 p m n) (1/2+e*alpha1 p m n)
    (m+e*tau0 p m n) (m+e*tau1 p m n)
    (2*m^2+e*kap0 p m) (2*m^2+e*kap1 p m)

private theorem block_hermitian (p : Parameters) (h m n q e : ℝ) :
    (feasibleBlock p h m n q e).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [feasibleBlock,realBlock,Matrix.conjTranspose_apply]

private def detBranch (r l q a t g z : ℝ) :=
  z^2+z*q*(r*a+l*g)+q^2*r*l*(a*g-t^2)
private def detNumerator (r l q a t g z : ℝ) := z + q*r*l*(a+g-2*t)
private def secular (r l q a0 a1 t0 t1 g0 g1 z : ℝ) :=
  detBranch r l q a0 t0 g0 z * detBranch r l (1-q) a1 t1 g1 z -
  q * detNumerator r l q a0 t0 g0 z * detBranch r l (1-q) a1 t1 g1 z -
  (1-q) * detNumerator r l (1-q) a1 t1 g1 z * detBranch r l q a0 t0 g0 z

private theorem block_determinant (r l k d q a0 a1 t0 t1 g0 g1 z : ℝ)
    (hrl : r+l=1) (hk : k^2=r*l) (hd : d^2=q*(1-q)) :
    ((Matrix.scalar (Fin 4) (z : ℂ)) - realBlock r l k d q a0 a1 t0 t1 g0 g1).det =
      (secular r l q a0 a1 t0 t1 g0 g1 z : ℝ) := by
  have hrEq : r=1-l := by linarith
  subst r
  have hk4 : k^4=((1-l)*l)^2 := by nlinarith [sq_nonneg (k^2-(1-l)*l)]
  have hd4 : d^4=(q*(1-q))^2 := by nlinarith [sq_nonneg (d^2-q*(1-q))]
  have hs0 : (0 : Fin 4).succAbove = ![1,2,3] := by
    funext i; fin_cases i <;> rfl
  have hs1 : (1 : Fin 4).succAbove = ![0,2,3] := by
    funext i; fin_cases i <;> rfl
  have hs2 : (2 : Fin 4).succAbove = ![0,1,3] := by
    funext i; fin_cases i <;> rfl
  have hs3 : (3 : Fin 4).succAbove = ![0,1,2] := by
    funext i; fin_cases i <;> rfl
  have hsu : (Fin.succ : Fin 3 → Fin 4) = ![1,2,3] := by
    funext i; fin_cases i <;> rfl
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, hs0,hs1,hs2,hs3,hsu]
  norm_num [realBlock, Matrix.scalar, Matrix.diagonal, Matrix.sub_apply,
    Matrix.one_apply, hs0,hs1,hs2,hs3,hsu, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]
  have hn01 : (0 : Fin 4) ≠ 1 := by decide
  have hn02 : (0 : Fin 4) ≠ 2 := by decide
  have hn03 : (0 : Fin 4) ≠ 3 := by decide
  have hn12 : (1 : Fin 4) ≠ 2 := by decide
  have hn13 : (1 : Fin 4) ≠ 3 := by decide
  have hn23 : (2 : Fin 4) ≠ 3 := by decide
  norm_num [hn01,hn02,hn03,hn12,hn13,hn23,Ne.symm hn01,Ne.symm hn02,
    Ne.symm hn03,Ne.symm hn12,Ne.symm hn13,Ne.symm hn23]
  unfold secular detBranch detNumerator
  norm_cast
  all_goals ring_nf
  all_goals try simp only [hk,hd,hk4,hd4]
  all_goals ring

private def branchTail (h m a t g q e z : ℝ) :=
  z*q*h*(g-a)+q^2*h*(2*m^2*a+g/2-2*m*t)+
  e*q^2*(h*(a*g-t^2)-h^2*(2*m^2*a+g/2-2*m*t))-
  e^2*q^2*h^2*(a*g-t^2)
private def numeratorTail (h m a t g q e : ℝ) :=
  q*(h*(a+g-2*t)-h^2*(1/2+2*m^2-2*m))-e*q*h^2*(a+g-2*t)
private def productTail (a0 a1 a2 b0 b1 b2 e : ℝ) :=
  a2*b0+a1*b1+a0*b2+e*(a2*b1+a1*b2)+e^2*a2*b2
private def traceOne (h m a : ℝ) := a-h/2+2*h*m^2
private def firstU (p : Parameters) (h m n q : ℝ) :=
  q*traceOne h m (alpha0 p m n)+(1-q)*traceOne h m (alpha1 p m n)
private def firstV (p : Parameters) (h m n q : ℝ) :=
  -q*(1-q)*(traceOne h m (alpha0 p m n)+traceOne h m (alpha1 p m n))/2-
    h*(1/2+2*m^2-2*m)*(q^2+(1-q)^2)
private def firstW (h m q : ℝ) := -h*(1/2+2*m^2-2*m)*q*(1-q)/2
private def firstCoeff (p : Parameters) (h m n q z : ℝ) :=
  z^3*firstU p h m n q+z^2*firstV p h m n q+z*firstW h m q
private def charTail (p : Parameters) (h m n q e z : ℝ) :=
  let d0 := z^2+z*q/2
  let d1 := z^2+z*(1-q)/2
  let c0 := z*q*traceOne h m (alpha0 p m n)
  let c1 := z*(1-q)*traceOne h m (alpha1 p m n)
  let r0 := branchTail h m (alpha0 p m n) (tau0 p m n) (kap0 p m) q e z
  let r1 := branchTail h m (alpha1 p m n) (tau1 p m n) (kap1 p m) (1-q) e z
  productTail d0 c0 r0 d1 c1 r1 e -
  q*productTail z (q*h*(1/2+2*m^2-2*m))
    (numeratorTail h m (alpha0 p m n) (tau0 p m n) (kap0 p m) q e) d1 c1 r1 e -
  (1-q)*productTail z ((1-q)*h*(1/2+2*m^2-2*m))
    (numeratorTail h m (alpha1 p m n) (tau1 p m n) (kap1 p m) (1-q) e) d0 c0 r0 e

private theorem secular_expansion (p : Parameters) (h m n q e z : ℝ) :
    secular (1-h*e) (h*e) q (1/2+e*alpha0 p m n) (1/2+e*alpha1 p m n)
      (m+e*tau0 p m n) (m+e*tau1 p m n) (2*m^2+e*kap0 p m) (2*m^2+e*kap1 p m) z =
    z^2*(z^2-z/2-3*q*(1-q)/4)+e*firstCoeff p h m n q z+e^2*charTail p h m n q e z := by
  unfold secular detBranch detNumerator firstCoeff firstU firstV firstW charTail
    productTail branchTail numeratorTail traceOne
  ring

/-- The separated positive eigenvalue at zero noise. -/
def lambdaPlus (q : ℝ) : ℝ := 1/4+Real.sqrt (1/16+3*q*(1-q)/4)
private def lambdaMinus (q : ℝ) : ℝ := 1/4-Real.sqrt (1/16+3*q*(1-q)/4)
private theorem base_roots {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1/2 ≤ lambdaPlus q ∧ lambdaPlus q ≤ 3/4 ∧
    -1/4 ≤ lambdaMinus q ∧ lambdaMinus q ≤ 0 ∧
    ∀ z : ℝ, z^2-z/2-3*q*(1-q)/4=(z-lambdaPlus q)*(z-lambdaMinus q) := by
  have hq : 0 ≤ q*(1-q) := mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hs := Real.sq_sqrt (show 0 ≤ 1/16+3*q*(1-q)/4 by positivity)
  have hn := Real.sqrt_nonneg (1/16+3*q*(1-q)/4)
  dsimp [lambdaPlus,lambdaMinus]
  refine ⟨by nlinarith,by nlinarith [sq_nonneg (q-1/2)],
    by nlinarith [sq_nonneg (q-1/2)],by nlinarith,?_⟩
  intro z
  nlinarith

private theorem characteristic_expansion (p : Parameters) (h m n q e z : ℝ)
    (hl : 0 ≤ h*e) (hr : h*e ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((Matrix.scalar (Fin 4) (z : ℂ)) - feasibleBlock p h m n q e).det =
      (z^2*(z-lambdaPlus q)*(z-lambdaMinus q)+e*firstCoeff p h m n q z+
        e^2*charTail p h m n q e z : ℝ) := by
  have hk : (Real.sqrt (1-h*e)*Real.sqrt (h*e))^2=(1-h*e)*(h*e) := by
    rw [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hr),Real.sq_sqrt hl]
  have hd : (Real.sqrt q*Real.sqrt (1-q))^2=q*(1-q) := by
    rw [mul_pow,Real.sq_sqrt hq0,Real.sq_sqrt (sub_nonneg.mpr hq1)]
  unfold feasibleBlock
  rw [block_determinant _ _ _ _ _ _ _ _ _ _ _ _ (by ring) hk hd,
    secular_expansion, (base_roots hq0 hq1).2.2.2.2 z]
  push_cast
  ring

private def top (p : Parameters) (h m n q e : ℝ) : ℝ :=
  (block_hermitian p h m n q e).eigenvalues₀ ⟨0,by simp⟩
private theorem top_greatest {Z : Matrix (Fin 4) (Fin 4) ℂ} (hZ : Z.IsHermitian) :
    IsGreatest (Set.range hZ.eigenvalues) (hZ.eigenvalues₀ ⟨0,by simp⟩) := by
  let f := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 4)))
  refine ⟨⟨f ⟨0,by simp⟩,by simp [Matrix.IsHermitian.eigenvalues,f]⟩,?_⟩
  rintro _ ⟨i,rfl⟩
  exact hZ.eigenvalues₀_antitone (Fin.zero_le _)

private theorem top_root (p : Parameters) (h m n q e : ℝ)
    (hl : 0 ≤ h*e) (hr : h*e ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    let z := top p h m n q e
    z^2*(z-lambdaPlus q)*(z-lambdaMinus q)+e*firstCoeff p h m n q z+
      e^2*charTail p h m n q e z=0 := by
  let hz := block_hermitian p h m n q e
  have hs : (top p h m n q e : ℂ) ∈ spectrum ℂ (feasibleBlock p h m n q e) := by
    rw [hz.spectrum_eq_image_range]
    exact ⟨top p h m n q e,(top_greatest hz).1,rfl⟩
  rw [Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly,Matrix.eval_charpoly,
    characteristic_expansion p h m n q e _ hl hr hq0 hq1] at hs
  simp only [isUnit_iff_ne_zero, not_not] at hs
  exact_mod_cast hs

private theorem top_at_zero (p : Parameters) (h m n q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : top p h m n q 0=lambdaPlus q := by
  obtain ⟨hl0,hl1,hk0,hk1,hroots⟩ := base_roots hq0 hq1
  have hs : (lambdaPlus q : ℂ) ∈ spectrum ℂ (feasibleBlock p h m n q 0) := by
    rw [Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly,Matrix.eval_charpoly,
      characteristic_expansion p h m n q 0 _ (by simp) (by simp) hq0 hq1]
    simp
  rw [(block_hermitian p h m n q 0).spectrum_eq_image_range] at hs
  obtain ⟨l,hl,heq⟩ := hs
  have heq' : l=lambdaPlus q := Complex.ofReal_injective heq
  have hle : lambdaPlus q ≤ top p h m n q 0 := by
    rw [← heq']; exact (top_greatest (block_hermitian p h m n q 0)).2 hl
  have hh := top_root p h m n q 0 (by simp) (by simp) hq0 hq1
  simp only [zero_mul,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hh
  rcases mul_eq_zero.mp hh with hh|hh
  · rcases mul_eq_zero.mp hh with hh|hh
    · nlinarith [sq_eq_zero_iff.mp hh]
    · exact sub_eq_zero.mp hh
  · nlinarith [sub_eq_zero.mp hh]

private theorem parameter_ball (p : Parameters) {h m n q e z : ℝ}
    (hh : 0 ≤ h) (hH : h ≤ p.H) (hm : |m| ≤ 1) (hn : |n| ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (![h,m,n,q,e,z] : Fin 6 → ℝ) ∈ Metric.closedBall 0 (p.H+2) := by
  rw [Metric.mem_closedBall,dist_eq_norm,sub_zero]
  apply (pi_norm_le_iff_of_nonneg (by linarith [p.H_pos])).mpr
  intro i
  fin_cases i <;> simp [Real.norm_eq_abs,abs_of_nonneg hh,abs_of_nonneg hq0,
    abs_of_nonneg he0,abs_of_nonneg hz0] <;> linarith [p.H_pos]

private theorem coefficient_budget (p : Parameters) : ∃ M : ℝ, 0 < M ∧
    ∀ h m n q e z : ℝ, 0 ≤ h → h ≤ p.H → |m| ≤ 1 → |n| ≤ 1 →
    0 ≤ q → q ≤ 1 → 0 ≤ e → e ≤ 1 → 0 ≤ z → z ≤ 1 →
    |firstU p h m n q|+|firstV p h m n q|+|firstW h m q|+
      |charTail p h m n q e z| ≤ M := by
  let f : (Fin 6 → ℝ) → ℝ := fun y =>
    |firstU p (y 0) (y 1) (y 2) (y 3)|+|firstV p (y 0) (y 1) (y 2) (y 3)|+
    |firstW (y 0) (y 1) (y 3)|+|charTail p (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)|
  have hf : Continuous f := by
    unfold f firstU firstV firstW charTail productTail branchTail numeratorTail traceOne
      alpha0 alpha1 tau0 tau1 kap0 kap1
    fun_prop
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Fin 6 → ℝ) (p.H+2)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨|M|+1,by positivity,?_⟩
  intro h m n q e z hh hH hm hn hq0 hq1 he0 he1 hz0 hz1
  have hb := hM (![h,m,n,q,e,z]) (parameter_ball p hh hH hm hn hq0 hq1 he0 he1 hz0 hz1)
  have hnon : 0 ≤ f (![h,m,n,q,e,z]) := by dsimp [f]; positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hnon] at hb
  dsimp [f] at hb
  linarith [le_abs_self M]

private theorem cubic_bounds {U V W M x l : ℝ}
    (hM : |U|+|V|+|W| ≤ M) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    |x^3*U+x^2*V+x*W| ≤ M ∧
    |(x^3*U+x^2*V+x*W)-(l^3*U+l^2*V+l*W)| ≤ 3*M*|x-l| := by
  have hc : ∀ a b c : ℝ, 0 ≤ a → a ≤ 3 → 0 ≤ b → b ≤ 3 → 0 ≤ c → c ≤ 3 →
      |a*U+b*V+c*W| ≤ 3*M := by
    intro a b c ha0 ha1 hb0 hb1 hc0 hc1
    calc
      _ ≤ |a*U|+|b*V|+|c*W| := (abs_add_le _ _).trans (by linarith [abs_add_le (a*U) (b*V)])
      _ = a*|U|+b*|V|+c*|W| := by rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg ha0,abs_of_nonneg hb0,abs_of_nonneg hc0]
      _ ≤ 3*M := by nlinarith [abs_nonneg U,abs_nonneg V,abs_nonneg W]
  constructor
  · calc
      _ ≤ |x^3*U|+|x^2*V|+|x*W| := (abs_add_le _ _).trans (by linarith [abs_add_le (x^3*U) (x^2*V)])
      _ = x^3*|U|+x^2*|V|+x*|W| := by simp [abs_mul,abs_of_nonneg hx0]
      _ ≤ M := by
        have hx2 : x^2 ≤ 1 := by nlinarith
        have hx3 : x^3 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx2) hx0]
        nlinarith [abs_nonneg U,abs_nonneg V,abs_nonneg W]
  · rw [show (x^3*U+x^2*V+x*W)-(l^3*U+l^2*V+l*W) =
      (x-l)*((x^2+x*l+l^2)*U+(x+l)*V+W) by ring,abs_mul]
    have ha : x^2+x*l+l^2 ≤ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hl1),
        sq_nonneg (x-l),mul_nonneg (sub_nonneg.mpr hx1) hx0,
        mul_nonneg (sub_nonneg.mpr hl1) hl0]
    have hb := hc (x^2+x*l+l^2) (x+l) 1 (by positivity) ha (by positivity) (by linarith) (by norm_num) (by norm_num)
    simp only [one_mul] at hb
    nlinarith [abs_nonneg (x-l)]

private theorem uniform_root_window (p : Parameters) : ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 1 ∧
    ∀ h m n q e : ℝ, 0 ≤ h → h ≤ p.H → |m| ≤ 1 → |n| ≤ 1 →
    0 ≤ q → q ≤ 1 → 0 ≤ e → e < e0 →
    1/4 ≤ top p h m n q e ∧ top p h m n q e ≤ 1 := by
  let f : (Fin 6 → ℝ) → (Fin 4 → Fin 4 → ℂ) := fun y i j =>
    feasibleBlock p (y 0) (y 1) (y 2) (y 3) (y 4) i j
  have hf : Continuous f := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;>
      dsimp [f,feasibleBlock,realBlock,alpha0,alpha1,tau0,tau1,kap0,kap1] <;> fun_prop
  have hu := (isCompact_closedBall (0 : Fin 6 → ℝ) (p.H+2)).uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (1/32) (by norm_num)
  refine ⟨min 1 d,lt_min (by norm_num) hd,min_le_left _ _,?_⟩
  intro h m n q e hh hH hm hn hq0 hq1 he0 he
  have he1 : e ≤ 1 := (he.trans_le (min_le_left _ _)).le
  have hb := hclose (![h,m,n,q,e,0]) (parameter_ball p hh hH hm hn hq0 hq1 he0 he1 (by norm_num) (by norm_num))
    (![h,m,n,q,0,0]) (parameter_ball p hh hH hm hn hq0 hq1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hdist : dist (![h,m,n,q,e,0] : Fin 6 → ℝ) (![h,m,n,q,0,0]) ≤ e := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg he0).mpr
    intro i; fin_cases i <;> simp [Real.norm_eq_abs,abs_of_nonneg he0,he0]
  have hb' := hb (hdist.trans_lt (he.trans_le (min_le_right _ _)))
  have hentry (i j : Fin 4) : ‖feasibleBlock p h m n q e i j-feasibleBlock p h m n q 0 i j‖ ≤ 1/32 := by
    have hc := (dist_le_pi_dist _ _ j).trans ((dist_le_pi_dist _ _ i).trans hb'.le)
    simpa [f,dist_eq_norm] using hc
  have hw := D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le
    (block_hermitian p h m n q 0) (block_hermitian p h m n q e) hentry ⟨0,by simp⟩
  change |top p h m n q e-top p h m n q 0| ≤ (4:ℝ)*(1/32) at hw
  rw [top_at_zero p h m n q hq0 hq1] at hw
  have hr := base_roots hq0 hq1
  exact ⟨by linarith [(abs_le.mp hw).1],by linarith [(abs_le.mp hw).2]⟩

def currentEven (p : Parameters) (x : CoupledPoint p) (a : FeasiblePoint)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  evenBlock (x.h*x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
    x.weights_nonneg x.weights_legal (feasibleInstrument a) (weightInput q)
    (by simp [weightInput,Fin.sum_univ_two,Complex.normSq_ofReal,Real.mul_self_sqrt hq0,
          Real.mul_self_sqrt (sub_nonneg.mpr hq1)])

private theorem actual_even_matrix (p : Parameters) (x : CoupledPoint p) (a : FeasiblePoint)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    currentEven p x a q hq0 hq1 =
      (feasibleBlock p x.h a.m a.n q x.eps).submatrix finProdFinEquiv finProdFinEquiv := by
  have hc : ∑ j, Complex.normSq (weightInput q j)=1 := by
    simp [weightInput,Fin.sum_univ_two,Complex.normSq_ofReal,Real.mul_self_sqrt hq0,
      Real.mul_self_sqrt (sub_nonneg.mpr hq1)]
  obtain ⟨hE,-⟩ := even_error_eq_top_eigenvalue (x.h*x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
    x.weights_nonneg x.weights_legal (feasibleInstrument a) (weightInput q) hc
  have hq := Real.sq_sqrt hq0
  have hq' := Real.sq_sqrt (sub_nonneg.mpr hq1)
  unfold currentEven
  ext ⟨j,i⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases l
  all_goals first
    | erw [upper_entry]
    | erw [cross_entry]
    | erw [lower_entry]
    | erw [← hE.apply]; erw [cross_entry]
  all_goals try simp only [CoupledPoint.weights]
  all_goals try simp only [(feasible_coefficients p a x.eps _).1,
    (feasible_coefficients p a x.eps _).2.1,(feasible_coefficients p a x.eps _).2.2]
  all_goals fin_cases j <;> fin_cases k <;>
    simp [feasibleBlock,realBlock,Matrix.submatrix_apply,finProdFinEquiv,
      weightInput,rate,signedAlpha,alpha0,alpha1,tau0,tau1,kap0,kap1,
      Complex.mul_re,Complex.mul_im]
  all_goals push_cast
  all_goals ring_nf
  all_goals try simp only [← Complex.ofReal_pow,hq,hq']
  all_goals push_cast
  all_goals first | exact Or.inl True.intro | ring

/-- The coefficient obtained from the actual characteristic polynomial at the isolated base root. -/
def spectralSlope (p : Parameters) (h m n q : ℝ) : ℝ :=
  -firstCoeff p h m n q (lambdaPlus q)/((lambdaPlus q)^2*(lambdaPlus q-lambdaMinus q))

/-- All reference weights have one common quadratic remainder, including the two endpoints. -/
theorem uniform_feasible_spectral_envelope (p : Parameters) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧
      ∀ (x : CoupledPoint p) (a : FeasiblePoint), x.eps < e0 →
      ∀ q : ℝ, ∀ hq0 : 0 ≤ q, ∀ hq1 : q ≤ 1,
      ∃ hE : (currentEven p x a q hq0 hq1).IsHermitian,
        ∃ t : ℝ, IsGreatest (Set.range hE.eigenvalues) t ∧
        |t-lambdaPlus q-x.eps*spectralSlope p x.h a.m a.n q| ≤ C*x.eps^2 := by
  obtain ⟨M,hM,hbudget⟩ := coefficient_budget p
  obtain ⟨e0,he0,he1,hwindow⟩ := uniform_root_window p
  let K := 3*M
  let C := 8*(4*(128*K)^2+K*(128*K)+K)
  refine ⟨C,e0,by dsimp [C,K]; positivity,he0,?_⟩
  intro x a he q hq0 hq1
  have hm : |a.m| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [a.disk,sq_nonneg a.n]
  have hn : |a.n| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [a.disk,sq_nonneg a.m]
  obtain ⟨hx0,hx1⟩ := hwindow x.h a.m a.n q x.eps x.h_nonneg x.h_le hm hn hq0 hq1 x.eps_pos.le he
  obtain ⟨hl0,hl1,hk0,hk1,-⟩ := base_roots hq0 hq1
  have hb := hbudget x.h a.m a.n q x.eps (top p x.h a.m a.n q x.eps)
    x.h_nonneg x.h_le hm hn hq0 hq1 x.eps_pos.le (he.le.trans he1) (by linarith) hx1
  have hsum : |firstU p x.h a.m a.n q|+|firstV p x.h a.m a.n q|+|firstW x.h a.m q| ≤ M :=
    le_trans (le_add_of_nonneg_right (abs_nonneg _)) hb
  obtain ⟨hu,hul⟩ := cubic_bounds hsum (by linarith : 0 ≤ top p x.h a.m a.n q x.eps) hx1
    (by linarith : 0 ≤ lambdaPlus q) (by linarith : lambdaPlus q ≤ 1)
  have hroot := top_root p x.h a.m a.n q x.eps
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le hq0 hq1
  have hr : |charTail p x.h a.m a.n q x.eps (top p x.h a.m a.n q x.eps)| ≤ K := by
    dsimp [K]; linarith [abs_nonneg (firstU p x.h a.m a.n q),
      abs_nonneg (firstV p x.h a.m a.n q),abs_nonneg (firstW x.h a.m q)]
  have hbound := separated_root_remainder hx0 hx1 hl0 hl1 hk0 hk1 x.eps_pos.le
    (he.le.trans he1) (show 0 ≤ K by dsimp [K]; positivity)
    (show |firstCoeff p x.h a.m a.n q (top p x.h a.m a.n q x.eps)| ≤ K by
      dsimp [firstCoeff,K]; linarith) hr hul hroot
  let hE : (currentEven p x a q hq0 hq1).IsHermitian := by
    rw [actual_even_matrix]; exact (block_hermitian p x.h a.m a.n q x.eps).submatrix _
  have hrange : Set.range hE.eigenvalues =
      Set.range (block_hermitian p x.h a.m a.n q x.eps).eigenvalues := by
    rw [← hE.spectrum_real_eq_range_eigenvalues,
      ← (block_hermitian p x.h a.m a.n q x.eps).spectrum_real_eq_range_eigenvalues]
    rw [actual_even_matrix]
    exact AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℂ finProdFinEquiv.symm) _
  refine ⟨hE,top p x.h a.m a.n q x.eps,?_,?_⟩
  · rw [hrange]; exact top_greatest _
  · convert hbound using 1 <;> dsimp [spectralSlope,C,firstCoeff] <;> congr 1 <;> ring

private theorem uniform_slope_lipschitz (p : Parameters) : ∃ L : ℝ, 0 ≤ L ∧
    ∀ h m n q : ℝ, 0 ≤ h → h ≤ p.H → |m| ≤ 1 → |n| ≤ 1 → 0 ≤ q → q ≤ 1 →
    |spectralSlope p h m n q-spectralSlope p h m n (1/2)| ≤ L*|q-1/2| := by
  let lo : Fin 4 → ℝ := ![0,-1,-1,0]
  let hi : Fin 4 → ℝ := ![p.H,1,1,1]
  let f : (Fin 4 → ℝ) → ℝ := fun y => spectralSlope p (y 0) (y 1) (y 2) (y 3)
  have hf : ∀ y ∈ Set.Icc lo hi, ContDiffAt ℝ 1 f y := by
    intro y hy
    have hq0 : 0 ≤ y 3 := hy.1 3
    have hq1 : y 3 ≤ 1 := hy.2 3
    obtain ⟨hl0,hl1,hk0,hk1,-⟩ := base_roots hq0 hq1
    have hs : 1/16+3*y 3*(1-y 3)/4 ≠ 0 := by
      nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
    have hd : (lambdaPlus (y 3))^2*(lambdaPlus (y 3)-lambdaMinus (y 3)) ≠ 0 := by
      have hl : 0 < lambdaPlus (y 3) := by linarith
      have hk : 0 < lambdaPlus (y 3)-lambdaMinus (y 3) := by linarith
      positivity
    dsimp [f,spectralSlope,firstCoeff,firstU,firstV,firstW,traceOne,alpha0,alpha1,
      lambdaPlus,lambdaMinus] at hd ⊢
    fun_prop (disch := assumption)
  have hc : ContinuousOn (fderiv ℝ f) (Set.Icc lo hi) := fun y hy =>
    ((hf y hy).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨L,hL⟩ := (isCompact_Icc : IsCompact (Set.Icc lo hi)).exists_bound_of_continuousOn hc
  refine ⟨|L|,abs_nonneg _,?_⟩
  intro h m n q hh hH hm hn hq0 hq1
  have hmem (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      (![h,m,n,t] : Fin 4 → ℝ) ∈ Set.Icc lo hi := by
    constructor <;> intro i <;> fin_cases i <;> simp [lo,hi]
    all_goals first | assumption | exact (abs_le.mp hm).1 | exact (abs_le.mp hm).2 |
      exact (abs_le.mp hn).1 | exact (abs_le.mp hn).2
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hf y hy).differentiableAt (by norm_num)) hL (convex_Icc lo hi)
    (hmem (1/2) (by norm_num) (by norm_num)) (hmem q hq0 hq1)
  have hd : ‖(![h,m,n,q] : Fin 4 → ℝ)-![h,m,n,1/2]‖ ≤ |q-1/2| := by
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i; fin_cases i <;> simp [Real.norm_eq_abs]
  dsimp [f] at hb
  calc
    _ ≤ L*‖(![h,m,n,q] : Fin 4 → ℝ)-![h,m,n,1/2]‖ := hb
    _ ≤ |L| * |q-1/2| := by
      exact (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hd (abs_nonneg L))

def feasibleSlope (p : Parameters) (h m n : ℝ) : ℝ :=
  7*h/12-p.beta*(p.R-1)/8-4*h*m/3+(h/3+p.beta*p.R)*m^2+
    (p.R-1)*(p.beta*n^2-p.gamma*n)/2
private theorem slope_center (p : Parameters) (h m n : ℝ) :
    spectralSlope p h m n (1/2)=feasibleSlope p h m n := by
  have hs : Real.sqrt (1/16+3*(1/2:ℝ)*(1-1/2)/4)=1/2 := by
    norm_num [Real.sqrt_eq_iff_eq_sq]
  unfold spectralSlope firstCoeff firstU firstV firstW traceOne alpha0 alpha1
    lambdaPlus lambdaMinus feasibleSlope
  rw [hs]
  ring
private theorem base_curvature {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    lambdaPlus q ≤ 3/4-3*(q-1/2)^2/4 := by
  have hq := mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hs := Real.sq_sqrt (show 0 ≤ 1/16+3*q*(1-q)/4 by positivity)
  have hn := Real.sqrt_nonneg (1/16+3*q*(1-q)/4)
  have hbd : (q-1/2)^2 ≤ 1/4 := by nlinarith
  have hfour := sq_nonneg ((q-1/2)^2)
  dsimp [lambdaPlus]
  nlinarith

/-- The feasible family's complete-reference error has a uniform quadratic remainder. -/
theorem uniform_feasible_error (p : Parameters) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧
      ∀ (x : CoupledPoint p) (a : FeasiblePoint), x.eps < e0 →
      |x.error (feasibleInstrument a)-3/4-x.eps*feasibleSlope p x.h a.m a.n| ≤ C*x.eps^2 := by
  obtain ⟨C,e0,hC,he0,henv⟩ := uniform_feasible_spectral_envelope p
  obtain ⟨L,hL,hlip⟩ := uniform_slope_lipschitz p
  refine ⟨C+L^2+1,e0,by positivity,he0,?_⟩
  intro x a he
  have hm : |a.m| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [a.disk,sq_nonneg a.n]
  have hn : |a.n| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [a.disk,sq_nonneg a.m]
  obtain ⟨q,hq0,hq1,hQ,hmax,hall⟩ := diamond_eq_even_spectral_max
    (x.h*x.eps) p.beta p.gamma x.weights (mul_nonneg x.h_nonneg x.eps_pos.le)
    x.ell_le p.beta_pos x.weights_nonneg x.weights_legal (feasibleInstrument a)
  obtain ⟨hE,t,ht,hbound⟩ := henv x a he q hq0 hq1
  have heq : x.error (feasibleInstrument a)=t := hmax.unique ht
  have hupper := (abs_le.mp hbound).2
  have hbase := base_curvature hq0 hq1
  have hsl := hlip x.h a.m a.n q x.h_nonneg x.h_le hm hn hq0 hq1
  rw [slope_center] at hsl
  have hu : x.error (feasibleInstrument a)-3/4-x.eps*feasibleSlope p x.h a.m a.n ≤
      (C+L^2+1)*x.eps^2 := by
    rw [heq]
    have hs := (abs_le.mp hsl).2
    have hscale := mul_nonneg x.eps_pos.le (sub_nonneg.mpr hs)
    have hsq := sq_nonneg (3*|q-1/2|-2*L*x.eps)
    nlinarith [sq_abs (q-1/2),sq_nonneg x.eps,mul_nonneg (sq_nonneg L) (sq_nonneg x.eps)]
  obtain ⟨hE0,t0,ht0,hbound0⟩ := henv x a he (1/2) (by norm_num) (by norm_num)
  obtain ⟨hT,hTbound⟩ := hall (1/2) (by norm_num) (by norm_num)
  obtain ⟨i,hi⟩ := ht0.1
  have ht0le : t0 ≤ x.error (feasibleInstrument a) := hi ▸ hTbound i
  have hhalf : lambdaPlus (1/2)=3/4 := by
    norm_num [lambdaPlus,Real.sqrt_eq_iff_eq_sq]
  rw [hhalf,slope_center] at hbound0
  have hlower : -((C+L^2+1)*x.eps^2) ≤
      x.error (feasibleInstrument a)-3/4-x.eps*feasibleSlope p x.h a.m a.n := by
    nlinarith [(abs_le.mp hbound0).1,
      mul_nonneg (sq_nonneg L) (sq_nonneg x.eps),sq_nonneg x.eps]
  exact abs_le.mpr ⟨hlower,hu⟩

/-- The error of an arbitrary common CPTP decoder; the memory is only a reference. -/
def decoderError (p : Parameters) (x : CoupledPoint p)
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) : ℝ :=
  D5.S3.Quantum.Foundation.FiniteDiamondDistance.diamondDistance
    (targetChannel (x.h*x.eps) (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le)
    ((receiverChannel (M := Qubit) D).comp
      (sourceChannel (x.h*x.eps) p.beta p.gamma x.weights
        (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos x.weights_nonneg x.weights_legal))/2

/-- The infimum ranges over every receiver CPTP channel, without a Kraus-rank restriction. -/
def optimalError (p : Parameters) (x : CoupledPoint p) : ℝ := sInf (Set.range (decoderError p x))

private theorem optimal_le_feasible (p : Parameters) (x : CoupledPoint p) (a : FeasiblePoint) :
    optimalError p x ≤ x.error (feasibleInstrument a) := by
  have hb : BddBelow (Set.range (decoderError p x)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨D,rfl⟩
    exact div_nonneg (PhaseBoundaryReferenceReduction.distance_nonnegative _ _) (by norm_num)
  apply csInf_le hb
  exact ⟨PhaseBoundaryReferenceReduction.flagSymmetrizedDecoder (instrumentRealization (feasibleInstrument a)),rfl⟩

/-- A minimizer of the signed feasible family gives a uniform bound on the all-CPTP infimum. -/
theorem uniform_optimal_upper_bound (p : Parameters) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧
      (∀ h : ℝ, Phi p h ≤ p.beta*(p.R+1)/8) ∧
      ∀ x : CoupledPoint p, x.eps < e0 →
        optimalError p x ≤ 3/4+x.eps*Phi p x.h+C*x.eps^2 := by
  obtain ⟨C,e0,hC,he0,herr⟩ := uniform_feasible_error p
  refine ⟨C,e0,hC,he0,?_,?_⟩
  · intro h
    obtain ⟨m,n,hm,hn,hd,hPhi,hmin⟩ := disk_minimum p h
    rw [hPhi]
    convert hmin (1/2) 0 (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      unfold diskQ <;> ring
  · intro x he
    obtain ⟨m,n,hm,hn,hd,hPhi,hmin⟩ := disk_minimum p x.h
    let a : FeasiblePoint := ⟨m,if p.gamma < 0 then -n else n,hm,
      by split_ifs <;> simpa using hd⟩
    have hs : feasibleSlope p x.h a.m a.n=Phi p x.h := by
      rw [hPhi]
      dsimp [a,feasibleSlope,diskQ]
      split_ifs with hg
      · rw [abs_of_neg hg] <;> ring
      · rw [abs_of_nonneg (le_of_not_gt hg)] <;> ring
    have hh := (abs_le.mp (herr x a he)).2
    rw [hs] at hh
    linarith [optimal_le_feasible p x a]

end D5.S3.Quantum.Recovery.PhaseBoundaryUniformFeasibleRecovery
