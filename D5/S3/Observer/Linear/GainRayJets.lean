/- GID: D5/S3/Observer/Linear/GainRayJets
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayJets
   mirror-E: none(waiver:nonzero-node-euler-interpolation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.FieldDivision]
   utility: none
   digest: Shifted Euler interpolation at distinct nodes constructs one fixed matrix recovering the whole gain vector on the literal pure-M trajectory. -/

import D5.S3.Observer.Linear.GainRayHistory
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Shifted Euler interpolation and its exact native gain-ray readout.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

abbrev phi : ℝ := Real.goldenRatio
abbrev psi : ℝ := Real.goldenConj

def spectralPlus : Mat := (phi - psi)⁻¹ • (action false - psi • (1 : Mat))
def spectralMinus : Mat := (phi - psi)⁻¹ • (phi • (1 : Mat) - action false)
def alpha (S : Mat) : ℝ := Matrix.trace (spectralPlus * S)
def eta (S : Mat) : ℝ := Matrix.trace (spectralMinus * S)

private theorem spectral_gap : 0 < phi - psi :=
  sub_pos.mpr (lt_trans Real.goldenConj_neg Real.goldenRatio_pos)

private theorem spectral_sum : spectralPlus + spectralMinus = (1 : Mat) := by
  unfold spectralPlus spectralMinus
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  <;> ring

private theorem spectral_power (i : ℕ) :
    action false ^ i = phi ^ i • spectralPlus + psi ^ i • spectralMinus := by
  cases i with
  | zero => simpa using spectral_sum.symm
  | succ k =>
    have packet := (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2
      1 (by omega) (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.atomicBlock (k+1))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (k+1) rfl
    have hv := packet.2.2.2.2.1 (by omega)
    have hp := packet.2.2.2.2.2.1
    have hm := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ =>
      A.map (Int.castRingHom ℝ)) hp.symm
    rw [Matrix.map_pow] at hm
    change action false ^ (k+1) = _ at hm
    rw [hm, ← Real.goldenRatio_mul_fib_succ_add_fib,
      ← Real.goldenConj_mul_fib_succ_add_fib]
    have hz : phi - psi ≠ 0 := ne_of_gt spectral_gap
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.blockMatrix,
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step, hv,
        spectralPlus, spectralMinus, action,
        D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM]
    all_goals field_simp
    all_goals ring

/-- The expansion is for the source-weighted trace, on every auxiliary matrix. -/
theorem pureM_spectral (S : Mat) (i : ℕ) :
    Matrix.trace (acquisition (List.replicate i false) * S) =
      alpha S * phi ^ i + eta S * psi ^ i := by
  rw [acquisition_pure, spectral_power, Matrix.add_mul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  simp only [alpha, eta, smul_eq_mul]
  ring

/-- Only the expanding source weight has a positivity requirement. -/
theorem legal_spectral_weights (P : Mat) (hP : LegalSource P) :
    0 < alpha P ∧ alpha P + eta P = 1 := by
  have hsum : alpha P + eta P = Matrix.trace P := by
    rw [alpha, eta, ← Matrix.trace_add, ← Matrix.add_mul, spectral_sum, one_mul]
  refine ⟨?_, hsum.trans hP.2.2⟩
  have hi : 0 < (phi - psi)⁻¹ := inv_pos.mpr spectral_gap
  have hp (i j : Fin 2) : 0 < spectralPlus i j := by
    change 0 < (phi - psi)⁻¹ * (action false - psi • (1 : Mat)) i j
    apply mul_pos hi
    fin_cases i <;> fin_cases j <;>
      norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM] <;>
      linarith [Real.goldenConj_neg]
  unfold alpha
  simpa [Matrix.trace, Matrix.mul_apply, dotProduct, Fin.sum_univ_two] using
    add_pos (add_pos (mul_pos (hp 0 0) (hP.1 0 0))
      (mul_pos (hp 0 1) (hP.1 1 0)))
      (add_pos (mul_pos (hp 1 0) (hP.1 0 1)) (mul_pos (hp 1 1) (hP.1 1 1)))

/-- Auxiliary projectors separate the two source functionals in universal identities. -/
theorem spectral_basis_weights :
    alpha spectralPlus = 1 ∧ eta spectralPlus = 0 ∧
      alpha spectralMinus = 0 ∧ eta spectralMinus = 1 := by
  have hψ : psi = 1 - phi := by linarith [Real.goldenRatio_add_goldenConj]
  have hz : phi - psi ≠ 0 := ne_of_gt spectral_gap
  have hsq := Real.goldenRatio_sq
  unfold alpha eta spectralPlus spectralMinus
  norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, dotProduct, Fin.sum_univ_two]
  rw [hψ] at hz ⊢
  field_simp
  repeat' constructor
  all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- Every bounded prefix uses its original clock, including the initial clock zero. -/
theorem pureM_readAt {d : ℕ} (W : World d) (n i : ℕ) (hi : i ≤ n) :
    readAt W (List.replicate n false) i =
      (gain d W.coeff).eval (i : ℝ) *
        (alpha W.source * phi ^ i + eta W.source * psi ^ i) + W.drift := by
  simp only [readAt, List.take_replicate, min_eq_left hi]
  rw [pureM_spectral]


/-- A shift changes polynomial coefficients used by the readout, never its clocks. -/
def euler (s : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := p.derivative * X + s • p
  map_add' p q := by simp [add_mul]; abel
  map_smul' a p := by simp [smul_mul_assoc, smul_add, smul_comm a s]

def jet (s : ℝ) (j : ℕ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  ((euler s ^ j) p).eval x

private theorem euler_coeff (s : ℝ) (p : ℝ[X]) (i : ℕ) :
    (euler s p).coeff i = ((i : ℝ) + s) * p.coeff i := by
  cases i with
  | zero => simp [euler]
  | succ i =>
    simp [euler, coeff_mul_X, coeff_derivative, Nat.cast_add, Nat.cast_one]
    ring

private theorem euler_ofFn (s : ℝ) (n : ℕ) (c : Fin n → ℝ) :
    euler s (ofFn n c) = ofFn n (fun i => ((i : ℝ) + s) * c i) := by
  ext i
  rw [euler_coeff]
  by_cases hi : i < n
  · simp [hi]
  · simp [Nat.le_of_not_gt hi]

private theorem euler_pow_ofFn (s : ℝ) (j n : ℕ) (c : Fin n → ℝ) :
    (euler s ^ j) (ofFn n c) = ofFn n (fun i => ((i : ℝ) + s) ^ j * c i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, euler_ofFn]
    congr 1
    ext i
    simp only [pow_succ]
    ring

/-- The exact coefficient identity includes 0^0=1 at the initial read. -/
theorem jet_ofFn (s : ℝ) (j n : ℕ) (c : Fin n → ℝ) (x : ℝ) :
    jet s j (ofFn n c) x = ∑ i : Fin n, c i * ((i : ℝ) + s) ^ j * x ^ (i : ℕ) := by
  rw [jet, euler_pow_ofFn]
  simp [ofFn_eq_sum_monomial, eval_finsetSum, mul_comm]

private theorem jet_shift (s : ℝ) (j : ℕ) (p : ℝ[X]) (x : ℝ) :
    jet s j (euler s p) x = jet s (j + 1) p x := by
  simp [jet, pow_succ, Module.End.mul_apply]

private theorem derivative_euler (s : ℝ) (n : ℕ) (p : ℝ[X]) :
    derivative^[n] (euler s p) =
      (derivative^[n + 1] p) * X + ((n : ℝ) + s) • (derivative^[n] p) := by
  change derivative^[n] (p.derivative * X + s • p) = _
  have hadd : derivative^[n] (p.derivative * X + s • p) =
      derivative^[n] (p.derivative * X) + derivative^[n] (s • p) := by
    simpa only [Module.End.pow_apply] using
      (Polynomial.derivative (R := ℝ) ^ n).map_add (p.derivative * X) (s • p)
  rw [hadd, iterate_derivative_derivative_mul_X, iterate_derivative_smul]
  simp only [add_smul, Nat.cast_smul_eq_nsmul]
  abel

private theorem ordinary_of_euler (s x : ℝ) (hx : x ≠ 0) (n : ℕ) (p : ℝ[X])
    (h : ∀ j ≤ n, jet s j p x = 0) : (derivative^[n] p).eval x = 0 := by
  induction n generalizing p with
  | zero => simpa [jet] using h 0 le_rfl
  | succ n ih =>
    have hp : (derivative^[n] p).eval x = 0 := ih p (fun j hj => h j (by omega))
    have he : (derivative^[n] (euler s p)).eval x = 0 :=
      ih (euler s p) (fun j hj => (jet_shift s j p x).trans (h (j + 1) (by omega)))
    rw [derivative_euler, eval_add, eval_mul, eval_X, eval_smul, hp, smul_zero,
      add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hx

private theorem euler_of_ordinary (s x : ℝ) (n : ℕ) (p : ℝ[X])
    (h : ∀ j ≤ n, (derivative^[j] p).eval x = 0) : jet s n p x = 0 := by
  induction n generalizing p with
  | zero => simpa [jet] using h 0 le_rfl
  | succ n ih =>
    rw [← jet_shift]
    apply ih
    intro j hj
    rw [derivative_euler, eval_add, eval_mul, eval_X, eval_smul,
      h (j + 1) (by omega), h j (by omega)]
    simp

/-- Both D and D+1 have the same finite vanishing jets as ordinary derivatives. -/
theorem jets_vanish_iff (s x : ℝ) (hx : x ≠ 0) (d : ℕ) (p : ℝ[X]) :
    (∀ j ≤ d, jet s j p x = 0) ↔
      ∀ j ≤ d, (derivative^[j] p).eval x = 0 := by
  constructor
  · intro h j hj
    exact ordinary_of_euler s x hx j p (fun k hk => h k (hk.trans hj))
  · intro h j hj
    exact euler_of_ordinary s x j p (fun k hk => h k (hk.trans hj))

/-- With the lower ordinary jets zero, the remaining diagonal factor is exactly x^n. -/
theorem jet_leading (s x : ℝ) (n : ℕ) (p : ℝ[X])
    (h : ∀ j < n, (derivative^[j] p).eval x = 0) :
    jet s n p x = x ^ n * (derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp [jet]
  | succ n ih =>
    rw [← jet_shift, ih]
    · rw [derivative_euler, eval_add, eval_mul, eval_X, eval_smul, h n (by omega)]
      simp only [smul_zero, add_zero, pow_succ]
      ring
    · intro j hj
      rw [derivative_euler, eval_add, eval_mul, eval_X, eval_smul,
        h (j + 1) (by omega), h j (by omega)]
      simp

/-- The multiple-root conclusion has no coefficient or degree nondegeneracy premise. -/
theorem jets_root_dvd (s x : ℝ) (hx : x ≠ 0) (d : ℕ) (p : ℝ[X])
    (h : ∀ j ≤ d, jet s j p x = 0) : (X - C x) ^ (d + 1) ∣ p := by
  by_cases hp : p = 0
  · simp [hp]
  have hr := lt_rootMultiplicity_of_isRoot_iterate_derivative hp
    ((jets_vanish_iff s x hx d p).mp h)
  exact (pow_dvd_pow _ (by omega : d + 1 ≤ p.rootMultiplicity x)).trans
    (pow_rootMultiplicity_dvd p x)

abbrev JetIndex (d : ℕ) := Fin (d + 1) ⊕ (Fin (d + 1) ⊕ Unit)

/-- The last condition is the drift-annihilating value at a third node. -/
def jetMatrix (d n : ℕ) (s a b c : ℝ) : Matrix (JetIndex d) (Fin n) ℝ :=
  fun j i => match j with
    | .inl k => ((i : ℝ) + s) ^ (k : ℕ) * a ^ (i : ℕ)
    | .inr (.inl k) => ((i : ℝ) + s) ^ (k : ℕ) * b ^ (i : ℕ)
    | .inr (.inr _) => c ^ (i : ℕ)

def jetMap (d n : ℕ) (s a b c : ℝ) := (jetMatrix d n s a b c).mulVecLin

private theorem jetMap_apply (d n : ℕ) (s a b c : ℝ) (v : Fin n → ℝ) :
    (∀ j : Fin (d + 1), jetMap d n s a b c v (.inl j) =
      jet s j (ofFn n v) a) ∧
    (∀ j : Fin (d + 1), jetMap d n s a b c v (.inr (.inl j)) =
      jet s j (ofFn n v) b) ∧
    jetMap d n s a b c v (.inr (.inr ())) = (ofFn n v).eval c := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [jet_ofFn]
    simp [jetMap, jetMatrix, Matrix.mulVecLin, Matrix.mulVec, dotProduct,
      mul_comm, mul_left_comm]
  · intro j
    rw [jet_ofFn]
    simp [jetMap, jetMatrix, Matrix.mulVecLin, Matrix.mulVec, dotProduct,
      mul_comm, mul_left_comm]
  · simp [jetMap, jetMatrix, Matrix.mulVecLin, Matrix.mulVec, dotProduct,
      ofFn_eq_sum_monomial, eval_finsetSum, mul_comm]

private theorem three_node_dvd (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (d : ℕ) (p : ℝ[X]) (ha : (X - C a) ^ (d + 1) ∣ p)
    (hb : (X - C b) ^ (d + 1) ∣ p) (hc : p.eval c = 0) :
    ((X - C a) ^ (d + 1) * (X - C b) ^ (d + 1)) * (X - C c) ∣ p := by
  have hab' := (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab)))
  have hac' := (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hac)))
  have hbc' := (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hbc)))
  exact (hac'.pow_left.mul_left hbc'.pow_left).mul_dvd
    (hab'.pow.mul_dvd ha hb) (dvd_iff_isRoot.mpr hc)

/-- The square system is onto for all shifted Euler jets, with no external Hermite dependency. -/
theorem jetMap_bijective (d : ℕ) (s a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Bijective (jetMap d (2 * (d + 1)+1) s a b c) := by
  have hinj : Function.Injective (jetMap d (2 * (d + 1)+1) s a b c) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have ht := jetMap_apply d (2 * (d + 1)+1) s a b c v
    have hrootA : ∀ j ≤ d, jet s j (ofFn (2 * (d + 1)+1) v) a = 0 := by
      intro j hj
      rw [← ht.1 ⟨j, by omega⟩, hv]
      rfl
    have hrootB : ∀ j ≤ d, jet s j (ofFn (2 * (d + 1)+1) v) b = 0 := by
      intro j hj
      rw [← ht.2.1 ⟨j, by omega⟩, hv]
      rfl
    have hrootC : (ofFn (2 * (d + 1)+1) v).eval c = 0 := by rw [← ht.2.2, hv]; rfl
    have hdvd := three_node_dvd a b c hab hac hbc d _
      (jets_root_dvd s a ha d _ hrootA) (jets_root_dvd s b hb d _ hrootB) hrootC
    have hp : ofFn (2 * (d + 1)+1) v = 0 := by
      by_contra hp
      have hle := natDegree_le_of_dvd hdvd hp
      have hdeg : (((X - C a) ^ (d + 1) * (X - C b) ^ (d + 1)) *
          (X - C c) : ℝ[X]).natDegree = 2 * (d + 1)+1 := by
        simp [natDegree_mul, natDegree_pow, X_sub_C_ne_zero]
        omega
      rw [hdeg] at hle
      have hlt := ofFn_natDegree_lt (by omega : 0 < 2 * (d + 1)+1) v
      omega
    exact (injective_ofFn _ (hp.trans (by simp)))
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [JetIndex, Module.finrank_pi_fintype]; omega)).mp hinj⟩

private theorem golden_interpolation (d : ℕ) :
    Function.Surjective (jetMap d ((List.replicate (2 * (d + 1)) false).length+1)
      0 phi psi 1) := by
  convert
    (jetMap_bijective d 0 phi psi 1 Real.goldenRatio_ne_zero Real.goldenConj_ne_zero
      (ne_of_gt (lt_trans Real.goldenConj_neg Real.goldenRatio_pos))
      (ne_of_gt Real.one_lt_goldenRatio)
      (ne_of_lt (lt_trans Real.goldenConj_neg zero_lt_one))).2 using 1
  rw [List.length_replicate]

private def betaCondition (d : ℕ) (k : Fin (d + 1)) : JetIndex d → ℝ
  | .inl j => if j = k then 1 else 0
  | .inr (.inl j) => if j = k then 1 else 0
  | .inr (.inr _) => 0

/-- Its entries depend only on the declared degree and the two fixed atoms. -/
def exactBetaReadout (d : ℕ) : Readout d (List.replicate (2 * (d + 1)) false) :=
  fun k => Function.surjInv (golden_interpolation d) (betaCondition d k)

private theorem exactBeta_conditions (d : ℕ) (k : Fin (d + 1)) :
    (∀ j : Fin (d + 1),
      ∑ i, exactBetaReadout d k i * (i.val : ℝ) ^ j.val * phi ^ i.val =
        if j = k then 1 else 0) ∧
    (∀ j : Fin (d + 1),
      ∑ i, exactBetaReadout d k i * (i.val : ℝ) ^ j.val * psi ^ i.val =
        if j = k then 1 else 0) ∧
    (∑ i, exactBetaReadout d k i) = 0 := by
  have h : jetMap d _ 0 phi psi 1 (exactBetaReadout d k) = betaCondition d k :=
    Function.surjInv_eq (golden_interpolation d) (betaCondition d k)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have he := congrFun h (.inl j)
    change (∑ i, ((i.val : ℝ) + 0)^j.val * phi^i.val * exactBetaReadout d k i) =
      (if j = k then 1 else 0) at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro j
    have he := congrFun h (.inr (.inl j))
    change (∑ i, ((i.val : ℝ) + 0)^j.val * psi^i.val * exactBetaReadout d k i) =
      (if j = k then 1 else 0) at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have he := congrFun h (.inr (.inr ()))
    change (∑ i, (1:ℝ)^i.val * exactBetaReadout d k i) = 0 at he
    simpa only [one_pow, one_mul] using he

private theorem row_expansion (d : ℕ) (W : World d) (k : Fin (d + 1)) :
    (exactBetaReadout d).mulVec (readings W (List.replicate (2 * (d + 1)) false)) k =
      alpha W.source * (∑ j : Fin (d + 1), W.coeff j *
        ∑ i, exactBetaReadout d k i * (i.val : ℝ)^j.val * phi^i.val) +
      eta W.source * (∑ j : Fin (d + 1), W.coeff j *
        ∑ i, exactBetaReadout d k i * (i.val : ℝ)^j.val * psi^i.val) +
      W.drift * ∑ i, exactBetaReadout d k i := by
  have hr (i : Fin ((List.replicate (2 * (d + 1)) false).length+1)) :
      readAt W (List.replicate (2 * (d + 1)) false) i.val =
        (∑ j : Fin (d + 1), W.coeff j * (i.val : ℝ)^j.val) *
          (alpha W.source * phi^i.val + eta W.source * psi^i.val) + W.drift := by
    rw [pureM_readAt W _ _ (by have := i.isLt; simp at this; omega)]
    simp [gain, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  simp only [Matrix.mulVec, dotProduct, readings, hr]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · congr 1
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Exact beta, for every original world: roots, lower actual degree, both signs and all drifts. -/
theorem pureM_exact_beta (d : ℕ) (W : World d) :
    (exactBetaReadout d).mulVec (readings W (List.replicate (2 * (d + 1)) false)) =
      W.coeff := by
  ext k
  rw [row_expansion]
  have h := exactBeta_conditions d k
  simp only [h.1, h.2.1, h.2.2, mul_zero, add_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← add_mul, (legal_spectral_weights W.source W.legal).2, one_mul]

#print axioms pureM_exact_beta
#print axioms jet_ofFn
#print axioms jets_vanish_iff
#print axioms jets_root_dvd
#print axioms jetMap_bijective
end D5.S3.Observer.Linear.GainRay
