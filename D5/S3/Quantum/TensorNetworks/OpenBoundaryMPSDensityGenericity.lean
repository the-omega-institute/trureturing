/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: An explicit intrinsic real polynomial for raw prefix MPS recovery. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
import D5.S3.Quantum.Algebra.CommonPhasePolynomial
import D5.S3.Quantum.Algebra.Polynomials.ComplexPolynomialCoefficients
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.MvPolynomial

/-! The fixed selector is the all-zero column of the actual Hermitian density.
The coefficient field of the recovery condition is literally real. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity

open Matrix MvPolynomial
open scoped BigOperators Matrix
open OpenBoundaryMPSMarginalBirationality OpenBoundaryMPSDensityRecovery
open PeriodicMPSParentIntersection (Bond Word)
open D5.S3.Quantum.Algebra
open OpenBoundaryMPSTwoSiteMinimality (originalCore original_chart)

def realCoeff {σ : Type*} (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  Polynomials.ComplexPolynomialCoefficients.realCoeff p

def imagCoeff {σ : Type*} (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  Polynomials.ComplexPolynomialCoefficients.imagCoeff p

-- The frozen statement inventory includes this private declaration.
private lemma coefficient_split {σ : Type*} (p : MvPolynomial σ ℂ) :
    map Complex.ofRealHom (realCoeff p) +
      C Complex.I * map Complex.ofRealHom (imagCoeff p) = p :=
  Polynomials.ComplexPolynomialCoefficients.coefficient_split p

lemma coefficient_eval {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) :
    eval x (realCoeff p) = (eval (fun i => (x i : ℂ)) p).re ∧
    eval x (imagCoeff p) = (eval (fun i => (x i : ℂ)) p).im :=
  Polynomials.ComplexPolynomialCoefficients.coefficient_eval p x

def normPolynomial {ι : Type*} (p : PhasePolynomial.Poly ι) :
    MvPolynomial (ι ⊕ ι) ℝ :=
  realCoeff (PhasePolynomial.toCartesian p) ^ 2 +
    imagCoeff (PhasePolynomial.toCartesian p) ^ 2

/-- Real and imaginary coordinates, with a real coefficient field. -/
def realCoordinates {ι : Type*} (z : ι → ℂ) : ι ⊕ ι → ℝ :=
  Sum.elim (fun i => (z i).re) (fun i => (z i).im)

lemma normPolynomial_eval {ι : Type*} (p : PhasePolynomial.Poly ι)
    (z : ι → ℂ) :
    eval (realCoordinates z) (normPolynomial p) = Complex.normSq (PhasePolynomial.actual p z) := by
  obtain ⟨hr, hi⟩ := coefficient_eval (PhasePolynomial.toCartesian p) (realCoordinates z)
  have hc : (fun i => ((realCoordinates z i) : ℂ)) = PhasePolynomial.cartesian z := by
    funext i
    cases i <;> rfl
  rw [hc, PhasePolynomial.actual_cartesian] at hr hi
  simp only [normPolynomial, map_add, pow_two, map_mul, hr, hi, Complex.normSq_apply]

/-- The four complex matrix-entry coordinates of a transfer operator. -/
def transferMatrix (A : Fin 2 → Bond) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ij kl => ∑ s : Fin 2, A s ij.1 kl.1 * star (A s ij.2 kl.2)

lemma transferMatrix_apply (A : Fin 2 → Bond) (X : Bond) :
    (transferMatrix A) *ᵥ (fun ij => X ij.1 ij.2) =
      fun ij => transfer A X ij.1 ij.2 := by
  funext ij
  simp [transferMatrix, transfer, mulVec, dotProduct, mul_apply, conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private lemma transfer_det_iff (A : Fin 2 → Bond) :
    (transferMatrix A).det ≠ 0 ↔ Function.Injective (transfer A) := by
  have hm : (transferMatrix A).det ≠ 0 ↔ Function.Injective (transferMatrix A).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [hm]
  constructor
  · intro h X Y hXY
    have he := h (show (transferMatrix A) *ᵥ (fun ij => X ij.1 ij.2) =
        (transferMatrix A) *ᵥ (fun ij => Y ij.1 ij.2) by
      rw [transferMatrix_apply, transferMatrix_apply, hXY])
    ext i j
    exact congrFun he (i, j)
  · intro h x y hxy
    have he : transfer A (fun i j => x (i, j)) = transfer A (fun i j => y (i, j)) := by
      have hx := transferMatrix_apply A (fun i j => x (i, j))
      have hy := transferMatrix_apply A (fun i j => y (i, j))
      ext i j
      exact congrFun (hx.symm.trans (hxy.trans hy)) (i, j)
    have he' := h he
    funext ij
    exact congrFun (congrFun he' ij.1) ij.2

/-- Polynomial numerator of the transfer matrix in independent t and conjugate-t variables. -/
def numeratorTransfer : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2)
    (PhasePolynomial.Poly (Word 3)) :=
  fun ij kl => ∑ s : Fin 2,
    rename Sum.inl (matrixNumerator s ij.1 kl.1) *
      rename Sum.inr (map (starRingEnd ℂ) (matrixNumerator s ij.2 kl.2))

lemma numeratorTransfer_eval (t : Word 3 → ℂ) :
    (eval (Sum.elim t (fun i => star (t i)))).mapMatrix numeratorTransfer =
      transferMatrix (fun s => (eval t).mapMatrix (matrixNumerator s)) := by
  ext ij kl
  change eval (Sum.elim t (fun i => star (t i))) (numeratorTransfer ij kl) = _
  simp only [numeratorTransfer, map_sum, map_mul, eval_rename]
  change (∑ s : Fin 2, eval t (matrixNumerator s ij.1 kl.1) *
      eval ((starRingEnd ℂ) ∘ t) (map (starRingEnd ℂ) (matrixNumerator s ij.2 kl.2))) = _
  simp only [← MvPolynomial.map_eval]
  rfl

lemma transferMatrix_smul (A : Fin 2 → Bond) (c : ℂ) :
    transferMatrix (fun s => c • A s) = (c * star c) • transferMatrix A := by
  ext ij kl
  simp [transferMatrix, Fin.sum_univ_two, star_mul]
  ring

lemma canonical_transfer_det (t : Word 3 → ℂ)
    (hg : eval t chartPoly ≠ 0) :
    PhasePolynomial.actual numeratorTransfer.det t ≠ 0 ↔
      Function.Injective (transfer (canonicalCore t)) := by
  let c := eval t minorPoly / eval t basisNumerator.det
  have hc : c ≠ 0 := by
    simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
    exact div_ne_zero hg.1.1.1.1 hg.1.1.1.2
  let N : Fin 2 → Bond := fun j => (eval t).mapMatrix (matrixNumerator j)
  have hA : canonicalCore t = fun j => c • N j := funext (chart_scalars t hg).2.1
  have he : transferMatrix (canonicalCore t) =
      (c * star c) • transferMatrix N := by rw [hA, transferMatrix_smul]
  have heval : PhasePolynomial.actual numeratorTransfer.det t = (transferMatrix N).det := by
    rw [PhasePolynomial.actual, (eval (Sum.elim t (fun i => star (t i)))).map_det,
      numeratorTransfer_eval]
  rw [heval, ← transfer_det_iff, he, Matrix.det_smul]
  have hscl : (c * star c) ^ Fintype.card (Fin 2 × Fin 2) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hc (star_ne_zero.mpr hc))
  rw [mul_ne_zero_iff]
  exact ⟨fun h => ⟨hscl, h⟩, fun h => h.2⟩

/-- One real polynomial encodes the chart factors and transfer numerator determinant. -/
def recoveryPolynomial : MvPolynomial ((Word 3) ⊕ (Word 3)) ℝ :=
  normPolynomial (rename Sum.inl chartPoly * numeratorTransfer.det)

/-- Its exact value retains both factors before taking their complex norm square. -/
private theorem recoveryPolynomial_eval (t : Word 3 → ℂ) :
    eval (realCoordinates t) recoveryPolynomial =
      Complex.normSq (eval t chartPoly * PhasePolynomial.actual numeratorTransfer.det t) := by
  rw [recoveryPolynomial, normPolynomial_eval]
  congr 1
  simp [PhasePolynomial.actual, eval_rename]

/-- Nonvanishing is exactly the fixed coherent chart and injective canonical transfer. -/
theorem recoveryPolynomial_ne_zero (t : Word 3 → ℂ) :
    eval (realCoordinates t) recoveryPolynomial ≠ 0 ↔
      eval t chartPoly ≠ 0 ∧ Function.Injective (transfer (canonicalCore t)) := by
  rw [recoveryPolynomial_eval, ne_eq, Complex.normSq_eq_zero, ← ne_eq, mul_ne_zero_iff]
  constructor
  · rintro ⟨hg, hd⟩
    exact ⟨hg, (canonical_transfer_det t hg).mp hd⟩
  · rintro ⟨hg, hE⟩
    exact ⟨hg, (canonical_transfer_det t hg).mpr hE⟩

/-- The fixed all-zero column; this is not a coherent sum over complement words. -/
def fixedTensor (Q : Matrix (Word 3) (Word 3) ℂ) : Word 3 → ℂ :=
  fun u => Q u (fun _ => 0)

private lemma fixedTensor_mulVec (Q : Matrix (Word 3) (Word 3) ℂ) :
    Q *ᵥ Pi.single (fun _ : Fin 3 => (0 : Fin 2)) 1 = fixedTensor Q := by
  ext u
  simp [fixedTensor]

/-- The real polynomial in all observed density-matrix coordinates, supported on one column. -/
def observedPolynomial :
    MvPolynomial (((Word 3 × Word 3) ⊕ (Word 3 × Word 3))) ℝ :=
  rename (Sum.map (fun u => (u, fun _ => 0)) (fun u => (u, fun _ => 0))) recoveryPolynomial

lemma observedPolynomial_eval (Q : Matrix (Word 3) (Word 3) ℂ) :
    eval (realCoordinates (fun ij => Q ij.1 ij.2)) observedPolynomial =
      eval (realCoordinates (fixedTensor Q)) recoveryPolynomial := by
  rw [observedPolynomial, eval_rename]
  apply congrArg (fun x : Word 3 ⊕ Word 3 → ℝ => eval x recoveryPolynomial)
  funext i
  cases i <;> rfl

private def prefixCoordinates (m : ℕ) :
    Word 3 ⊕ Word 3 → MvPolynomial ((Word (3 + m)) ⊕ (Word (3 + m))) ℝ :=
  Sum.elim
    (fun u => ∑ b : Word m, (
      X (Sum.inl (Fin.append u b)) * X (Sum.inl (Fin.append (fun _ => 0) b)) +
      X (Sum.inr (Fin.append u b)) * X (Sum.inr (Fin.append (fun _ => 0) b))))
    (fun u => ∑ b : Word m, (
      X (Sum.inr (Fin.append u b)) * X (Sum.inl (Fin.append (fun _ => 0) b)) -
      X (Sum.inl (Fin.append u b)) * X (Sum.inr (Fin.append (fun _ => 0) b))))

/-- Explicit quadratic pullback to the real and imaginary parts of the full actual state. -/
def statePolynomial (m : ℕ) :
    MvPolynomial ((Word (3 + m)) ⊕ (Word (3 + m))) ℝ :=
  eval₂Hom C (prefixCoordinates m) recoveryPolynomial

private lemma prefixCoordinates_eval (m : ℕ) (ψ : Word (3 + m) → ℂ) :
    (eval (realCoordinates ψ) ∘ prefixCoordinates m) =
      realCoordinates (fixedTensor (rawPrefix 3 m ψ)) := by
  funext u
  cases u <;>
    simp [prefixCoordinates, realCoordinates, fixedTensor, rawPrefix, amplitudeColumns,
      mul_apply, conjTranspose_apply, Complex.mul_re, Complex.mul_im, sub_eq_add_neg, add_comm]

/-- The actual raw-prefix pullback identity, with no parametrization hypothesis. -/
theorem statePolynomial_eval (m : ℕ) (ψ : Word (3 + m) → ℂ) :
    eval (realCoordinates ψ) (statePolynomial m) =
      eval (realCoordinates (fixedTensor (rawPrefix 3 m ψ))) recoveryPolynomial := by
  change eval (realCoordinates ψ) (eval₂ C (prefixCoordinates m) recoveryPolynomial) = _
  rw [← eval_assoc, prefixCoordinates_eval]

private def parameterCoordinates (n : ℕ) :
    Word n ⊕ Word n → MvPolynomial (parameterIndex ⊕ parameterIndex) ℝ :=
  Sum.elim
    (fun w => realCoeff (PhasePolynomial.toCartesian (rename Sum.inl (parameterPolys n w))))
    (fun w => imagCoeff (PhasePolynomial.toCartesian (rename Sum.inl (parameterPolys n w))))

/-- Real polynomial pullback through the supplier's original twelve-complex-parameter map. -/
def parameterPolynomial (m : ℕ) : MvPolynomial (parameterIndex ⊕ parameterIndex) ℝ :=
  eval₂Hom C (parameterCoordinates (3 + m)) (statePolynomial m)

private lemma parameterCoordinates_eval (n : ℕ) (x : parameterIndex → ℂ) :
    eval (realCoordinates x) ∘ parameterCoordinates n =
      realCoordinates (fun w => eval x (parameterPolys n w)) := by
  funext u
  have hc : (fun i => ((realCoordinates x i) : ℂ)) = PhasePolynomial.cartesian x := by
    funext i
    cases i <;> rfl
  cases u with
  | inl w =>
    have h := (coefficient_eval
      (PhasePolynomial.toCartesian (rename Sum.inl (parameterPolys n w))) (realCoordinates x)).1
    rw [hc, PhasePolynomial.actual_cartesian] at h
    simpa [parameterCoordinates, realCoordinates, PhasePolynomial.actual, eval_rename] using h
  | inr w =>
    have h := (coefficient_eval
      (PhasePolynomial.toCartesian (rename Sum.inl (parameterPolys n w))) (realCoordinates x)).2
    rw [hc, PhasePolynomial.actual_cartesian] at h
    simpa [parameterCoordinates, realCoordinates, PhasePolynomial.actual, eval_rename] using h

private lemma parameterPolynomial_eval (m : ℕ) (x : parameterIndex → ℂ) :
    eval (realCoordinates x) (parameterPolynomial m) =
      eval (realCoordinates (fun w => eval x (parameterPolys (3 + m) w))) (statePolynomial m) := by
  change eval (realCoordinates x)
    (eval₂ C (parameterCoordinates (3 + m)) (statePolynomial m)) = _
  rw [← eval_assoc, parameterCoordinates_eval]

private lemma original_transfer_injective : Function.Injective (transfer originalCore) := by
  intro X Y h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  norm_num [transfer, originalCore, mul_apply, vecMul, dotProduct,
    conjTranspose_apply, Fin.sum_univ_two, map_ofNat]
    at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · change X 0 0 = Y 0 0
    linear_combination 4 * h00 - (5 / 2 : ℂ) * h01 - (5 / 2 : ℂ) * h10 + (3 / 2 : ℂ) * h11
  · change X 0 1 = Y 0 1
    linear_combination -(13 / 4 : ℂ) * h00 + (7 / 4 : ℂ) * h01 + 2 * h10 - h11
  · change X 1 0 = Y 1 0
    linear_combination -(13 / 4 : ℂ) * h00 + 2 * h01 + (7 / 4 : ℂ) * h10 - h11
  · change X 1 1 = Y 1 1
    linear_combination (21 / 8 : ℂ) * h00 - (11 / 8 : ℂ) * h01 -
      (11 / 8 : ℂ) * h10 + (5 / 8 : ℂ) * h11

private lemma gauge_transfer_injective (A : Fin 2 → Bond) (s : ℂ) (hs : s ≠ 0)
    (u : Bond) (hu : IsUnit u.det) (hA : Function.Injective (transfer A)) :
    Function.Injective (transfer (fun i => s • (u * A i * u⁻¹))) := by
  have hout := sandwich_injective u
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hu))
  have hin := sandwich_injective u⁻¹
    (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr
        (by simpa only [det_nonsing_inv, Ring.inverse_eq_inv] using hu.inv)))
  have he (X : Bond) : transfer (fun i => s • (u * A i * u⁻¹)) X =
      (s * star s) • (u * transfer A (u⁻¹ * X * (u⁻¹)ᴴ) * uᴴ) := by
    simp only [transfer, conjTranspose_smul, conjTranspose_mul, smul_mul_assoc,
      mul_smul_comm, smul_smul, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum,
      Matrix.mul_assoc, mul_comm (star s) s]
  intro X Y h
  rw [he, he] at h
  exact hin (hA (hout ((smul_right_injective Bond (mul_ne_zero hs (star_ne_zero.mpr hs))) h)))

private lemma original_canonical_transfer (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Function.Injective (transfer (canonicalCore
      (mpsState 3 (originalCore 0) (originalCore 1) ![1, 0] ![(x : ℂ), (y : ℂ)]))) := by
  obtain ⟨s, hs, u, hu, _, hA, _⟩ := triple_gauge (originalCore 0) (originalCore 1)
    ![1, 0] ![(x : ℂ), (y : ℂ)] (original_chart x y hx hy)
  have he : canonicalCore (mpsState 3 (originalCore 0) (originalCore 1)
      ![1, 0] ![(x : ℂ), (y : ℂ)]) = fun i => s • (u * originalCore i * u⁻¹) := by
    have hη : (![originalCore 0, originalCore 1] : Fin 2 → Bond) = originalCore :=
      FinVec.etaExpand_eq _
    funext i
    simpa only [canonicalCore, hη] using hA i
  rw [he]
  exact gauge_transfer_injective originalCore s hs u hu original_transfer_injective

private lemma original_tail_positive (m : ℕ) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (transfer originalCore)^[m] (vecMulVec ![1, 2] (star ![1, 2])) =
        !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] := by
  induction m with
  | zero =>
    refine ⟨1, 2, 4, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [vecMulVec, Pi.star_apply, map_ofNat]
  | succ m ih =>
    obtain ⟨a, b, c, ha, hb, hc, hH⟩ := ih
    refine ⟨26 * a + 64 * b + 40 * c, 38 * a + 92 * b + 56 * c,
      58 * a + 136 * b + 80 * c, by positivity, by positivity, by positivity, ?_⟩
    rw [Function.iterate_succ_apply', hH]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transfer, originalCore, mul_apply, vecMul, dotProduct,
        conjTranspose_apply, Fin.sum_univ_two, map_ofNat] <;> ring

private lemma fixed_witness_tensor (m : ℕ) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      fixedTensor (rawPrefix 3 m
        (mpsState (3 + m) (originalCore 0) (originalCore 1) ![1, 0] ![1, 2])) =
        mpsState 3 (originalCore 0) (originalCore 1) ![1, 0] ![(x : ℂ), (y : ℂ)] := by
  obtain ⟨a, b, c, ha, hb, hc, hH⟩ := original_tail_positive m
  refine ⟨37 * a + 54 * b, 37 * b + 54 * c, by positivity, by positivity, ?_⟩
  have hcol : (prefixMap originalCore ![1, 0] 3)ᴴ *ᵥ
      Pi.single (fun _ : Fin 3 => (0 : Fin 2)) 1 = ![37, 54] := by
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i <;>
      norm_num [mulVec, dotProduct, conjTranspose_apply, prefixMap,
        PeriodicMPSParentIntersection.wordMatrix, List.ofFn_succ, originalCore,
        mul_apply, vecMul, Fin.sum_univ_two, map_ofNat]
  have he : fixedTensor (rawPrefix 3 m
      (mpsState (3 + m) (originalCore 0) (originalCore 1) ![1, 0] ![1, 2])) =
      rawPrefix 3 m (mpsState (3 + m) (originalCore 0) (originalCore 1) ![1, 0] ![1, 2]) *ᵥ
        Pi.single (fun _ : Fin 3 => (0 : Fin 2)) 1 := by
    exact (fixedTensor_mulVec _).symm
  rw [he, density_factor, ← mulVec_mulVec, ← mulVec_mulVec, hcol, hH]
  have hγ : (!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] : Bond) *ᵥ ![37, 54] =
      ![((37 * a + 54 * b : ℝ) : ℂ), ((37 * b + 54 * c : ℝ) : ℂ)] := by
    ext i
    fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hγ]
  have hη : (![originalCore 0, originalCore 1] : Fin 2 → Bond) = originalCore :=
    FinVec.etaExpand_eq _
  funext w
  simp only [mpsState, hη]
  change dotProduct (![1, 0] ᵥ* PeriodicMPSParentIntersection.wordMatrix originalCore w)
    ![((37 * a + 54 * b : ℝ) : ℂ), ((37 * b + 54 * c : ℝ) : ℂ)] = _
  rw [dotProduct_mulVec]
  rfl

/-- The fixed raw-density column satisfies the intrinsic polynomial at every length. -/
theorem statePolynomial_witness (m : ℕ) :
    eval (realCoordinates
      (mpsState (3 + m) (originalCore 0) (originalCore 1) ![1, 0] ![1, 2]))
        (statePolynomial m) ≠ 0 := by
  rw [statePolynomial_eval, recoveryPolynomial_ne_zero]
  obtain ⟨x, y, hx, hy, ht⟩ := fixed_witness_tensor m
  rw [ht]
  exact ⟨original_chart x y hx hy, original_canonical_transfer x y hx hy⟩

lemma polynomial_nonzero_dense {ρ : Type*} [Finite ρ]
    (P : MvPolynomial ρ ℝ) (a : ρ → ℝ) (ha : eval a P ≠ 0) :
    Dense {x : ρ → ℝ | eval x P ≠ 0} := by
  letI := Fintype.ofFinite ρ
  have hz : interior {x : ρ → ℝ | eval x P = 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have he : (fun x : ρ → ℝ => eval x P) =ᶠ[nhds z] 0 := by
      exact mem_interior_iff_mem_nhds.mp hz
    have hall := (AnalyticOnNhd.eval_mvPolynomial P).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) he
    exact ha (hall (Set.mem_univ a))
  exact interior_eq_empty_iff_dense_compl.mp hz

lemma continuous_realCoordinates {ι : Type*} :
    Continuous (realCoordinates : (ι → ℂ) → (ι ⊕ ι → ℝ)) := by
  apply continuous_pi
  intro i
  cases i <;> dsimp [realCoordinates] <;> fun_prop

private def complexParameters (x : parameterIndex ⊕ parameterIndex → ℝ) : parameterIndex → ℂ :=
  fun i => (x (.inl i) : ℂ) + Complex.I * (x (.inr i) : ℂ)

private lemma real_complex_parameters (x : parameterIndex ⊕ parameterIndex → ℝ) :
    realCoordinates (complexParameters x) = x := by
  funext i
  cases i <;> simp [realCoordinates, complexParameters]

private lemma complex_real_parameters (x : parameterIndex → ℂ) :
    complexParameters (realCoordinates x) = x := by
  funext i
  simpa only [complexParameters, realCoordinates, Sum.elim_inl, Sum.elim_inr, mul_comm]
    using Complex.re_add_im (x i)

private lemma parameterPolynomial_nonzero (m : ℕ) :
    ∃ a : parameterIndex ⊕ parameterIndex → ℝ, eval a (parameterPolynomial m) ≠ 0 := by
  let x : parameterIndex → ℂ := Sum.elim
    (fun ijk => originalCore ijk.1 ijk.2.1 ijk.2.2) (Sum.elim ![1, 0] ![1, 2])
  refine ⟨realCoordinates x, ?_⟩
  rw [parameterPolynomial_eval, parameter_eval]
  exact statePolynomial_witness m

/-- A principal real-algebraic open set in the literal parametrized state image. -/
def goodStates (m : ℕ) : Set (openBoundaryMPS (3 + m)) :=
  {ψ | eval (realCoordinates (fun ij => rawPrefix 3 m
      (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) observedPolynomial ≠ 0}

/-- Every length has a nonempty dense relative principal real-algebraic recovery locus.
The competitor ranges over the entire actual state image, with no chart premise. -/
theorem intrinsic_recovery_genericity (m : ℕ) :
    (goodStates m).Nonempty ∧ IsOpen (goodStates m) ∧ Dense (goodStates m) ∧
      ∀ ψ ∈ goodStates m, ∀ φ : Word (3 + m) → ℂ,
        φ ∈ openBoundaryMPS (3 + m) →
        (rawPrefix 3 m φ = rawPrefix 3 m (ψ : Word (3 + m) → ℂ) ↔
          ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • (ψ : Word (3 + m) → ℂ)) := by
  have hset : goodStates m =
      {ψ : openBoundaryMPS (3 + m) |
        eval (realCoordinates (ψ : Word (3 + m) → ℂ)) (statePolynomial m) ≠ 0} := by
    ext ψ
    simp only [goodStates, Set.mem_ofPred_eq, observedPolynomial_eval, ← statePolynomial_eval]
  have hnonempty : (goodStates m).Nonempty := by
    rw [hset]
    exact ⟨⟨_, ⟨_, _, _, _, rfl⟩⟩, statePolynomial_witness m⟩
  have hopen : IsOpen (goodStates m) := by
    rw [hset]
    exact isOpen_ne.preimage ((MvPolynomial.continuous_eval (statePolynomial m)).comp
      (continuous_realCoordinates.comp continuous_subtype_val))
  have hdense : Dense (goodStates m) := by
    let f : (parameterIndex ⊕ parameterIndex → ℝ) → (Word (3 + m) → ℂ) :=
      fun a w => eval (complexParameters a) (parameterPolys (3 + m) w)
    have hf : Continuous f := by
      apply continuous_pi
      intro w
      apply (MvPolynomial.continuous_eval (parameterPolys (3 + m) w)).comp
      apply continuous_pi
      intro i
      dsimp [complexParameters]
      fun_prop
    have hrange : Set.range f = openBoundaryMPS (3 + m) := by
      rw [parameter_image]
      ext ψ
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨complexParameters a, rfl⟩
      · rintro ⟨x, rfl⟩
        refine ⟨realCoordinates x, ?_⟩
        dsimp [f]
        rw [complex_real_parameters]
    obtain ⟨a, ha⟩ := parameterPolynomial_nonzero m
    have hd := polynomial_nonzero_dense (parameterPolynomial m) a ha
    rw [hset]
    apply Subtype.dense_iff.mpr
    intro ψ hψ
    apply Set.mem_of_subset_of_mem (closure_mono ?_)
      (hf.range_subset_closure_image_dense hd (hrange.symm ▸ hψ))
    rintro y ⟨b, hb, rfl⟩
    have hgood : eval (realCoordinates (f b)) (statePolynomial m) ≠ 0 := by
      have he := parameterPolynomial_eval m (complexParameters b)
      rw [real_complex_parameters] at he
      exact he ▸ hb
    exact ⟨⟨f b, hrange ▸ Set.mem_range_self b⟩, hgood, rfl⟩
  refine ⟨hnonempty, hopen, hdense, ?_⟩
  intro ψ hψ φ hφ
  apply observable_chart_phase_recovery m ψ φ ψ.property hφ
  refine ⟨Pi.single (fun _ : Fin 3 => (0 : Fin 2)) 1, ?_⟩
  change eval (realCoordinates (fun ij => rawPrefix 3 m
    (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) observedPolynomial ≠ 0 at hψ
  have hgood := (recoveryPolynomial_ne_zero _).mp
    (observedPolynomial_eval (rawPrefix 3 m ψ) ▸ hψ)
  simpa only [fixedTensor_mulVec] using hgood

#print axioms intrinsic_recovery_genericity

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
