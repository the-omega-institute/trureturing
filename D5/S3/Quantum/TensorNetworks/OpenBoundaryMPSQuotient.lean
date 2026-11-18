/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Rational observable boundary Gram for actual open-boundary MPS. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity

/-! Raw affine prefix observations retain the full boundary Gram. The inverse
transfer is algebraic and is not asserted to be positive or physical.
The coherent reconstruction is the original Ma--Zhang C8 supplier. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient

open Matrix MvPolynomial
open scoped BigOperators Matrix
open OpenBoundaryMPSMarginalBirationality OpenBoundaryMPSDensityRecovery
open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open D5.S3.Quantum.Algebra

/-- The five entries in the original normalized canonical-core order. -/
def coreCoordinates (t : Word 3 → ℂ) : Fin 5 → ℂ :=
  ![reconstructedLeft t 0, canonicalCore t 0 0 0, canonicalCore t 0 0 1,
    canonicalCore t 1 0 0, canonicalCore t 1 0 1]

lemma canonical_shape (t : Word 3 → ℂ) (ht : t ∈ openBoundaryMPS 3)
    (hg : eval t chartPoly ≠ 0) :
    let θ : OpenBoundaryMPSTwoSiteMinimality.Parameter := (coreCoordinates t, 0, 0)
    OpenBoundaryMPSTwoSiteMinimality.left θ = reconstructedLeft t ∧ OpenBoundaryMPSTwoSiteMinimality.core θ = canonicalCore t := by
  dsimp only
  have hd : eval t minorPoly ≠ 0 := by
    simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
    exact hg.1.1.1.1
  have hl1 : reconstructedLeft t 1 = 1 := by
    simp [reconstructedLeft, leftNumerator, hd]
  have hn := (chart_reconstruction t (quartic_image t ht) hg).2.1
  constructor
  · ext i
    fin_cases i <;> simp [OpenBoundaryMPSTwoSiteMinimality.left, coreCoordinates, hl1]
  · have h (i j : Fin 2) := congrFun (hn i) j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hl1, one_mul] at h
    have h00 := h 0 0
    have h01 := h 0 1
    have h10 := h 1 0
    have h11 := h 1 1
    norm_num at h00 h01 h10 h11
    ext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [OpenBoundaryMPSTwoSiteMinimality.core, coreCoordinates, canonicalCore]
    · linear_combination -h00
    · linear_combination -h01
    · linear_combination -h10
    · linear_combination -h11

/-- The normalized-row boundary contraction, with no matrix inverse selector. -/
def boundaryLeft (l : Fin 2 → ℂ) : Matrix (Fin 2) (Word 3) ℂ :=
  fun k w => if w 2 = k then l (w 0) * l (w 1) else 0

private lemma sum_words_three (f : Word 3 → ℂ) :
    (∑ w : Word 3, f w) = ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, f ![i, j, k] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => Fin 2)).sum_comp]
  simp only [Fintype.sum_prod_type]
  congr 1; ext i
  rw [← (Fin.consEquiv (fun _ : Fin 2 => Fin 2)).sum_comp]
  simp only [Fintype.sum_prod_type]
  congr 1; ext j
  rw [← (Fin.consEquiv (fun _ : Fin 1 => Fin 2)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  congr 1

private lemma boundaryLeft_prefix (t : Word 3 → ℂ) (ht : t ∈ openBoundaryMPS 3)
    (hg : eval t chartPoly ≠ 0) :
    boundaryLeft (reconstructedLeft t) *
      prefixMap (canonicalCore t) (reconstructedLeft t) 3 = 1 := by
  let θ : OpenBoundaryMPSTwoSiteMinimality.Parameter := (coreCoordinates t, 0, 0)
  obtain ⟨hl, hA⟩ := canonical_shape t ht hg
  change OpenBoundaryMPSTwoSiteMinimality.left θ = _ at hl
  change OpenBoundaryMPSTwoSiteMinimality.core θ = _ at hA
  have hv (q : Fin 2 → ℂ) :
      (boundaryLeft (reconstructedLeft t) *
        prefixMap (canonicalCore t) (reconstructedLeft t) 3) *ᵥ q = q := by
    rw [← mulVec_mulVec]
    funext k
    simp only [mulVec, dotProduct]
    rw [sum_words_three]
    change (∑ i : Fin 2, ∑ j : Fin 2, ∑ a : Fin 2,
      (if a = k then reconstructedLeft t i * reconstructedLeft t j else 0) *
        (∑ b : Fin 2, prefixMap (canonicalCore t) (reconstructedLeft t) 3 ![i,j,a] b * q b)) = q k
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hs (w : Word 3) :
        (∑ j : Fin 2, prefixMap (canonicalCore t) (reconstructedLeft t) 3 w j * q j) =
          mpsState 3 (OpenBoundaryMPSTwoSiteMinimality.core θ 0) (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) q w := by
      rw [hA, hl, state_formula, dotProduct_mulVec]
      rfl
    simp_rw [hs]
    rw [← hl]
    exact OpenBoundaryMPSTwoSiteMinimality.boundary_contraction θ q k
  ext i j
  have hh := congrFun (hv (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Matrix.one_apply] using hh

private lemma transfer_power (A : Fin 2 → Bond) (m : ℕ) (X : Bond) :
    OpenBoundaryMPSDensityGenericity.transferMatrix A ^ m *ᵥ (fun ij => X ij.1 ij.2) =
      fun ij => (transfer A)^[m] X ij.1 ij.2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, OpenBoundaryMPSDensityGenericity.transferMatrix_apply,
      Function.iterate_succ_apply']

/-- The original Cramer left numerators evaluated on the observed tensor. -/
def leftNumeratorMap (t : Word 3 → ℂ) : Matrix (Fin 2) (Word 3) ℂ :=
  boundaryLeft (eval t ∘ leftNumerator)

private lemma boundaryLeft_scalars (t : Word 3 → ℂ) (hg : eval t chartPoly ≠ 0) :
    boundaryLeft (reconstructedLeft t) = (eval t minorPoly)⁻¹ ^ 2 • leftNumeratorMap t := by
  rw [(chart_scalars t hg).2.2.1]
  ext k w
  by_cases hw : w 2 = k <;>
    simp [boundaryLeft, leftNumeratorMap, hw, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- The evaluated polynomial transfer numerator, in the existing complex four-entry basis. -/
def transferNumerator (t : Word 3 → ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  OpenBoundaryMPSDensityGenericity.transferMatrix (fun i => (eval t).mapMatrix (matrixNumerator i))

/-- Complex squared modulus, used only as an algebraic scalar. -/
def modulus (z : ℂ) : ℂ := z * star z

/-- The cleared boundary-Gram numerator prior to division by its exact scalar denominator. -/
def gramNumerator (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) : Bond :=
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  let B := leftNumeratorMap t * Q * (leftNumeratorMap t)ᴴ
  modulus (eval t basisNumerator.det) ^ m •
    (fun i j => ((transferNumerator t).adjugate ^ m *ᵥ (fun kl => B kl.1 kl.2)) (i, j))

/-- The exact denominator keeps the complement length m and the contraction's extra square. -/
def gramDenominator (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) : ℂ :=
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  modulus (eval t minorPoly) ^ (m + 2) * (transferNumerator t).det ^ m

/-- A rational formula on arbitrary observed matrices; physical claims require an actual state. -/
def boundaryGram (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) : Bond :=
  (gramDenominator m Q)⁻¹ • gramNumerator m Q

private lemma modulus_ne_zero {z : ℂ} (hz : z ≠ 0) : modulus z ≠ 0 :=
  mul_ne_zero hz (star_ne_zero.mpr hz)

private lemma transfer_scalars (t : Word 3 → ℂ) (hg : eval t chartPoly ≠ 0) :
    OpenBoundaryMPSDensityGenericity.transferMatrix (canonicalCore t) =
      (modulus (eval t minorPoly) / modulus (eval t basisNumerator.det)) •
        transferNumerator t := by
  have hA : canonicalCore t = fun j => (eval t minorPoly / eval t basisNumerator.det) •
      (eval t).mapMatrix (matrixNumerator j) :=
    funext (chart_scalars t hg).2.1
  rw [hA, OpenBoundaryMPSDensityGenericity.transferMatrix_smul]
  congr 1
  simp only [modulus, star_div₀, div_mul_div_comm]

private lemma gram_formula (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (ht : OpenBoundaryMPSDensityGenericity.fixedTensor Q ∈ openBoundaryMPS 3)
    (hg : eval (OpenBoundaryMPSDensityGenericity.fixedTensor Q) chartPoly ≠ 0)
    (hM : (transferNumerator (OpenBoundaryMPSDensityGenericity.fixedTensor Q)).det ≠ 0)
    (X : Bond)
    (hQ : Q = prefixMap (canonicalCore (OpenBoundaryMPSDensityGenericity.fixedTensor Q))
        (reconstructedLeft (OpenBoundaryMPSDensityGenericity.fixedTensor Q)) 3 *
      (transfer (canonicalCore (OpenBoundaryMPSDensityGenericity.fixedTensor Q)))^[m] X *
      (prefixMap (canonicalCore (OpenBoundaryMPSDensityGenericity.fixedTensor Q))
        (reconstructedLeft (OpenBoundaryMPSDensityGenericity.fixedTensor Q)) 3)ᴴ) :
    boundaryGram m Q = X := by
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  let d := modulus (eval t minorPoly)
  let v := modulus (eval t basisNumerator.det)
  let T := transferNumerator t
  let B := leftNumeratorMap t * Q * (leftNumeratorMap t)ᴴ
  let L := boundaryLeft (reconstructedLeft t)
  let F := prefixMap (canonicalCore t) (reconstructedLeft t) 3
  have hdv := hg
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hdv
  have hd : d ≠ 0 := modulus_ne_zero hdv.1.1.1.1
  have hv : v ≠ 0 := modulus_ne_zero hdv.1.1.1.2
  have hLF : L * F = 1 := boundaryLeft_prefix t ht hg
  have hH : L * Q * Lᴴ = (transfer (canonicalCore t))^[m] X := by
    change Q = F * _ * Fᴴ at hQ
    rw [hQ]
    calc
      L * (F * (transfer (canonicalCore t))^[m] X * Fᴴ) * Lᴴ =
          (L * F) * (transfer (canonicalCore t))^[m] X * (L * F)ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hLF]; simp
  have hL : L * Q * Lᴴ = d⁻¹ ^ 2 • B := by
    dsimp only [L]
    rw [boundaryLeft_scalars t hg, conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    simp [d, modulus, star_pow, star_inv₀, _root_.mul_inv_rev, mul_pow, mul_comm]
  have hp := transfer_power (canonicalCore t) m X
  rw [transfer_scalars t hg, smul_pow, Matrix.smul_mulVec] at hp
  have he : d⁻¹ ^ 2 • (fun ij => B ij.1 ij.2) =
      (d / v) ^ m • (T ^ m *ᵥ (fun ij => X ij.1 ij.2)) := by
    rw [hp]
    exact congrArg (fun H : Bond => fun ij : Fin 2 × Fin 2 => H ij.1 ij.2)
      (hL.symm.trans hH)
  have ha := congrArg (fun y => T.adjugate ^ m *ᵥ y) he
  simp only [mulVec_smul, mulVec_mulVec, ← Matrix.adjugate_pow,
    Matrix.adjugate_mul, Matrix.det_pow, Matrix.smul_mulVec, one_mulVec,
    smul_smul] at ha
  rw [Matrix.adjugate_pow] at ha
  have hc : v ^ m • (T.adjugate ^ m *ᵥ (fun ij => B ij.1 ij.2)) =
      (d ^ (m + 2) * T.det ^ m) • (fun ij => X ij.1 ij.2) := by
    calc
      _ = (v ^ m * d ^ 2) • (d⁻¹ ^ 2 •
          (T.adjugate ^ m *ᵥ (fun ij => B ij.1 ij.2))) := by
        rw [smul_smul]
        congr 1
        field_simp
      _ = (v ^ m * d ^ 2) • (((d / v) ^ m * T.det ^ m) •
          (fun ij => X ij.1 ij.2)) := congrArg _ ha
      _ = _ := by
        rw [smul_smul]
        congr 1
        rw [div_pow, pow_add]
        field_simp
  have hden : gramDenominator m Q ≠ 0 := mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hM)
  apply (inv_smul_eq_iff₀ hden).mpr
  ext i j
  exact congrFun hc (i, j)

/-- On every actual free-boundary state in the fixed observed recovery chart,
the rational observable formula is its full-length canonical boundary Gram. -/
theorem actual_boundary_gram (m : ℕ) (ψ : Word (3 + m) → ℂ)
    (hψ : ψ ∈ openBoundaryMPS (3 + m))
    (hg : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor (rawPrefix 3 m ψ)))
        OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0) :
    let t := OpenBoundaryMPSDensityGenericity.fixedTensor (rawPrefix 3 m ψ)
    ∃ q : Fin 2 → ℂ,
      ψ = mpsState (3 + m) (canonicalCore t 0) (canonicalCore t 1)
        (reconstructedLeft t) q ∧
      boundaryGram m (rawPrefix 3 m ψ) = vecMulVec q (star q) := by
  dsimp only
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor (rawPrefix 3 m ψ)
  obtain ⟨hchart, hE⟩ := (OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero t).mp hg
  obtain ⟨a₀, a₁, l, r, hstate⟩ := hψ
  let A : Fin 2 → Bond := ![a₀, a₁]
  obtain ⟨g, ht⟩ := observed_coherent m A l r (Pi.single (fun _ => 0) 1)
  have hcoh : mpsState 3 (A 0) (A 1) l g = t := by
    rw [← ht]
    change rawPrefix 3 m (mpsState (3 + m) a₀ a₁ l r) *ᵥ Pi.single _ 1 = t
    rw [← hstate, Matrix.mulVec_single_one]
    rfl
  have him : t ∈ openBoundaryMPS 3 := ⟨A 0, A 1, l, g, hcoh.symm⟩
  obtain ⟨q, hq⟩ := gauge_lift t A l g hcoh hchart (3 + m) r
  have hψq : ψ = mpsState (3 + m) (canonicalCore t 0) (canonicalCore t 1)
      (reconstructedLeft t) q := hstate.trans hq
  refine ⟨q, hψq, ?_⟩
  have hm : (transferNumerator t).det ≠ 0 := by
    dsimp only [transferNumerator]
    rw [← OpenBoundaryMPSDensityGenericity.numeratorTransfer_eval]
    have hm := (OpenBoundaryMPSDensityGenericity.canonical_transfer_det t hchart).mpr hE
    simpa only [D5.S3.Quantum.Algebra.PhasePolynomial.actual, RingHom.map_det] using hm
  apply gram_formula m _ him hchart hm (vecMulVec q (star q))
  change rawPrefix 3 m ψ = prefixMap (canonicalCore t) (reconstructedLeft t) 3 *
    (transfer (canonicalCore t))^[m] (vecMulVec q (star q)) *
    (prefixMap (canonicalCore t) (reconstructedLeft t) 3)ᴴ
  rw [hψq, density_factor]
/-- Observed entries, including entries away from the selected column. -/
abbrev ObservationIndex := Word 3 × Word 3
def polynomialConjugate {ι : Type*} (p : PhasePolynomial.Poly ι) :
    PhasePolynomial.Poly ι := rename Sum.swap (map (starRingEnd ℂ) p)
lemma polynomialConjugate_eval {ι : Type*} (p : PhasePolynomial.Poly ι)
    (z : ι → ℂ) :
    PhasePolynomial.actual (polynomialConjugate p) z = star (PhasePolynomial.actual p z) := by
  rw [polynomialConjugate, PhasePolynomial.actual, eval_rename]
  have hv : (Sum.elim z (fun i => star (z i))) ∘ Sum.swap =
      (starRingEnd ℂ) ∘ (Sum.elim z (fun i => star (z i))) := by
    funext i
    cases i <;> simp
  rw [hv, ← MvPolynomial.map_eval]
  rfl
private def columnPolynomial (p : MvPolynomial (Word 3) ℂ) :
    PhasePolynomial.Poly ObservationIndex := rename (fun w => Sum.inl (w, fun _ => 0)) p
private lemma columnPolynomial_eval (p : MvPolynomial (Word 3) ℂ)
    (Q : Matrix (Word 3) (Word 3) ℂ) :
    PhasePolynomial.actual (columnPolynomial p) (fun ij => Q ij.1 ij.2) =
      eval (OpenBoundaryMPSDensityGenericity.fixedTensor Q) p := by
  rw [columnPolynomial, PhasePolynomial.actual, eval_rename]
  rfl
private def contractionPolynomial : Matrix (Fin 2) (Word 3)
    (PhasePolynomial.Poly ObservationIndex) := fun k w =>
  if w 2 = k then columnPolynomial (leftNumerator (w 0)) *
    columnPolynomial (leftNumerator (w 1)) else 0
private def contractedPolynomial : Matrix (Fin 2) (Fin 2) (PhasePolynomial.Poly ObservationIndex) :=
  contractionPolynomial * (Matrix.of fun u v : Word 3 => (X (Sum.inl (u, v)) : PhasePolynomial.Poly ObservationIndex)) *
    (Matrix.of fun w k => polynomialConjugate (contractionPolynomial k w))
private def observedTransferPolynomial : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2)
    (PhasePolynomial.Poly ObservationIndex) :=
  fun ij kl => rename (Sum.map (fun w => (w, fun _ => 0)) (fun w => (w, fun _ => 0)))
    (OpenBoundaryMPSDensityGenericity.numeratorTransfer ij kl)
private def modulusPolynomial (p : MvPolynomial (Word 3) ℂ) :
    PhasePolynomial.Poly ObservationIndex := columnPolynomial p *
      polynomialConjugate (columnPolynomial p)
/-- A literal polynomial numerator in independent observed entries and conjugates. -/
def boundaryGramPolynomial (m : ℕ) :
    Matrix (Fin 2) (Fin 2) (PhasePolynomial.Poly ObservationIndex) :=
  modulusPolynomial basisNumerator.det ^ m •
    (fun i j => (observedTransferPolynomial.adjugate ^ m *ᵥ
      (fun kl => contractedPolynomial kl.1 kl.2)) (i, j))
/-- A literal polynomial denominator in the same observed coordinates. -/
def boundaryDenominatorPolynomial (m : ℕ) : PhasePolynomial.Poly ObservationIndex :=
  modulusPolynomial minorPoly ^ (m + 2) * observedTransferPolynomial.det ^ m
private lemma polynomial_evaluations (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) :
    (∀ i j, PhasePolynomial.actual (boundaryGramPolynomial m i j) (fun ij => Q ij.1 ij.2) =
      gramNumerator m Q i j) ∧
    PhasePolynomial.actual (boundaryDenominatorPolynomial m) (fun ij => Q ij.1 ij.2) =
      gramDenominator m Q := by
  let ε := eval (Sum.elim (fun ij : ObservationIndex => Q ij.1 ij.2)
    (fun ij : ObservationIndex => star (Q ij.1 ij.2)))
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  have hmod (p : MvPolynomial (Word 3) ℂ) : ε (modulusPolynomial p) = modulus (eval t p) := by
    change PhasePolynomial.actual (modulusPolynomial p) _ = _
    simp only [modulusPolynomial, PhasePolynomial.actual, map_mul]
    change PhasePolynomial.actual (columnPolynomial p) _ *
      PhasePolynomial.actual (polynomialConjugate (columnPolynomial p)) _ = _
    rw [polynomialConjugate_eval, columnPolynomial_eval]
    rfl
  have hL : contractionPolynomial.map ε = leftNumeratorMap t := by
    ext k w
    change ε (contractionPolynomial k w) = _
    by_cases hw : w 2 = k <;>
      simp only [contractionPolynomial, hw, ite_true, ite_false, map_mul, map_zero]
    · change PhasePolynomial.actual (columnPolynomial _) _ *
        PhasePolynomial.actual (columnPolynomial _) _ = _
      rw [columnPolynomial_eval, columnPolynomial_eval]
      simp [leftNumeratorMap, boundaryLeft, hw, t]
    · simp [leftNumeratorMap, boundaryLeft, hw]
  have hB : ε.mapMatrix contractedPolynomial =
      leftNumeratorMap t * Q * (leftNumeratorMap t)ᴴ := by
    change contractedPolynomial.map ε = _
    rw [contractedPolynomial, Matrix.map_mul, Matrix.map_mul, hL]
    congr 1
    · congr 1
      ext i j
      change ε (X (Sum.inl (i, j))) = Q i j
      exact eval_X _
    · ext w k
      change PhasePolynomial.actual (polynomialConjugate (contractionPolynomial k w)) _ = _
      rw [polynomialConjugate_eval]
      exact congrArg star (congrFun (congrFun hL k) w)
  have hT : ε.mapMatrix observedTransferPolynomial = transferNumerator t := by
    dsimp only [transferNumerator]
    rw [← OpenBoundaryMPSDensityGenericity.numeratorTransfer_eval]
    ext ij kl
    change ε (rename _ _) = _
    rw [eval_rename]
    change eval _ _ = eval _ _
    congr 2
    funext w; cases w <;> rfl
  constructor
  · intro i j
    change ε ((modulusPolynomial basisNumerator.det ^ m) *
      (observedTransferPolynomial.adjugate ^ m *ᵥ
        (fun kl => contractedPolynomial kl.1 kl.2)) (i, j)) = _
    rw [map_mul, map_pow, hmod]
    change _ * ε ((observedTransferPolynomial.adjugate ^ m *ᵥ
      (fun kl => contractedPolynomial kl.1 kl.2)) (i, j)) = _
    have hpow : (observedTransferPolynomial.adjugate ^ m).map ε =
        (transferNumerator t).adjugate ^ m := by
      change ε.mapMatrix (observedTransferPolynomial.adjugate ^ m) = _
      rw [map_pow, RingHom.map_adjugate, hT]
    rw [RingHom.map_mulVec, hpow]
    have hb : (ε ∘ fun kl : Fin 2 × Fin 2 => contractedPolynomial kl.1 kl.2) =
        fun kl : Fin 2 × Fin 2 => (leftNumeratorMap t * Q * (leftNumeratorMap t)ᴴ) kl.1 kl.2 := by
      funext kl
      exact congrFun (congrFun hB kl.1) kl.2
    rw [hb]
    rfl
  · change ε _ = _
    rw [boundaryDenominatorPolynomial, map_mul, map_pow, map_pow, hmod, RingHom.map_det, hT]
    rfl
/-- Thirteen real quotient coordinates: five complex core entries, sigma and eta.
Here sigma is the boundary Gram's 00 entry, not the older positive boundary amplitude. -/
abbrev Quotient := OpenBoundaryMPSTwoSiteMinimality.Parameter
def quotientCoordinates (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) : Quotient :=
  (coreCoordinates (OpenBoundaryMPSDensityGenericity.fixedTensor Q),
    (boundaryGram m Q 0 0).re, boundaryGram m Q 1 0 / boundaryGram m Q 0 0)
/-- Only the positive phase representative uses a square root. -/
def positiveBoundary (p : Quotient) : Fin 2 → ℂ :=
  ![((Real.sqrt p.2.1 : ℝ) : ℂ), (Real.sqrt p.2.1 : ℂ) * p.2.2]
private lemma positiveBoundary_gram (q : Fin 2 → ℂ) (hq : q 0 ≠ 0) :
    let p : Quotient := (0, Complex.normSq (q 0), q 1 / q 0)
    vecMulVec (positiveBoundary p) (star (positiveBoundary p)) = vecMulVec q (star q) := by
  dsimp only
  have hs : ((Real.sqrt (Complex.normSq (q 0)) : ℝ) : ℂ) ^ 2 =
      q 0 * star (q 0) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Complex.normSq_nonneg _)]
    exact (Complex.mul_conj (q 0)).symm
  have hstar : (starRingEnd ℂ) (q 0) ≠ 0 := star_ne_zero.mpr hq
  change _ = q 0 * (starRingEnd ℂ) (q 0) at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveBoundary, vecMulVec, star_mul, star_div₀]
  · simpa only [pow_two] using hs
  · field_simp [hq, hstar]
    linear_combination (starRingEnd ℂ) (q 1) * hs
  · field_simp [hq, hstar]
    linear_combination q 1 * hs
  · field_simp [hq, hstar]
    linear_combination q 1 * (starRingEnd ℂ) (q 1) * hs
/-- The actual boundary Gram gives sigma=|q0|² and the correctly oriented eta=q1/q0.
The square-root representative has exactly the original state's unit-phase class. -/
theorem actual_quotient_representative (m : ℕ) (ψ : Word (3 + m) → ℂ)
    (hψ : ψ ∈ openBoundaryMPS (3 + m))
    (hg : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor (rawPrefix 3 m ψ)))
        OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0)
    (h00 : boundaryGram m (rawPrefix 3 m ψ) 0 0 ≠ 0) :
    let p := quotientCoordinates m (rawPrefix 3 m ψ)
    0 < p.2.1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      ψ = z • mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p) (positiveBoundary p) := by
  let Q := rawPrefix 3 m ψ
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  obtain ⟨q, hstate, hGram⟩ := actual_boundary_gram m ψ hψ hg
  have hq : q 0 ≠ 0 := by
    intro hz
    exact h00 (by rw [hGram]; simp [vecMulVec_apply, hz])
  have hsigma : (boundaryGram m Q 0 0).re = Complex.normSq (q 0) := by
    rw [hGram]
    change (q 0 * star (q 0)).re = _
    change (q 0 * (starRingEnd ℂ) (q 0)).re = _
    rw [Complex.mul_conj]
    rfl
  have hstar : star (q 0) ≠ 0 := star_ne_zero.mpr hq
  have heta : boundaryGram m Q 1 0 / boundaryGram m Q 0 0 = q 1 / q 0 := by
    rw [hGram]
    change (q 1 * star (q 0)) / (q 0 * star (q 0)) = _
    field_simp
  have hrep : vecMulVec (positiveBoundary (quotientCoordinates m Q))
      (star (positiveBoundary (quotientCoordinates m Q))) = vecMulVec q (star q) := by
    simpa only [positiveBoundary, quotientCoordinates, hsigma, heta] using
      positiveBoundary_gram q hq
  obtain ⟨z, hz, hphase⟩ := boundary_phase _ q hrep
  have ht : t ∈ openBoundaryMPS 3 := by
    obtain ⟨a₀,a₁,l,r,hs⟩ := hψ
    obtain ⟨g,hg'⟩ := observed_coherent m ![a₀,a₁] l r (Pi.single (fun _ => 0) 1)
    refine ⟨a₀,a₁,l,g,?_⟩
    change rawPrefix 3 m (mpsState (3 + m) a₀ a₁ l r) *ᵥ Pi.single _ 1 =
      mpsState 3 a₀ a₁ l g at hg'
    rw [← hg', ← hs, Matrix.mulVec_single_one]
    rfl
  have hc := (OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero t).mp hg
  obtain ⟨hl,hA⟩ := canonical_shape t ht hc.1
  change 0 < (quotientCoordinates m Q).2.1 ∧ _
  refine ⟨?_, z, hz, ?_⟩
  · change 0 < (boundaryGram m Q 0 0).re
    rw [hsigma]
    exact Complex.normSq_pos.mpr hq
  · change ψ = z • mpsState (3 + m)
      (OpenBoundaryMPSTwoSiteMinimality.core (quotientCoordinates m Q) 0)
      (OpenBoundaryMPSTwoSiteMinimality.core (quotientCoordinates m Q) 1)
      (OpenBoundaryMPSTwoSiteMinimality.left (quotientCoordinates m Q))
      (positiveBoundary (quotientCoordinates m Q))
    have hl' : OpenBoundaryMPSTwoSiteMinimality.left (quotientCoordinates m Q) =
        reconstructedLeft t := hl
    have hA' : OpenBoundaryMPSTwoSiteMinimality.core (quotientCoordinates m Q) =
        canonicalCore t := hA
    rw [hl', hA']
    rw [hstate, hphase]
    funext w
    simp only [state_formula, mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul]
    rfl
private lemma canonical_self (θ : OpenBoundaryMPSTwoSiteMinimality.Parameter)
    (g : Fin 2 → ℂ) (t : Word 3 → ℂ)
    (ht : mpsState 3 (OpenBoundaryMPSTwoSiteMinimality.core θ 0)
      (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) g = t)
    (hg : eval t chartPoly ≠ 0) :
    coreCoordinates t = θ.1 ∧ reconstructedLeft t = OpenBoundaryMPSTwoSiteMinimality.left θ ∧
      canonicalCore t = OpenBoundaryMPSTwoSiteMinimality.core θ := by
  have him : t ∈ openBoundaryMPS 3 := ⟨_, _, _, g, ht.symm⟩
  let η : OpenBoundaryMPSTwoSiteMinimality.Parameter := (coreCoordinates t, 0, 0)
  obtain ⟨hl,hA⟩ := canonical_shape t him hg
  obtain ⟨q,hq⟩ := gauge_lift t (OpenBoundaryMPSTwoSiteMinimality.core θ)
    (OpenBoundaryMPSTwoSiteMinimality.left θ) g ht hg 3 g
  have he : mpsState 3 (OpenBoundaryMPSTwoSiteMinimality.core θ 0)
      (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) g =
      mpsState 3 (OpenBoundaryMPSTwoSiteMinimality.core η 0)
        (OpenBoundaryMPSTwoSiteMinimality.core η 1) (OpenBoundaryMPSTwoSiteMinimality.left η) q := by
    rw [hl,hA]
    exact hq
  have hc : θ.1 = coreCoordinates t :=
    OpenBoundaryMPSTwoSiteMinimality.canonical_core_rigidity θ η g q he (by rwa [ht])
  refine ⟨hc.symm, ?_, ?_⟩
  · rw [← hl]
    simp only [OpenBoundaryMPSTwoSiteMinimality.left, hc]
  · rw [← hA]
    simp only [OpenBoundaryMPSTwoSiteMinimality.core, hc]
private lemma canonical_gram (m : ℕ) (θ : OpenBoundaryMPSTwoSiteMinimality.Parameter)
    (q : Fin 2 → ℂ)
    (hg : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor (rawPrefix 3 m
        (mpsState (3 + m) (OpenBoundaryMPSTwoSiteMinimality.core θ 0)
          (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) q))))
        OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0) :
    let Q := rawPrefix 3 m (mpsState (3 + m) (OpenBoundaryMPSTwoSiteMinimality.core θ 0)
      (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) q)
    coreCoordinates (OpenBoundaryMPSDensityGenericity.fixedTensor Q) = θ.1 ∧
      boundaryGram m Q = vecMulVec q (star q) := by
  dsimp only
  let ψ := mpsState (3 + m) (OpenBoundaryMPSTwoSiteMinimality.core θ 0)
    (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) q
  let Q := rawPrefix 3 m ψ
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  obtain ⟨hchart,hE⟩ := (OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero t).mp hg
  obtain ⟨g,hg'⟩ := observed_coherent m (OpenBoundaryMPSTwoSiteMinimality.core θ)
    (OpenBoundaryMPSTwoSiteMinimality.left θ) q (Pi.single (fun _ => 0) 1)
  have ht : mpsState 3 (OpenBoundaryMPSTwoSiteMinimality.core θ 0)
      (OpenBoundaryMPSTwoSiteMinimality.core θ 1) (OpenBoundaryMPSTwoSiteMinimality.left θ) g = t := by
    rw [← hg', Matrix.mulVec_single_one]
    rfl
  obtain ⟨hc,hl,hA⟩ := canonical_self θ g t ht hchart
  refine ⟨hc, ?_⟩
  have him : t ∈ openBoundaryMPS 3 := ⟨_,_,_,g,ht.symm⟩
  have hM : (transferNumerator t).det ≠ 0 := by
    dsimp only [transferNumerator]
    rw [← OpenBoundaryMPSDensityGenericity.numeratorTransfer_eval]
    have hm := (OpenBoundaryMPSDensityGenericity.canonical_transfer_det t hchart).mpr hE
    simpa only [PhasePolynomial.actual, RingHom.map_det] using hm
  apply gram_formula m Q him hchart hM (vecMulVec q (star q))
  change Q = prefixMap (canonicalCore t) (reconstructedLeft t) 3 *
    (transfer (canonicalCore t))^[m] (vecMulVec q (star q)) *
    (prefixMap (canonicalCore t) (reconstructedLeft t) 3)ᴴ
  rw [hl,hA]
  exact density_factor 3 m _ _ _
/-- The raw polynomial observation uses boundary (1,eta), followed by the real scale sigma. -/
def quotientObservation (k m : ℕ) (p : Quotient) : Matrix (Word k) (Word k) ℂ :=
  (p.2.1 : ℂ) • rawPrefix k m
    (OpenBoundaryMPSTwoSiteMinimality.state (k + m) (p.1, 1, p.2.2))
private lemma rawPrefix_scale (k m : ℕ) (z : ℂ) (ψ : Word (k + m) → ℂ) :
    rawPrefix k m (z • ψ) = modulus z • rawPrefix k m ψ := by
  have hC : amplitudeColumns k m (z • ψ) = z • amplitudeColumns k m ψ := rfl
  rw [rawPrefix, hC, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rfl
private lemma positive_observation (k m : ℕ) (p : Quotient) (hp : 0 ≤ p.2.1) :
    rawPrefix k m (mpsState (k + m) (OpenBoundaryMPSTwoSiteMinimality.core p 0)
      (OpenBoundaryMPSTwoSiteMinimality.core p 1) (OpenBoundaryMPSTwoSiteMinimality.left p)
      (positiveBoundary p)) = quotientObservation k m p := by
  have hs : mpsState (k + m) (OpenBoundaryMPSTwoSiteMinimality.core p 0)
      (OpenBoundaryMPSTwoSiteMinimality.core p 1) (OpenBoundaryMPSTwoSiteMinimality.left p)
      (positiveBoundary p) = (Real.sqrt p.2.1 : ℂ) •
        OpenBoundaryMPSTwoSiteMinimality.state (k + m) (p.1, 1, p.2.2) := by
    have hr : positiveBoundary p = (Real.sqrt p.2.1 : ℂ) •
        OpenBoundaryMPSTwoSiteMinimality.right (p.1, 1, p.2.2) := by
      ext i
      fin_cases i <;> simp [positiveBoundary, OpenBoundaryMPSTwoSiteMinimality.right]
    rw [hr]
    funext w
    simp only [state_formula, mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
      OpenBoundaryMPSTwoSiteMinimality.state, OpenBoundaryMPSTwoSiteMinimality.core,
      OpenBoundaryMPSTwoSiteMinimality.left]
  rw [hs, rawPrefix_scale]
  have hz : modulus (Real.sqrt p.2.1 : ℂ) = (p.2.1 : ℂ) := by
    simp only [modulus, Complex.star_def, Complex.conj_ofReal, ← sq,
      ← Complex.ofReal_pow, Real.sq_sqrt hp]
  rw [hz]
  rfl
/-- Exact observable retraction to all thirteen quotient coordinates.
The hypothesis is the fixed observed recovery condition, with sigma strictly positive. -/
theorem quotient_retraction (m : ℕ) (p : Quotient) (hp : 0 < p.2.1)
    (hg : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor (quotientObservation 3 m p)))
        OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0) :
    quotientCoordinates m (quotientObservation 3 m p) = p := by
  have hobs := positive_observation 3 m p hp.le
  have hg' := hg
  rw [← hobs] at hg'
  obtain ⟨hc,hGram⟩ := canonical_gram m p (positiveBoundary p) hg'
  rw [hobs] at hc hGram
  have hs : (Real.sqrt p.2.1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
  apply Prod.ext hc
  apply Prod.ext
  · change (boundaryGram m (quotientObservation 3 m p) 0 0).re = p.2.1
    rw [hGram]
    simp [positiveBoundary, vecMulVec, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt hp.le]
  · change boundaryGram m (quotientObservation 3 m p) 1 0 /
      boundaryGram m (quotientObservation 3 m p) 0 0 = p.2.2
    rw [hGram]
    simp [positiveBoundary, vecMulVec, hs, mul_div_mul_right]
/-- A fixed real polynomial refinement: recovery and a nonzero boundary numerator at 00. -/
def quotientLocusPolynomial (m : ℕ) : MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ :=
  OpenBoundaryMPSDensityGenericity.observedPolynomial *
    OpenBoundaryMPSDensityGenericity.normPolynomial (boundaryGramPolynomial m 0 0)
theorem quotientLocus_eval (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) :
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
      (quotientLocusPolynomial m) ≠ 0 ↔
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor Q))
      OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 ∧ gramNumerator m Q 0 0 ≠ 0 := by
  rw [quotientLocusPolynomial, map_mul, mul_ne_zero_iff,
    OpenBoundaryMPSDensityGenericity.observedPolynomial_eval,
    OpenBoundaryMPSDensityGenericity.normPolynomial_eval,
    (polynomial_evaluations m Q).1 0 0]
  simp only [ne_eq, Complex.normSq_eq_zero]
private lemma gramDenominator_ne_zero (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (hg : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor Q))
      OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0) : gramDenominator m Q ≠ 0 := by
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  obtain ⟨hc,hE⟩ := (OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero t).mp hg
  have hd := hc
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hd
  have hM : (transferNumerator t).det ≠ 0 := by
    dsimp only [transferNumerator]
    rw [← OpenBoundaryMPSDensityGenericity.numeratorTransfer_eval]
    have hm := (OpenBoundaryMPSDensityGenericity.canonical_transfer_det t hc).mpr hE
    simpa only [PhasePolynomial.actual, RingHom.map_det] using hm
  exact mul_ne_zero (pow_ne_zero _ (modulus_ne_zero hd.1.1.1.1)) (pow_ne_zero _ hM)
/-- The positive-real-denominator version of the exact polynomial boundary numerator. -/
def positiveGramPolynomial (m : ℕ) :
    Matrix (Fin 2) (Fin 2) (PhasePolynomial.Poly ObservationIndex) :=
  polynomialConjugate observedTransferPolynomial.det ^ m • boundaryGramPolynomial m
/-- The real positive denominator is h(d)^(m+2) times normSq(det M)^m. -/
def positiveGramDenominator (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ) : ℝ :=
  Complex.normSq (eval (OpenBoundaryMPSDensityGenericity.fixedTensor Q) minorPoly) ^ (m + 2) *
    Complex.normSq (transferNumerator (OpenBoundaryMPSDensityGenericity.fixedTensor Q)).det ^ m
private lemma positive_gram_formula (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (hg : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (OpenBoundaryMPSDensityGenericity.fixedTensor Q))
      OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0) :
    0 < positiveGramDenominator m Q ∧
      ∀ i j, boundaryGram m Q i j =
        PhasePolynomial.actual (positiveGramPolynomial m i j) (fun ij => Q ij.1 ij.2) /
          (positiveGramDenominator m Q : ℂ) := by
  have hden := gramDenominator_ne_zero m Q hg
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  have hd : eval t minorPoly ≠ 0 := by
    intro hz
    apply hden
    simp [gramDenominator, t, modulus, hz]
  have hT : (transferNumerator t).det ≠ 0 := by
    obtain ⟨hc,hE⟩ := (OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero t).mp hg
    dsimp only [transferNumerator]
    rw [← OpenBoundaryMPSDensityGenericity.numeratorTransfer_eval]
    have hm := (OpenBoundaryMPSDensityGenericity.canonical_transfer_det t hc).mpr hE
    simpa only [PhasePolynomial.actual, RingHom.map_det] using hm
  refine ⟨mul_pos (pow_pos (Complex.normSq_pos.mpr hd) _)
    (pow_pos (Complex.normSq_pos.mpr hT) _), ?_⟩
  intro i j
  have heT : PhasePolynomial.actual observedTransferPolynomial.det (fun ij => Q ij.1 ij.2) =
      (transferNumerator t).det := by
    rw [PhasePolynomial.actual, RingHom.map_det]
    congr 1
    dsimp only [transferNumerator]
    rw [← OpenBoundaryMPSDensityGenericity.numeratorTransfer_eval]
    ext ij kl
    simp only [observedTransferPolynomial, RingHom.mapMatrix_apply, Matrix.map_apply,
      eval_rename]
    congr 2
    funext w; cases w <;> rfl
  change (gramDenominator m Q)⁻¹ * gramNumerator m Q i j = _
  change _ = eval (Sum.elim (fun ij : ObservationIndex => Q ij.1 ij.2)
    (fun ij => star (Q ij.1 ij.2)))
    (polynomialConjugate observedTransferPolynomial.det ^ m * boundaryGramPolynomial m i j) / _
  rw [map_mul, map_pow]
  change _ = (PhasePolynomial.actual (polynomialConjugate observedTransferPolynomial.det) _ ^ m *
    PhasePolynomial.actual (boundaryGramPolynomial m i j) _) / _
  rw [polynomialConjugate_eval, heT, (polynomial_evaluations m Q).1 i j]
  have hmod (z : ℂ) : modulus z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  simp only [gramDenominator, positiveGramDenominator, hmod, Complex.ofReal_mul,
    Complex.ofReal_pow]
  rw [← Complex.mul_conj (transferNumerator t).det, mul_pow]
  dsimp only [t] at hT
  have hstar : (starRingEnd ℂ) (transferNumerator
      (OpenBoundaryMPSDensityGenericity.fixedTensor Q)).det ≠ 0 := star_ne_zero.mpr hT
  dsimp only [t]
  simp only [Complex.star_def]
  field_simp [hT, hstar]
  <;> ring
/-- Five real core parts, five imaginary core parts, sigma, Re eta and Im eta. -/
abbrev QuotientRealIndex := Fin 5 ⊕ (Fin 5 ⊕ Fin 3)
def quotientRealCoordinates (p : Quotient) : QuotientRealIndex → ℝ :=
  Sum.elim (fun i => (p.1 i).re)
    (Sum.elim (fun i => (p.1 i).im) (fun i => ![p.2.1, p.2.2.re, p.2.2.im] i))
private def coreRatioNumerators : Fin 5 → PhasePolynomial.Poly ObservationIndex :=
  ![columnPolynomial (leftNumerator 0),
    columnPolynomial (minorPoly * matrixNumerator 0 0 0),
    columnPolynomial (minorPoly * matrixNumerator 0 0 1),
    columnPolynomial (minorPoly * matrixNumerator 1 0 0),
    columnPolynomial (minorPoly * matrixNumerator 1 0 1)]
private def coreRatioDenominators : Fin 5 → PhasePolynomial.Poly ObservationIndex :=
  ![columnPolynomial minorPoly, columnPolynomial basisNumerator.det,
    columnPolynomial basisNumerator.det, columnPolynomial basisNumerator.det,
    columnPolynomial basisNumerator.det]
private def quotientRatioNumerator (m : ℕ) : QuotientRealIndex →
    PhasePolynomial.Poly ObservationIndex :=
  Sum.elim coreRatioNumerators (Sum.elim coreRatioNumerators
    (fun i => ![boundaryGramPolynomial m 0 0, boundaryGramPolynomial m 1 0,
      boundaryGramPolynomial m 1 0] i))
private def quotientRatioDenominator (m : ℕ) : QuotientRealIndex →
    PhasePolynomial.Poly ObservationIndex :=
  Sum.elim coreRatioDenominators (Sum.elim coreRatioDenominators
    (fun i => ![boundaryDenominatorPolynomial m, boundaryGramPolynomial m 0 0,
      boundaryGramPolynomial m 0 0] i))
private def imaginaryCoordinate : QuotientRealIndex → Bool :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun i => i == 2))
/-- Explicit real polynomial numerators for every one of the thirteen coordinates. -/
def quotientRealNumerator (m : ℕ) (i : QuotientRealIndex) :
    MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ :=
  let p := PhasePolynomial.toCartesian
    (quotientRatioNumerator m i * polynomialConjugate (quotientRatioDenominator m i))
  if imaginaryCoordinate i then OpenBoundaryMPSDensityGenericity.imagCoeff p
    else OpenBoundaryMPSDensityGenericity.realCoeff p
/-- The corresponding real denominators are sums of squares of real polynomials. -/
def quotientRealDenominator (m : ℕ) (i : QuotientRealIndex) :
    MvPolynomial (ObservationIndex ⊕ ObservationIndex) ℝ :=
  OpenBoundaryMPSDensityGenericity.normPolynomial (quotientRatioDenominator m i)
private lemma coefficient_actual {ι : Type*} (p : PhasePolynomial.Poly ι) (z : ι → ℂ) :
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates z)
      (OpenBoundaryMPSDensityGenericity.realCoeff (PhasePolynomial.toCartesian p)) =
        (PhasePolynomial.actual p z).re ∧
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates z)
      (OpenBoundaryMPSDensityGenericity.imagCoeff (PhasePolynomial.toCartesian p)) =
        (PhasePolynomial.actual p z).im := by
  have h := OpenBoundaryMPSDensityGenericity.coefficient_eval (PhasePolynomial.toCartesian p)
    (OpenBoundaryMPSDensityGenericity.realCoordinates z)
  have hv : (fun i => ((OpenBoundaryMPSDensityGenericity.realCoordinates z i) : ℂ)) =
      PhasePolynomial.cartesian z := by
    funext i; cases i <;> rfl
  rw [hv, PhasePolynomial.actual_cartesian] at h
  exact h
private lemma real_ratio_eval (m : ℕ) (i : QuotientRealIndex)
    (Q : Matrix (Word 3) (Word 3) ℂ) :
    let z := fun ij : ObservationIndex => Q ij.1 ij.2
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates z) (quotientRealNumerator m i) /
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates z) (quotientRealDenominator m i) =
    if imaginaryCoordinate i then
      (PhasePolynomial.actual (quotientRatioNumerator m i) z /
        PhasePolynomial.actual (quotientRatioDenominator m i) z).im
    else (PhasePolynomial.actual (quotientRatioNumerator m i) z /
        PhasePolynomial.actual (quotientRatioDenominator m i) z).re := by
  dsimp only
  let z := fun ij : ObservationIndex => Q ij.1 ij.2
  have h := coefficient_actual
    (quotientRatioNumerator m i * polynomialConjugate (quotientRatioDenominator m i)) z
  have he : PhasePolynomial.actual
      (quotientRatioNumerator m i * polynomialConjugate (quotientRatioDenominator m i)) z =
      PhasePolynomial.actual (quotientRatioNumerator m i) z *
        star (PhasePolynomial.actual (quotientRatioDenominator m i) z) := by
    change eval _ (_ * _) = _
    rw [map_mul]
    change PhasePolynomial.actual (quotientRatioNumerator m i) z *
      PhasePolynomial.actual (polynomialConjugate (quotientRatioDenominator m i)) z = _
    rw [polynomialConjugate_eval]
  rw [he] at h
  simp only [quotientRealNumerator, quotientRealDenominator,
    OpenBoundaryMPSDensityGenericity.normPolynomial_eval]
  by_cases hb : imaginaryCoordinate i = true <;> simp only [hb, Bool.false_eq_true, ite_true, ite_false]
  · rw [h.2]
    simp [Complex.div_im, Complex.mul_im, Complex.star_def]
    <;> ring
  · rw [h.1]
    simp [Complex.div_re, Complex.mul_re, Complex.star_def]
    <;> ring
private lemma quotient_ratios (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (hc : eval (OpenBoundaryMPSDensityGenericity.fixedTensor Q) chartPoly ≠ 0)
    (i : Fin 5) :
    PhasePolynomial.actual (coreRatioNumerators i) (fun ij => Q ij.1 ij.2) /
      PhasePolynomial.actual (coreRatioDenominators i) (fun ij => Q ij.1 ij.2) =
        coreCoordinates (OpenBoundaryMPSDensityGenericity.fixedTensor Q) i := by
  let t := OpenBoundaryMPSDensityGenericity.fixedTensor Q
  have hA := (chart_scalars t hc).2.1
  dsimp only [t] at hA
  fin_cases i <;> simp [coreRatioNumerators, coreRatioDenominators,
    columnPolynomial_eval, coreCoordinates, canonicalCore, hA, reconstructedLeft,
    Matrix.smul_apply, map_mul]
  all_goals ring
/-- Each quotient coordinate is an exact ratio of real polynomials on the refined observed chart.
This includes the positive real denominator formula for the whole boundary Gram. -/
private def coreVariable (i : Fin 5) : MvPolynomial QuotientRealIndex ℂ :=
  X (.inl i) + C Complex.I * X (.inr (.inl i))
private def etaVariable : MvPolynomial QuotientRealIndex ℂ :=
  X (.inr (.inr 1)) + C Complex.I * X (.inr (.inr 2))
private def quotientCorePolynomials : Fin 2 →
    Matrix (Fin 2) (Fin 2) (MvPolynomial QuotientRealIndex ℂ) :=
  ![!![coreVariable 1, coreVariable 2;
      1 - coreVariable 0 * coreVariable 1, -coreVariable 0 * coreVariable 2],
    !![coreVariable 3, coreVariable 4;
      -coreVariable 0 * coreVariable 3, 1 - coreVariable 0 * coreVariable 4]]
private def quotientParameterPolynomials : parameterIndex → MvPolynomial QuotientRealIndex ℂ :=
  Sum.elim (fun ijk => quotientCorePolynomials ijk.1 ijk.2.1 ijk.2.2)
    (Sum.elim (fun i => ![coreVariable 0, 1] i) (fun i => ![1, etaVariable] i))
private def quotientStatePolynomial (n : ℕ) (w : Word n) :
    MvPolynomial QuotientRealIndex ℂ :=
  eval₂Hom C quotientParameterPolynomials (parameterPolys n w)
private def quotientObservationComplexPolynomial (k m : ℕ) (u v : Word k) :
    MvPolynomial QuotientRealIndex ℂ :=
  X (.inr (.inr 0)) * ∑ b : Word m,
    quotientStatePolynomial (k + m) (Fin.append u b) *
      map (starRingEnd ℂ) (quotientStatePolynomial (k + m) (Fin.append v b))
/-- Real coefficient polynomials for either component of every raw quotient observation entry. -/
def quotientObservationPolynomial (k m : ℕ) (u v : Word k) (imaginary : Bool) :
    MvPolynomial QuotientRealIndex ℝ :=
  if imaginary then OpenBoundaryMPSDensityGenericity.imagCoeff
    (quotientObservationComplexPolynomial k m u v)
  else OpenBoundaryMPSDensityGenericity.realCoeff
    (quotientObservationComplexPolynomial k m u v)
private lemma quotientObservation_eval (k m : ℕ) (u v : Word k) (imaginary : Bool)
    (p : Quotient) :
    eval (quotientRealCoordinates p) (quotientObservationPolynomial k m u v imaginary) =
      if imaginary then (quotientObservation k m p u v).im
      else (quotientObservation k m p u v).re := by
  let r := fun i : QuotientRealIndex => (quotientRealCoordinates p i : ℂ)
  have hc (i : Fin 5) : eval r (coreVariable i) = p.1 i := by
    simp only [coreVariable, map_add, map_mul, eval_X, eval_C]
    simpa only [r, quotientRealCoordinates, Sum.elim_inl, Sum.elim_inr, mul_comm] using
      Complex.re_add_im (p.1 i)
  have he : eval r etaVariable = p.2.2 := by
    simp only [etaVariable, map_add, map_mul, eval_X, eval_C]
    simpa [r, quotientRealCoordinates, mul_comm] using Complex.re_add_im p.2.2
  let θ : OpenBoundaryMPSTwoSiteMinimality.Parameter := (p.1, 1, p.2.2)
  let x : parameterIndex → ℂ := Sum.elim
    (fun ijk => OpenBoundaryMPSTwoSiteMinimality.core θ ijk.1 ijk.2.1 ijk.2.2)
    (Sum.elim (OpenBoundaryMPSTwoSiteMinimality.left θ)
      (OpenBoundaryMPSTwoSiteMinimality.right θ))
  have hx : (eval r) ∘ quotientParameterPolynomials = x := by
    funext i
    rcases i with ⟨i,j,l⟩ | i | i
    · fin_cases i <;> fin_cases j <;> fin_cases l <;>
        simp [quotientParameterPolynomials, quotientCorePolynomials, x, θ,
          OpenBoundaryMPSTwoSiteMinimality.core, hc]
    · fin_cases i <;> simp [quotientParameterPolynomials, x, θ,
        OpenBoundaryMPSTwoSiteMinimality.left, hc]
    · fin_cases i <;> simp [quotientParameterPolynomials, x, θ,
        OpenBoundaryMPSTwoSiteMinimality.right, he]
  have hhom : (eval r).comp (eval₂Hom C quotientParameterPolynomials) = eval x := by
    ext i
    · simp
    · simp only [RingHom.comp_apply, eval₂Hom_X', eval_X]
      exact congrFun hx i
  have hstate (n : ℕ) (w : Word n) : eval r (quotientStatePolynomial n w) =
      OpenBoundaryMPSTwoSiteMinimality.state n θ w := by
    change ((eval r).comp (eval₂Hom C quotientParameterPolynomials)) (parameterPolys n w) = _
    rw [hhom]
    have hs := congrFun (parameter_eval n x) w
    exact hs
  have hstar (P : MvPolynomial QuotientRealIndex ℂ) :
      eval r (map (starRingEnd ℂ) P) = star (eval r P) := by
    have hr : (starRingEnd ℂ) ∘ r = r := by
      funext i; simp [r]
    calc
      eval r (map (starRingEnd ℂ) P) =
          eval ((starRingEnd ℂ) ∘ r) (map (starRingEnd ℂ) P) := by rw [hr]
      _ = star (eval r P) := (MvPolynomial.map_eval (starRingEnd ℂ) r P).symm
  have hobs : eval r (quotientObservationComplexPolynomial k m u v) =
      quotientObservation k m p u v := by
    simp only [quotientObservationComplexPolynomial, map_mul, eval_X, map_sum, hstate, hstar]
    rfl
  have hr := OpenBoundaryMPSDensityGenericity.coefficient_eval
    (quotientObservationComplexPolynomial k m u v) (quotientRealCoordinates p)
  change eval _ _ = (eval r _).re ∧ eval _ _ = (eval r _).im at hr
  rw [hobs] at hr
  cases imaginary <;> simp only [quotientObservationPolynomial, Bool.false_eq_true,
    ite_false, ite_true] <;> first | exact hr.1 | exact hr.2
theorem rational_quotient_inverse (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (hQ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Q ij.1 ij.2)) (quotientLocusPolynomial m) ≠ 0) :
    Fintype.card QuotientRealIndex = 13 ∧
    (∀ i : QuotientRealIndex,
      0 < eval (OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
        (quotientRealDenominator m i) ∧
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
        (quotientRealNumerator m i) /
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates (fun ij => Q ij.1 ij.2))
        (quotientRealDenominator m i) =
      quotientRealCoordinates (quotientCoordinates m Q) i) ∧
    0 < positiveGramDenominator m Q ∧
    (∀ i j, boundaryGram m Q i j =
      PhasePolynomial.actual (positiveGramPolynomial m i j) (fun ij => Q ij.1 ij.2) /
        (positiveGramDenominator m Q : ℂ)) ∧
    (∀ (k a : ℕ) (u v : Word k) (imaginary : Bool) (p : Quotient),
      eval (quotientRealCoordinates p) (quotientObservationPolynomial k a u v imaginary) =
        if imaginary then (quotientObservation k a p u v).im
        else (quotientObservation k a p u v).re) ∧
    boundaryGram m Q 0 0 ≠ 0 := by
  obtain ⟨hg,hnum⟩ := (quotientLocus_eval m Q).mp hQ
  have hc := (OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero _).mp hg
  have hdv := hc.1
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hdv
  have hden := gramDenominator_ne_zero m Q hg
  have heval := polynomial_evaluations m Q
  have h00 : boundaryGram m Q 0 0 ≠ 0 := by
    change (gramDenominator m Q)⁻¹ * gramNumerator m Q 0 0 ≠ 0
    exact mul_ne_zero (inv_ne_zero hden) hnum
  refine ⟨by decide, ?_, (positive_gram_formula m Q hg).1,
    (positive_gram_formula m Q hg).2, quotientObservation_eval, h00⟩
  intro i
  have hratio :
      (if imaginaryCoordinate i then
        (PhasePolynomial.actual (quotientRatioNumerator m i) (fun ij => Q ij.1 ij.2) /
          PhasePolynomial.actual (quotientRatioDenominator m i) (fun ij => Q ij.1 ij.2)).im
      else (PhasePolynomial.actual (quotientRatioNumerator m i) (fun ij => Q ij.1 ij.2) /
        PhasePolynomial.actual (quotientRatioDenominator m i) (fun ij => Q ij.1 ij.2)).re) =
      quotientRealCoordinates (quotientCoordinates m Q) i := by
    rcases i with i | i | i
    · simpa only [quotientRatioNumerator, quotientRatioDenominator, imaginaryCoordinate,
        Sum.elim_inl, Bool.false_eq_true, ite_false, quotientRealCoordinates,
        quotientCoordinates] using congrArg Complex.re (quotient_ratios m Q hc.1 i)
    · simpa only [quotientRatioNumerator, quotientRatioDenominator, imaginaryCoordinate,
        Sum.elim_inl, Sum.elim_inr, ite_true, quotientRealCoordinates,
        quotientCoordinates] using congrArg Complex.im (quotient_ratios m Q hc.1 i)
    · have hs (a b : Fin 2) : boundaryGram m Q a b =
          gramNumerator m Q a b / gramDenominator m Q := by
        change (gramDenominator m Q)⁻¹ * gramNumerator m Q a b = _
        ring
      have heta : gramNumerator m Q 1 0 / gramNumerator m Q 0 0 =
          boundaryGram m Q 1 0 / boundaryGram m Q 0 0 := by
        rw [hs,hs]
        field_simp
      fin_cases i
      · change (PhasePolynomial.actual (boundaryGramPolynomial m 0 0) _ /
          PhasePolynomial.actual (boundaryDenominatorPolynomial m) _).re =
            (boundaryGram m Q 0 0).re
        rw [heval.1,heval.2]
        exact congrArg Complex.re (hs 0 0).symm
      · change (PhasePolynomial.actual (boundaryGramPolynomial m 1 0) _ /
          PhasePolynomial.actual (boundaryGramPolynomial m 0 0) _).re =
            (boundaryGram m Q 1 0 / boundaryGram m Q 0 0).re
        rw [heval.1,heval.1]
        exact congrArg Complex.re heta
      · change (PhasePolynomial.actual (boundaryGramPolynomial m 1 0) _ /
          PhasePolynomial.actual (boundaryGramPolynomial m 0 0) _).im =
            (boundaryGram m Q 1 0 / boundaryGram m Q 0 0).im
        rw [heval.1,heval.1]
        exact congrArg Complex.im heta
  refine ⟨?_, (real_ratio_eval m i Q).trans hratio⟩
  rw [quotientRealDenominator, OpenBoundaryMPSDensityGenericity.normPolynomial_eval]
  apply Complex.normSq_pos.mpr
  rcases i with i | i | i
  · fin_cases i <;> simp [quotientRatioDenominator, coreRatioDenominators,
      columnPolynomial_eval, hdv.1.1.1.1, hdv.1.1.1.2]
  · fin_cases i <;> simp [quotientRatioDenominator, coreRatioDenominators,
      columnPolynomial_eval, hdv.1.1.1.1, hdv.1.1.1.2]
  · fin_cases i <;> simp [quotientRatioDenominator, heval.1, heval.2, hden, hnum]
/-- The refined polynomial chart is inhabited by an actual state at every complement length.
The witness is the original fixed-density tail witness, with its original full-length gauge. -/
theorem quotient_locus_witness (m : ℕ) :
    let ψ := mpsState (3 + m) (OpenBoundaryMPSTwoSiteMinimality.originalCore 0)
      (OpenBoundaryMPSTwoSiteMinimality.originalCore 1) ![1, 0] ![1, 2]
    ψ ∈ openBoundaryMPS (3 + m) ∧
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => rawPrefix 3 m ψ ij.1 ij.2)) (quotientLocusPolynomial m) ≠ 0 ∧
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (OpenBoundaryMPSDensityGenericity.fixedTensor (rawPrefix 3 m ψ)))
        OpenBoundaryMPSDensityGenericity.recoveryPolynomial ≠ 0 ∧
      boundaryGram m (rawPrefix 3 m ψ) 0 0 ≠ 0 := by
  dsimp only
  let θ := OpenBoundaryMPSTwoSiteMinimality.witnessParameter m
  let ψ := OpenBoundaryMPSTwoSiteMinimality.state (3 + m) θ
  let Q := rawPrefix 3 m ψ
  have hw := OpenBoundaryMPSTwoSiteMinimality.witness_gauge m
  have hg := OpenBoundaryMPSDensityGenericity.statePolynomial_witness m
  rw [OpenBoundaryMPSDensityGenericity.statePolynomial_eval, ← hw] at hg
  obtain ⟨_,hGram⟩ := canonical_gram m θ (OpenBoundaryMPSTwoSiteMinimality.right θ) hg
  have hq : OpenBoundaryMPSTwoSiteMinimality.right θ 0 ≠ 0 := by
    simp [θ, OpenBoundaryMPSTwoSiteMinimality.right,
      OpenBoundaryMPSTwoSiteMinimality.witnessParameter]
  change boundaryGram m Q = _ at hGram
  have h00 : boundaryGram m Q 0 0 ≠ 0 := by
    rw [hGram]
    exact mul_ne_zero hq (star_ne_zero.mpr hq)
  have hnum : gramNumerator m Q 0 0 ≠ 0 := by
    intro hz
    exact h00 (by change (gramDenominator m Q)⁻¹ * gramNumerator m Q 0 0 = 0; rw [hz,mul_zero])
  -- Keep the actual witness on the rational inverse path used by the chart.
  have hQ := (quotientLocus_eval m Q).mpr ⟨hg,hnum⟩
  obtain ⟨_, hrat, _, _, _, h00'⟩ := rational_quotient_inverse m Q hQ
  refine ⟨⟨_,_,_,_,rfl⟩, ?_⟩
  rw [← hw]
  exact ⟨hQ, hg, h00'⟩
#print axioms actual_boundary_gram
#print axioms actual_quotient_representative
#print axioms quotient_retraction
#print axioms quotient_locus_witness
#print axioms rational_quotient_inverse
end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
