/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity
   mirror-E: none(waiver:static-interior-recovery)
   anchors: []
   utility: none
   digest: One intrinsic polynomial locus for recovery at every interior three-site window. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSIntrinsicQ2Fiber
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore

/-! Raw, unnormalized observations of actual free-boundary uniform bond-two
states. The canonical reconstruction retains Haobo Ma and Wenlin Zhang's
CC BY 4.0 C8 attribution. Polynomial clearing, retraction and actual-image
density are reused from the quotient and Q2 suppliers. This is three-site
sufficiency only; interior two-site insufficiency and full C9 remain open. -/

noncomputable section
open Set Matrix MvPolynomial
open scoped BigOperators Matrix Topology ComplexOrder

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity

open PeriodicMPSParentIntersection (Bond Word TwoSiteSpanning)
open OpenBoundaryMPSMarginalBirationality
open OpenBoundaryMPSDensityRecovery
open OpenBoundaryMPSTwoSiteMinimality
open OpenBoundaryMPSQ2PolynomialFiber
open OpenBoundaryMPSIntrinsicQ2Fiber
open OpenBoundaryMPSInteriorCommonCore
open OpenBoundaryMPSQuotient hiding coreCoordinates
open OpenBoundaryMPSDensityGenericity
  (realCoeff imagCoeff coefficient_eval realCoordinates fixedTensor recoveryPolynomial
    recoveryPolynomial_ne_zero)

private def productMatrix (A : Fin 2 → Bond) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ab ij => (A ij.1 * A ij.2) ab.1 ab.2

private def boundaryMatrix (A : Fin 2 → Bond) (v : Fin 2 → ℂ) : Bond :=
  fun a i => (A i *ᵥ v) a

private def productPolynomial : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Poly :=
  fun ab ij => (corePolynomial ij.1 * corePolynomial ij.2) ab.1 ab.2

private def boundaryPolynomial : Matrix (Fin 2) (Fin 2) Poly :=
  fun a i => (corePolynomial i *ᵥ ![1, etaVariable]) a

private def normSquare (p : Poly) : RealPoly := realCoeff p ^ 2 + imagCoeff p ^ 2

private def conditionsPolynomial : RealPoly :=
  normSquare productPolynomial.det * normSquare (corePolynomial 0).det *
    normSquare boundaryPolynomial.det

private lemma normSquare_eval (p : Poly) (x : Coordinates) :
    eval x (normSquare p) = Complex.normSq (evaluate x p) := by
  simp only [normSquare, map_add, map_pow, Complex.normSq_apply]
  rw [(coefficient_eval p x).1, (coefficient_eval p x).2]
  ring

private lemma product_eval (x : Coordinates) :
    (evaluate x).mapMatrix productPolynomial =
      productMatrix (core (positiveRepresentative x)) := by
  ext ab ij
  exact congrFun (congrFun (by
    rw [map_mul, evaluate_core, evaluate_core] :
      (evaluate x).mapMatrix (corePolynomial ij.1 * corePolynomial ij.2) =
        core (positiveRepresentative x) ij.1 * core (positiveRepresentative x) ij.2)
    ab.1) ab.2

private lemma boundary_eval (x : Coordinates) :
    (evaluate x).mapMatrix boundaryPolynomial =
      boundaryMatrix (core (positiveRepresentative x)) ![1, eta x] := by
  ext a i
  change evaluate x ((corePolynomial i *ᵥ ![1, etaVariable]) a) = _
  rw [RingHom.map_mulVec]
  change ((evaluate x).mapMatrix (corePolynomial i) *ᵥ _ ) a = _
  rw [evaluate_core]
  have he : evaluate x ∘ ![1, etaVariable] = (![1, eta x] : Fin 2 → ℂ) := by
    ext j
    fin_cases j <;> simp [evaluate_eta]
  rw [he]
  rfl

private lemma conditions_eval (x : Coordinates) :
    eval x conditionsPolynomial =
      Complex.normSq (productMatrix (core (positiveRepresentative x))).det *
      Complex.normSq (core (positiveRepresentative x) 0).det *
      Complex.normSq (boundaryMatrix (core (positiveRepresentative x)) ![1, eta x]).det := by
  simp only [conditionsPolynomial, map_mul, normSquare_eval]
  rw [RingHom.map_det, product_eval, RingHom.map_det, evaluate_core,
    RingHom.map_det, boundary_eval]

private lemma spanning_of_det (A : Fin 2 → Bond) (h : (productMatrix A).det ≠ 0) :
    TwoSiteSpanning A := by
  classical
  have hu := (Matrix.isUnit_iff_isUnit_det (productMatrix A)).mpr
    (isUnit_iff_ne_zero.mpr h)
  apply Submodule.eq_top_iff'.mpr
  intro M
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) (fun ab => M ab.1 ab.2)
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨c, ?_⟩
  ext a b
  simpa [Matrix.mulVec, dotProduct, productMatrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm]
    using congrFun hc (a, b)

private lemma left_seed (θ : Parameter) :
    dualTransfer (core θ) (vecMulVec (star (left θ)) (left θ)) = 1 := by
  have hrows (i : Fin 2) : left θ ᵥ* core θ i = Pi.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [left, core, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  simp only [dualTransfer, mul_vecMulVec, vecMulVec_mul, ← star_vecMul,
    hrows, Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec]

private lemma right_seed (x : Coordinates) (hx : 0 < sigma x)
    (hv : (boundaryMatrix (core (positiveRepresentative x)) ![1, eta x]).det ≠ 0) :
    (transfer (core (positiveRepresentative x))
      (vecMulVec (right (positiveRepresentative x))
        (star (right (positiveRepresentative x))))).PosDef := by
  let A := core (positiveRepresentative x)
  let r := right (positiveRepresentative x)
  let W := boundaryMatrix A r
  have hr : r = (Real.sqrt (sigma x) : ℂ) • ![1, eta x] := by
    ext i
    fin_cases i <;> simp [r, right, positiveRepresentative]
  have hW : W = (Real.sqrt (sigma x) : ℂ) • boundaryMatrix A ![1, eta x] := by
    ext a i
    simp only [W, boundaryMatrix, hr, Matrix.mulVec_smul, Pi.smul_apply, Matrix.smul_apply]
  have hu : IsUnit W := by
    apply (Matrix.isUnit_iff_isUnit_det W).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [hW, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr hx)))) hv
  convert Matrix.PosDef.mul_conjTranspose_self W (Matrix.vecMul_injective_of_isUnit hu) using 1
  ext i j
  simp only [transfer, mul_vecMulVec, vecMulVec_mul, ← star_mulVec,
    Matrix.sum_apply, vecMulVec_apply, mul_apply, conjTranspose_apply, Pi.star_apply,
    W, boundaryMatrix]
  rfl

private lemma positive_steps (A : Fin 2 → Bond) (hu : IsUnit (A 0))
    (X : Bond) (hX : X.PosDef) :
    (dualTransfer A X).PosDef ∧ (transfer A X).PosDef := by
  constructor
  · rw [dualTransfer, Fin.sum_univ_two]
    exact (hX.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)).add_posSemidef
      (hX.posSemidef.conjTranspose_mul_mul_same (A 1))
  · rw [transfer, Fin.sum_univ_two]
    exact (hX.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)).add_posSemidef
      (hX.posSemidef.mul_mul_conjTranspose_same (A 1))

lemma positive_iterates (x : Coordinates) (hx : 0 < sigma x)
    (h0 : (core (positiveRepresentative x) 0).det ≠ 0)
    (hv : (boundaryMatrix (core (positiveRepresentative x)) ![1, eta x]).det ≠ 0) :
    ∀ k : ℕ, 1 ≤ k →
      ((dualTransfer (core (positiveRepresentative x)))^[k]
        (vecMulVec (star (left (positiveRepresentative x)))
          (left (positiveRepresentative x)))).PosDef ∧
      ((transfer (core (positiveRepresentative x)))^[k]
        (vecMulVec (right (positiveRepresentative x))
          (star (right (positiveRepresentative x))))).PosDef := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h0)
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction j with
  | zero =>
    simp only [zero_add, Function.iterate_one]
    exact ⟨by rw [left_seed]; exact Matrix.PosDef.one, right_seed x hx hv⟩
  | succ j ih =>
    constructor
    · rw [Function.iterate_succ_apply']
      exact (positive_steps _ hu _ ih.1).1
    · rw [Function.iterate_succ_apply']
      exact (positive_steps _ hu _ ih.2).2

private lemma witness_conditions (m : ℕ) :
    eval (coordinatesOf (witnessParameter m)) conditionsPolynomial ≠ 0 := by
  rw [conditions_eval, positiveRepresentative_witness]
  have he : eta (coordinatesOf (witnessParameter m)) = (17 / 5 : ℂ) := by
    change (⟨_, _⟩ : ℂ) = _
    have hz : (witnessParameter m).2.2 / ((witnessParameter m).2.1 : ℂ) = 17 / 5 := by
      simp only [witnessParameter, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
      field_simp
    exact hz
  rw [he]
  have hs : (productMatrix (core (witnessParameter m))).det = 64 := by
    let e : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv
    have hmat : Matrix.reindex e e (productMatrix (core (witnessParameter m))) =
        (!![3, -5/4, 15/2, -11/4;
            5/4, 11/2, 11/4, 13;
            10, -17/4, 53/2, -39/4;
            17/4, 37/2, 39/4, 46] : Matrix (Fin 4) (Fin 4) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [e, Matrix.reindex, finProdFinEquiv, Fin.divNat, Fin.modNat,
          productMatrix, core, witnessParameter, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← Matrix.det_reindex_self e, hmat, Matrix.det_succ_row_zero]
    norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  have h0 : (core (witnessParameter m) 0).det = -1 / 2 := by
    norm_num [core, witnessParameter, Matrix.det_fin_two]
  have hv : (boundaryMatrix (core (witnessParameter m)) ![1, (17 / 5 : ℂ)]).det = 72 / 25 := by
    norm_num [boundaryMatrix, core, witnessParameter, Matrix.det_fin_two,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hs, h0, hv]
  norm_num [Complex.normSq_apply]

private lemma actual_core_injective (m : ℕ) (ψ : Word (3 + m) → ℂ)
    (hψ : ψ ∈ openBoundaryMPS (3 + m))
    (hρ : eval (realCoordinates (fun ij => rawPrefix 3 m ψ ij.1 ij.2))
      (quotientLocusPolynomial m) ≠ 0)
    (hp : 0 < (quotientCoordinates m (rawPrefix 3 m ψ)).2.1) :
    Function.Injective (transfer (core (positiveRepresentative
      (quotientCoordinates13 (quotientCoordinates m (rawPrefix 3 m ψ)))))) := by
  let Q := rawPrefix 3 m ψ
  let t := fixedTensor Q
  have hg := ((quotientLocus_eval m Q).mp hρ).1
  obtain ⟨hc, hE⟩ := (recoveryPolynomial_ne_zero t).mp hg
  have ht : t ∈ openBoundaryMPS 3 := by
    obtain ⟨a₀, a₁, l, r, hs⟩ := hψ
    obtain ⟨g, hg'⟩ := observed_coherent m ![a₀, a₁] l r (Pi.single (fun _ => 0) 1)
    refine ⟨a₀, a₁, l, g, ?_⟩
    change rawPrefix 3 m (mpsState (3 + m) a₀ a₁ l r) *ᵥ Pi.single _ 1 =
      mpsState 3 a₀ a₁ l g at hg'
    rw [← hg', ← hs, Matrix.mulVec_single_one]
    rfl
  have hA := (canonical_shape t ht hc).2
  rw [quotientCoordinates_positiveRepresentative _ hp]
  exact hA ▸ hE

/-- Reindex a length-n' state to a propositionally equal length n. -/
def castState {n n' : ℕ} (h : n = n') (f : Word n' → ℂ) : Word n → ℂ :=
  fun w => f (fun i => w (Fin.cast h.symm i))

lemma cast_mps {n n' : ℕ} (h : n = n') (A B : Bond) (l r : Fin 2 → ℂ) :
    castState h (mpsState n' A B l r) = mpsState n A B l r := by
  subst n'
  rfl

private lemma cast_injective {n n' : ℕ} (h : n = n') : Function.Injective (castState h) := by
  subst n'
  exact fun _ _ h => h

lemma rawInterior_phase (p k q : ℕ) (f : Word ((p + k) + q) → ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) : rawInterior p k q (z • f) = rawInterior p k q f := by
  have hC : interiorColumns p k q (z • f) = z • interiorColumns p k q f := rfl
  have hn : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [rawInterior, hC, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  change (z * (starRingEnd ℂ) z) • _ = _
  rw [Complex.mul_conj, hn, Complex.ofReal_one, one_smul]
  rfl

lemma actual_phase (n : ℕ) (ψ : openBoundaryMPS n) (z : ℂ) :
    z • (ψ : Word n → ℂ) ∈ openBoundaryMPS n := by
  obtain ⟨a₀, a₁, l, r, hs⟩ := ψ.property
  refine ⟨a₀, a₁, z • l, r, ?_⟩
  rw [hs]
  funext w
  simp [mpsState]

lemma locus_phase (m : ℕ) (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ)
    (ψ : openBoundaryMPS (3 + m)) (z : ℂ) (hz : ‖z‖ = 1) :
    (⟨z • (ψ : Word (3 + m) → ℂ), actual_phase _ ψ z⟩ ∈ actualPrincipalLocus m R ↔
      ψ ∈ actualPrincipalLocus m R) := by
  have hn : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  change (eval _ R ≠ 0 ↔ eval _ R ≠ 0)
  rw [rawPrefix_scale_local, hn, Complex.ofReal_one, one_smul]

/-- A single observed principal locus at length 3+m serves every interior split.
The environments and representative are the actual canonical ones. -/
def intrinsicInteriorRecovery (m : ℕ) : Prop :=
  ∃ R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ, R ≠ 0 ∧
    (actualPrincipalLocus m R).Nonempty ∧ IsOpen (actualPrincipalLocus m R) ∧
    Dense (actualPrincipalLocus m R) ∧
    (∀ (ψ : openBoundaryMPS (3 + m)) (z : ℂ), ‖z‖ = 1 →
      ∃ hz : z • (ψ : Word (3 + m) → ℂ) ∈ openBoundaryMPS (3 + m),
        (⟨z • (ψ : Word (3 + m) → ℂ), hz⟩ ∈ actualPrincipalLocus m R ↔
          ψ ∈ actualPrincipalLocus m R)) ∧
    ∀ ψ : openBoundaryMPS (3 + m), ψ ∈ actualPrincipalLocus m R →
      let x := quotientCoordinates13 (quotientCoordinates m (rawPrefix 3 m ψ))
      let θ := positiveRepresentative x
      0 < sigma x ∧
      (∃ z : ℂ, ‖z‖ = 1 ∧ (ψ : Word (3 + m) → ℂ) = z • state (3 + m) θ) ∧
      TwoSiteSpanning (core θ) ∧ Function.Injective (transfer (core θ)) ∧
      (∀ k : ℕ, 1 ≤ k →
        ((dualTransfer (core θ))^[k] (vecMulVec (star (left θ)) (left θ))).PosDef ∧
        ((transfer (core θ))^[k] (vecMulVec (right θ) (star (right θ)))).PosDef) ∧
      ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → p + q = m →
        ∀ h : ((p + 3) + q) = 3 + m, ∀ φ : openBoundaryMPS (3 + m),
          rawInterior p 3 q (castState h φ) = rawInterior p 3 q (castState h ψ) ↔
            ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)

set_option maxHeartbeats 1200000 in
/-- Intrinsic generic sufficiency of every interior three-site window, with
arbitrary actual competitors and one polynomial for all splits at each length. -/
theorem intrinsic_interior_recovery (m : ℕ) (hm : 2 ≤ m) : intrinsicInteriorRecovery m := by
  obtain ⟨H, B, hclear⟩ := clear_polynomial conditionsPolynomial
    (fun j => quotientRealNumerator m (quotientIndexEquiv.symm j))
    (fun j => quotientRealDenominator m (quotientIndexEquiv.symm j))
  let x₀ := coordinatesOf (witnessParameter m)
  let Q₀ := quotientRawPrefix m x₀
  let y₀ := realCoordinates (fun ij : ObsIndex => Q₀ ij.1 ij.2)
  have hρ₀ : eval y₀ (quotientLocusPolynomial m) ≠ 0 := by
    have hw := (quotient_locus_witness m).2.1
    simpa [y₀, Q₀, quotientRawPrefix, x₀, positiveRepresentative_witness,
      witness_gauge] using hw
  have hσ₀ : 0 < sigma x₀ := by
    dsimp [x₀, sigma, coordinatesOf, witnessParameter]
    positivity
  have hrat₀ : (fun j => eval y₀ (quotientRealNumerator m (quotientIndexEquiv.symm j)) /
      eval y₀ (quotientRealDenominator m (quotientIndexEquiv.symm j))) = x₀ := by
    rw [funext (quotientCoordinate_ratio m Q₀ hρ₀)]
    exact quotientCoordinates_retraction_local m x₀ hσ₀ hρ₀
  have hcx := hclear y₀ (quotient_denominators_nonzero m Q₀ hρ₀)
  rw [hrat₀] at hcx
  have hH₀ : eval y₀ H ≠ 0 := by
    intro hh
    apply witness_conditions m
    simpa [hh] using hcx.2
  let R := quotientLocusPolynomial m * H
  have hR₀ : eval y₀ R ≠ 0 := by simpa [R] using mul_ne_zero hρ₀ hH₀
  have hR : R ≠ 0 := by
    intro hh
    simp [hh] at hR₀
  let ψ₀ : openBoundaryMPS (3 + m) :=
    ⟨state (3 + m) (positiveRepresentative x₀),
      ⟨_, _, _, _, rfl⟩⟩
  have hgeneric := actual_principal_genericity m R ⟨ψ₀, hR₀⟩
  refine ⟨R, hR, hgeneric.1, hgeneric.2.1, hgeneric.2.2, ?_, ?_⟩
  · intro ψ z hz
    exact ⟨actual_phase _ ψ z, locus_phase m R ψ z hz⟩
  · intro ψ hψ
    let Q := rawPrefix 3 m (ψ : Word (3 + m) → ℂ)
    let y := realCoordinates (fun ij : ObsIndex => Q ij.1 ij.2)
    let pθ := quotientCoordinates m Q
    let x := quotientCoordinates13 pθ
    let θ := positiveRepresentative x
    have hparts : eval y (quotientLocusPolynomial m) ≠ 0 ∧ eval y H ≠ 0 := by
      simpa only [actualPrincipalLocus, Set.mem_ofPred_eq, R, map_mul, mul_ne_zero_iff]
        using hψ
    have hρ := hparts.1
    have hg := ((quotientLocus_eval m Q).mp hρ).1
    have h00 := (rational_quotient_inverse m Q hρ).2.2.2.2.2
    obtain ⟨hp, z₀, hz₀, hrep₀⟩ := actual_quotient_representative m ψ ψ.property hg h00
    have hσ : 0 < sigma x := by
      change 0 < quotientRealCoordinates pθ (quotientIndexEquiv.symm 10)
      have hi : quotientIndexEquiv.symm 10 = Sum.inr (Sum.inr 0) := by decide
      simpa [hi, quotientRealCoordinates] using hp
    have hθ := quotientCoordinates_positiveRepresentative pθ hp
    have hrep : (ψ : Word (3 + m) → ℂ) = z₀ • state (3 + m) θ := by
      dsimp [θ, x]
      rw [hθ]
      exact hrep₀
    have hrat : (fun j => eval y (quotientRealNumerator m (quotientIndexEquiv.symm j)) /
        eval y (quotientRealDenominator m (quotientIndexEquiv.symm j))) = x :=
      funext (quotientCoordinate_ratio m Q hρ)
    have hcx := hclear y (quotient_denominators_nonzero m Q hρ)
    rw [hrat] at hcx
    have hK : eval x conditionsPolynomial ≠ 0 := by
      rw [hcx.2]
      exact div_ne_zero hparts.2 hcx.1
    rw [conditions_eval, mul_ne_zero_iff, mul_ne_zero_iff] at hK
    have hS := (not_congr Complex.normSq_eq_zero).mp hK.1.1
    have hA0 := (not_congr Complex.normSq_eq_zero).mp hK.1.2
    have hV := (not_congr Complex.normSq_eq_zero).mp hK.2
    have hspan := spanning_of_det (core θ) hS
    have hE := actual_core_injective m ψ ψ.property hρ hp
    have hpos := positive_iterates x hσ hA0 hV
    refine ⟨hσ, ⟨z₀, hz₀, hrep⟩, hspan, hE, hpos, ?_⟩
    intro p q hp' hq' hpq h φ
    constructor
    · intro hraw
      obtain ⟨b₀, b₁, l', r', hφ⟩ := φ.property
      have hraw' : rawInterior p 3 q (mpsState ((p + 3) + q) b₀ b₁ l' r') =
          rawInterior p 3 q (mpsState ((p + 3) + q) (core θ 0) (core θ 1) (left θ) (right θ)) := by
        rw [← cast_mps h]
        rw [← hφ]
        rw [hraw, hrep]
        change rawInterior p 3 q (z₀ • castState h (state (3 + m) θ)) = _
        rw [rawInterior_phase _ _ _ _ _ hz₀]
        rw [state, cast_mps]
      obtain ⟨z₁, hz₁, he⟩ := interior_phase_recovery (core θ) ![b₀, b₁]
        (left θ) (right θ) l' r' p q hp' hq' hspan hE (hpos p hp').1 (hpos q hq').2 hraw'
      have hz₀ne : z₀ ≠ 0 := by intro hz; simp [hz] at hz₀
      refine ⟨z₁ / z₀, by simp [hz₁, hz₀], ?_⟩
      apply cast_injective h
      change castState h φ = (z₁ / z₀) • castState h ψ
      rw [hφ, cast_mps, hrep]
      change mpsState ((p + 3) + q) b₀ b₁ l' r' =
        (z₁ / z₀) • (z₀ • castState h (state (3 + m) θ))
      rw [smul_smul, div_mul_cancel₀ _ hz₀ne, state, cast_mps]
      exact he
    · rintro ⟨z, hz, he⟩
      rw [he]
      change rawInterior p 3 q (z • castState h ψ) = _
      exact rawInterior_phase _ _ _ _ _ hz

#print axioms intrinsic_interior_recovery

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity
