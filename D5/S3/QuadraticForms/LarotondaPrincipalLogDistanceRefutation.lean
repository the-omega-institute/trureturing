/- GID: D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.claim; result=D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.result; claim=D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.claim
   digest: A trace-coupled quadratic norm refutes principal-log distance minimality on U(2). -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#26384; Refuted)
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6.

Escape audit unfinished for the two published norm identities: https://github.com/the-omega-institute/trureturing/issues/26905.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
All theorem proofs are bind-only. The definitions introduce the predicates and constructions used below.
The spectral norm in claim is the literal Matrix.toEuclideanCLM norm.
The curve length and distance use the formulas of issue #26384.
The two published norm identities are expanded in the dependency lists.

Direct frozen dependency identities:
  F1: D5/S3/Quantum/GNSMatrix.frobenius_norm_sq_eq_trace; D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace
    declaration statement_id: sha256:470140292aee89705512206af514f5a42fdc3948e5c9195d302613a47b859917
  F2: D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_left; D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left
    declaration statement_id: sha256:8a106b7c09f759560b1ae0469b6698029e4c2b0b2000528a314e20e06f5013ff
  F3: D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_right; D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right
    declaration statement_id: sha256:63c2cd1b86c23c2972e5bf796750663ea1953eea0946f6abb48832ba5fa201e7
  F4: D5/S3/Quantum/Matrix/CommutatorGap.opSq; D5.S3.Quantum.Matrix.CommutatorGap.opSq
    declaration statement_id: sha256:6d7fcaf97319bd2a70dda8acf0b09b70ad5080babdfe933d711e778bfa88abf3
  F5: D5/S3/Quantum/Matrix/CommutatorGap.opSq_le_frobSq; D5.S3.Quantum.Matrix.CommutatorGap.opSq_le_frobSq
    declaration statement_id: sha256:09c53e2375760ded38e0495bb2bdca6fdf88baad54be26e92b69cd347c5d72d8
  F6: D5/S3/Weil/ZetaLinear/PosIndex.frobSq; RHLinalg.frobSq
    declaration statement_id: sha256:87344d8035a8c18278b7631968fd9b17dbe3a4221dfb10f55432779f1064e116

Declaration classifications and consumers:
  IsAdInvariantFinsler: proof_shape: bind-only; escape_witness: none;
    consumers: claim, quadNorm_admissible; Direct frozen dependencies: none.
  PiecewiseSmooth: proof_shape: bind-only; escape_witness: none;
    consumers: IsCurve, expCurve_isCurve; Direct frozen dependencies: none.
  IsCurve: proof_shape: bind-only; escape_witness: none;
    consumers: rectifiableDistance, expCurve_isCurve, distance_le_expCurve; Direct frozen dependencies: none.
  curveLength: proof_shape: bind-only; escape_witness: none;
    consumers: rectifiableDistance, expCurve_length, distance_le_expCurve; Direct frozen dependencies: none.
  rectifiableDistance: proof_shape: bind-only; escape_witness: none;
    consumers: claim, distance_le_expCurve, result; Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: none.
  normCoords: proof_shape: bind-only; escape_witness: none;
    consumers: quadNorm, quadNorm_sq, quadNorm_admissible, witness_strict, result; Direct frozen dependencies: none.
  quadNorm: proof_shape: bind-only; escape_witness: none;
    consumers: quadNorm_sq, quadNorm_admissible, quadNorm_angle_sq, winding_gap, witness_strict, result; Direct frozen dependencies: none.
  quadNorm_sq: proof_shape: bind-only; escape_witness: none;
    consumers: quadNorm_admissible, quadNorm_angle_sq; Direct frozen dependencies: none.
  hsNorm_conj: proof_shape: bind-only; escape_witness: none;
    consumers: quadNorm_admissible; Direct frozen dependencies: F1, F2, F3, F6.
  spectral_le_hs: proof_shape: bind-only; escape_witness: none;
    consumers: quadNorm_admissible; Direct frozen dependencies: F1, F4, F5, F6.
  quadNorm_admissible: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: F1, F2, F3, F4, F5, F6.
  expCurve: proof_shape: bind-only; escape_witness: none;
    consumers: expCurve_smooth, expCurve_isCurve, expCurve_velocity, expCurve_length, distance_le_expCurve; Direct frozen dependencies: none.
  expCurve_smooth: proof_shape: bind-only; escape_witness: none;
    consumers: expCurve_isCurve; Direct frozen dependencies: none.
  expCurve_isCurve: proof_shape: bind-only; escape_witness: none;
    consumers: distance_le_expCurve; Direct frozen dependencies: none.
  expCurve_velocity: proof_shape: bind-only; escape_witness: none;
    consumers: expCurve_length; Direct frozen dependencies: none.
  expCurve_length: proof_shape: bind-only; escape_witness: none;
    consumers: distance_le_expCurve; Direct frozen dependencies: none.
  distance_le_expCurve: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: none.
  angleMatrix: proof_shape: bind-only; escape_witness: none;
    consumers: angleMatrix_skew, angleMatrix_winding, witness_endpoint, witness_spectral, quadNorm_angle_sq, winding_gap, witness_strict, result; Direct frozen dependencies: none.
  angleMatrix_skew: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: none.
  angleMatrix_winding: proof_shape: bind-only; escape_witness: none;
    consumers: witness_endpoint; Direct frozen dependencies: none.
  witnessAngles: proof_shape: bind-only; escape_witness: none;
    consumers: witness_endpoint, witness_spectral, witness_strict, result; Direct frozen dependencies: none.
  shiftedAngles: proof_shape: bind-only; escape_witness: none;
    consumers: witness_endpoint, witness_strict, result; Direct frozen dependencies: none.
  witness_endpoint: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: none.
  witness_spectral: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: none.
  quadNorm_angle_sq: proof_shape: bind-only; escape_witness: none;
    consumers: winding_gap; Direct frozen dependencies: none.
  winding_gap: proof_shape: bind-only; escape_witness: none;
    consumers: witness_strict; Direct frozen dependencies: none.
  witness_strict: proof_shape: bind-only; escape_witness: none;
    consumers: result; Direct frozen dependencies: none.
-/

import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Quantum.Matrix.CommutatorGap

/-! A diagonal winding shift gives a shorter curve for an Ad-invariant quadratic norm. -/

namespace D5.S3.QuadraticForms.LarotondaPrincipalLogDistanceRefutation

open scoped Matrix.Norms.L2Operator ENNReal ContDiff
open MeasureTheory



/-- A matrix-valued extension of a Finsler norm on the existing skew-adjoint
subspace. Its values outside that subspace impose no condition. Symmetry is
not required. The last clause is Section 4.1's normalization. -/
def IsAdInvariantFinsler {n : ℕ} (F : (Matrix (Fin n) (Fin n) ℂ) → ℝ) : Prop :=
  F 0 = 0 ∧
  (∀ z : (Matrix (Fin n) (Fin n) ℂ), z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) → 0 ≤ F z) ∧
  (∀ z : (Matrix (Fin n) (Fin n) ℂ), z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) → (F z = 0 ↔ z =
      0)) ∧
  (∀ x y : (Matrix (Fin n) (Fin n) ℂ), x ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) → y ∈
      skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) →
    F (x + y) ≤ F x + F y) ∧
  (∀ (r : ℝ) (z : (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ r → z ∈ skewAdjoint ((Matrix (Fin n) (Fin n)
      ℂ)) →
    F (r • z) = r * F z) ∧
  (∀ (u z : (Matrix (Fin n) (Fin n) ℂ)), u ∈ Matrix.unitaryGroup (Fin n) ℂ →
    z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) → F (u * z * star u) = F z) ∧
  (∀ z : (Matrix (Fin n) (Fin n) ℂ), z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) →
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) z‖ ≤ F z)

/-- A continuous curve with a finite partition into smooth closed pieces. -/
def PiecewiseSmooth {n : ℕ} (γ : ℝ → (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
  ∃ (m : ℕ) (τ : Fin (m + 1) → ℝ),
    τ 0 = 0 ∧ τ (Fin.last m) = 1 ∧ StrictMono τ ∧
    ∀ j : Fin m, ContDiffOn ℝ ∞ γ (Set.Icc (τ j.castSucc) (τ j.succ))

/-- Piecewise smooth curves from u to v, with values in the actual unitary group. -/
def IsCurve {n : ℕ} (u v : (Matrix (Fin n) (Fin n) ℂ)) (γ : ℝ → (Matrix (Fin n) (Fin n) ℂ)) : Prop
    :=
  PiecewiseSmooth γ ∧ γ 0 = u ∧ γ 1 = v ∧
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ t ∈ Matrix.unitaryGroup (Fin n) ℂ

/-- L(γ) = integral F(γ⁻¹ γ'). On a unitary matrix its inverse is its star.
The extended nonnegative integral retains infinite lengths. Values of deriv
at the finitely many partition points do not affect the integral. -/
noncomputable def curveLength {n : ℕ} (F : (Matrix (Fin n) (Fin n) ℂ) → ℝ) (γ : ℝ → (Matrix (Fin
    n) (Fin n) ℂ)) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1,
    ENNReal.ofReal (F (star (γ t) * deriv γ t))

/-- The infimum of lengths, from u to v; an empty competitor set has value ∞. -/
noncomputable def rectifiableDistance {n : ℕ} (F : (Matrix (Fin n) (Fin n) ℂ) → ℝ) (u v : (Matrix
    (Fin n) (Fin n) ℂ)) : ℝ≥0∞ :=
  sInf {L : ℝ≥0∞ | ∃ γ : ℝ → (Matrix (Fin n) (Fin n) ℂ), IsCurve u v γ ∧ L = curveLength F γ}

/-- The conjecture after Proposition 4.3, for every normalized Ad-invariant
Finsler norm on u(n), including nonsymmetric norms. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ F : (Matrix (Fin n) (Fin n) ℂ) → ℝ, IsAdInvariantFinsler F →
      ∀ z : (Matrix (Fin n) (Fin n) ℂ), z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) →
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) z‖ ≤ Real.pi →
        rectifiableDistance F 1 (NormedSpace.exp z) = ENNReal.ofReal (F z)


open D5.S3.Quantum.Matrix.CommutatorGap
open scoped Matrix Matrix.Norms.L2Operator ENNReal ContDiff
open MeasureTheory


private noncomputable def normCoords {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ)) :
    EuclideanSpace ℂ (Option (Fin n × Fin n)) :=
  WithLp.toLp 2 (fun k => match k with
    | none => 2 * Matrix.trace z
    | some (i,j) => z i j)

private noncomputable def quadNorm {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ)) : ℝ := ‖normCoords z‖

private theorem quadNorm_sq {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ)) :
    quadNorm z ^ 2 = (@norm (Matrix (Fin n) (Fin n) ℂ)
        Matrix.frobeniusSeminormedAddCommGroup.toNorm) z ^ 2 + 4 * ‖Matrix.trace z‖ ^ 2 := by
  have hhs : (@norm (Matrix (Fin n) (Fin n) ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) z ^
      2 = ∑ i, ∑ j, ‖z i j‖ ^ 2 :=
    rectNorm_sq z
  rw [quadNorm, EuclideanSpace.norm_sq_eq]
  simp [normCoords, Fintype.sum_option, Fintype.sum_prod_type, hhs]
  ring

open scoped Matrix.Norms.Frobenius in
private theorem hsNorm_conj {n : ℕ} (u z : (Matrix (Fin n) (Fin n) ℂ))
    (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (@norm (Matrix (Fin n) (Fin n) ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) (u * z * star
        u) = (@norm (Matrix (Fin n) (Fin n) ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm) z :=
        by
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨u, hu⟩
  have hf := D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right (u*z) (star U)
  have hl := D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left z U
  have h := hf.trans hl
  rw [← rectNorm_sq_square,
    ← rectNorm_sq_square] at h
  change (@norm (Matrix (Fin n) (Fin n) ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm)
      (u*z*star u) ^ 2 = (@norm (Matrix (Fin n) (Fin n) ℂ)
      Matrix.frobeniusSeminormedAddCommGroup.toNorm) z ^ 2 at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

open scoped Matrix.Norms.Frobenius in
private theorem spectral_le_hs {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ)) : ‖Matrix.toEuclideanCLM
    (n := Fin n) (𝕜 := ℂ) z‖ ≤ (@norm (Matrix (Fin n) (Fin n) ℂ)
    Matrix.frobeniusSeminormedAddCommGroup.toNorm) z := by
  have h := D5.S3.Quantum.Matrix.CommutatorGap.opSq_le_frobSq z
  rw [← rectNorm_sq_square] at h
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) z‖ ^ 2 ≤ (@norm (Matrix (Fin n) (Fin n) ℂ)
      Matrix.frobeniusSeminormedAddCommGroup.toNorm) z ^ 2 at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg z)).mp h

open scoped Matrix.Norms.Frobenius in
private theorem quadNorm_admissible {n : ℕ} :
    IsAdInvariantFinsler (quadNorm : (Matrix (Fin n) (Fin n) ℂ) → ℝ) := by
  have hz0 : normCoords (0 : (Matrix (Fin n) (Fin n) ℂ)) = 0 := by
    ext k
    cases k <;> simp [normCoords]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [quadNorm, hz0, norm_zero]
  · intro z hz
    exact norm_nonneg _
  · intro z hz
    constructor
    · intro h
      have hc : normCoords z = 0 := norm_eq_zero.mp h
      ext i j
      have he := congrArg (fun v : EuclideanSpace ℂ (Option (Fin n × Fin n)) => v (some (i,j))) hc
      simpa [normCoords] using he
    · intro h
      subst z
      simp only [quadNorm, hz0, norm_zero]
  · intro x y hx hy
    have hadd : normCoords (x+y) = normCoords x + normCoords y := by
      ext k
      cases k with
      | none => simp [normCoords, Matrix.trace_add, mul_add]
      | some ij => simp [normCoords]
    simpa only [quadNorm, hadd] using norm_add_le (normCoords x) (normCoords y)
  · intro r z hr hz
    have hs : normCoords (r • z) = r • normCoords z := by
      ext k
      cases k with
      | none => simp [normCoords, Matrix.trace_smul, mul_left_comm]
      | some ij => simp [normCoords]
    simp only [quadNorm, hs, norm_smul, Real.norm_of_nonneg hr]
  · intro u z hu hz
    have ht : Matrix.trace (u * z * star u) = Matrix.trace z := by
      rw [Matrix.trace_mul_cycle, (Unitary.mem_iff.mp hu).1, one_mul]
    have hq := quadNorm_sq (u*z*star u)
    rw [hsNorm_conj u z hu, ht, ← quadNorm_sq z] at hq
    have h0 : 0 ≤ quadNorm (u * z * star u) := norm_nonneg _
    have h1 : 0 ≤ quadNorm z := norm_nonneg _
    nlinarith
  · intro z hz
    refine (spectral_le_hs z).trans ?_
    have hq := quadNorm_sq z
    have h0 : 0 ≤ (@norm (Matrix (Fin n) (Fin n) ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm)
        z := norm_nonneg z
    have h1 : 0 ≤ quadNorm z := norm_nonneg _
    nlinarith [sq_nonneg ‖Matrix.trace z‖]


open scoped Matrix Matrix.Norms.L2Operator ENNReal ContDiff
open MeasureTheory

private noncomputable def expCurve {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ)) (t : ℝ) : (Matrix (Fin
    n) (Fin n) ℂ) :=
  NormedSpace.exp (t • z)

private theorem expCurve_smooth {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ)) :
    ContDiff ℝ ∞ (expCurve z) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (Matrix (Fin n) (Fin n) ℂ) → (Matrix (Fin n) (Fin n)
      ℂ)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact he.comp (contDiff_id.smul_const z)

private theorem expCurve_isCurve {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ))
    (hz : z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ))) :
    IsCurve 1 (NormedSpace.exp z) (expCurve z) := by
  let : NormedAlgebra ℚ ((Matrix (Fin n) (Fin n) ℂ)) := .restrictScalars ℚ ℂ ((Matrix (Fin n) (Fin
      n) ℂ))
  have hs := expCurve_smooth z
  refine ⟨⟨hs.continuous.continuousOn, 1, (fun i => (i.val : ℝ)), ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  · intro j
    exact hs.contDiffOn
  · simp [expCurve]
  · simp [expCurve]
  · intro t ht
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hz)

private theorem expCurve_velocity {n : ℕ} (z : (Matrix (Fin n) (Fin n) ℂ))
    (hz : z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ))) (t : ℝ) :
    star (expCurve z t) * deriv (expCurve z) t = z := by
  let : NormedAlgebra ℚ ((Matrix (Fin n) (Fin n) ℂ)) := .restrictScalars ℚ ℂ ((Matrix (Fin n) (Fin
      n) ℂ))
  have hd : deriv (expCurve z) t = expCurve z t * z :=
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) z t).deriv
  have hu : expCurve z t ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hz)
  rw [hd, ← mul_assoc, (Unitary.mem_iff.mp hu).1, one_mul]

private theorem expCurve_length {n : ℕ} (F : (Matrix (Fin n) (Fin n) ℂ) → ℝ) (z : (Matrix (Fin n)
    (Fin n) ℂ))
    (hz : z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ))) :
    curveLength F (expCurve z) = ENNReal.ofReal (F z) := by
  simp only [curveLength, expCurve_velocity z hz]
  simp [MeasureTheory.lintegral_const, Real.volume_Icc]

private theorem distance_le_expCurve {n : ℕ} (F : (Matrix (Fin n) (Fin n) ℂ) → ℝ) (z : (Matrix
    (Fin n) (Fin n) ℂ))
    (hz : z ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ))) :
    rectifiableDistance F 1 (NormedSpace.exp z) ≤ ENNReal.ofReal (F z) := by
  apply sInf_le
  exact ⟨expCurve z, expCurve_isCurve z hz, (expCurve_length F z hz).symm⟩


open scoped Matrix Matrix.Norms.L2Operator ENNReal ContDiff
open MeasureTheory

private noncomputable def angleMatrix {n : ℕ} (θ : Fin n → ℝ) : (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.diagonal (fun j => (θ j : ℂ) * Complex.I)

private theorem angleMatrix_skew {n : ℕ} (θ : Fin n → ℝ) :
    angleMatrix θ ∈ skewAdjoint ((Matrix (Fin n) (Fin n) ℂ)) := by
  rw [skewAdjoint.mem_iff]
  ext i j
  by_cases h : i = j
  · subst j
    simp [angleMatrix]
  · simp [angleMatrix, h, Ne.symm h]

private theorem angleMatrix_winding {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) :
    NormedSpace.exp (angleMatrix (fun i => θ i - if i = j then 2*Real.pi else 0)) =
      NormedSpace.exp (angleMatrix θ) := by
  simp only [angleMatrix, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  by_cases hi : i = j
  · simp only [hi, ite_eq_left, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [sub_mul]
    exact Complex.exp_periodic.sub_eq _
  · simp [hi]

private noncomputable def witnessAngles : Fin 2 → ℝ :=
  ![(4/5 : ℝ)*Real.pi, (1/2 : ℝ)*Real.pi]
private noncomputable def shiftedAngles : Fin 2 → ℝ :=
  ![(-6/5 : ℝ)*Real.pi, (1/2 : ℝ)*Real.pi]

private theorem witness_endpoint :
    NormedSpace.exp (angleMatrix shiftedAngles) =
      NormedSpace.exp (angleMatrix witnessAngles) := by
  have h := angleMatrix_winding witnessAngles 0
  have hθ : (fun i => witnessAngles i - if i = 0 then 2*Real.pi else 0) = shiftedAngles := by
    funext i
    fin_cases i <;> simp [witnessAngles, shiftedAngles]; ring
  rwa [hθ] at h

private theorem witness_spectral : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (angleMatrix
    witnessAngles)‖ ≤ Real.pi := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, angleMatrix, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
  intro i
  fin_cases i <;> simp [witnessAngles, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] <;> nlinarith [Real.pi_pos]

open scoped Matrix.Norms.Frobenius in
private theorem quadNorm_angle_sq {n : ℕ} (θ : Fin n → ℝ) :
    quadNorm (angleMatrix θ) ^ 2 =
      (∑ i, θ i ^ 2) + 4 * (∑ i, θ i) ^ 2 := by
  have hh : (@norm (Matrix (Fin n) (Fin n) ℂ) Matrix.frobeniusSeminormedAddCommGroup.toNorm)
      (angleMatrix θ) ^ 2 = ∑ i, θ i ^ 2 := by
    change ‖angleMatrix θ‖ ^ 2 = _
    rw [angleMatrix, Matrix.frobenius_norm_diagonal]
    simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  have ht : Matrix.trace (angleMatrix θ) = ((∑ i, θ i : ℝ) : ℂ) * Complex.I := by
    simp [angleMatrix, Matrix.trace_diagonal, Finset.sum_mul]
  rw [quadNorm_sq, hh, ht]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem winding_gap (a b : ℝ) :
    quadNorm (angleMatrix ![a-2*Real.pi,b]) ^ 2 -
      quadNorm (angleMatrix ![a,b]) ^ 2 =
        4*Real.pi*((Real.pi-a)+4*(Real.pi-(a+b))) := by
  simp only [quadNorm_angle_sq, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

private theorem witness_strict :
    quadNorm (angleMatrix shiftedAngles) < quadNorm (angleMatrix witnessAngles) := by
  have h := winding_gap ((4/5 : ℝ)*Real.pi) ((1/2 : ℝ)*Real.pi)
  have he : ((4/5 : ℝ)*Real.pi - 2*Real.pi) = (-6/5 : ℝ)*Real.pi := by ring
  rw [he] at h
  change quadNorm (angleMatrix shiftedAngles) ^ 2 -
    quadNorm (angleMatrix witnessAngles) ^ 2 = _ at h
  have hn0 : 0 ≤ quadNorm (angleMatrix shiftedAngles) := norm_nonneg _
  have hn1 : 0 ≤ quadNorm (angleMatrix witnessAngles) := norm_nonneg _
  nlinarith [sq_pos_of_pos Real.pi_pos]

theorem result : ¬ D5.S3.QuadraticForms.LarotondaPrincipalLogDistanceRefutation.claim := by
  intro h
  have hc := h 2 (by norm_num) quadNorm quadNorm_admissible
    (angleMatrix witnessAngles) (angleMatrix_skew witnessAngles) witness_spectral
  have hd := distance_le_expCurve quadNorm (angleMatrix shiftedAngles)
    (angleMatrix_skew shiftedAngles)
  rw [witness_endpoint, hc] at hd
  have hstrict : ENNReal.ofReal (quadNorm (angleMatrix shiftedAngles)) <
      ENNReal.ofReal (quadNorm (angleMatrix witnessAngles)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr witness_strict
  exact (not_lt_of_ge hd) hstrict


end D5.S3.QuadraticForms.LarotondaPrincipalLogDistanceRefutation
