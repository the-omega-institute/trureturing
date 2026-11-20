/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryRecordRate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryRecordRate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionOverlap]
   utility: none
   digest: The exact rate for a complementary record of a hidden label. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionOverlap
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section

variable {O E : Type*} [Fintype O] [Fintype E] [DecidableEq O] [DecidableEq E]

/-- The environment Gram matrix in the convention that rows label visible coordinates. -/
def environmentGram (W : Matrix O E ℂ) : Matrix E E ℂ := Wᴴ * W

/-- The literal complementary partial trace in the amplitude basis. -/
def environmentDensity (W : Matrix O E ℂ) : Matrix E E ℂ :=
  fun e f => ∑ i, W i e * star (W i f)

/-- A binary effect is the outcome that guesses label zero. -/
def IsEffect (P : Matrix E E ℂ) : Prop := P.PosSemidef ∧ (1 - P).PosSemidef

/-- The equiprobable binary error in Gram coordinates. -/
def fairError (W₀ W₁ : Matrix O E ℂ) (P : Matrix E E ℂ) : ℝ :=
  ((trace ((1 - P) * environmentGram W₀)).re +
    (trace (P * environmentGram W₁)).re) / 2

/-- The equiprobable binary error using the literal complementary partial traces. -/
def physicalError (W₀ W₁ : Matrix O E ℂ) (Q : Matrix E E ℂ) : ℝ :=
  ((trace ((1 - Q) * environmentDensity W₀)).re +
    (trace (Q * environmentDensity W₁)).re) / 2

omit [Fintype E] [DecidableEq O] [DecidableEq E] in
theorem environmentDensity_eq_transpose (W : Matrix O E ℂ) :
    environmentDensity W = (environmentGram W)ᵀ := by
  ext e f
  simp only [environmentDensity, environmentGram, transpose_apply, mul_apply,
    conjTranspose_apply, mul_comm]

omit [Fintype E] in
theorem isEffect_transpose_iff (P : Matrix E E ℂ) : IsEffect Pᵀ ↔ IsEffect P := by
  simp only [IsEffect, posSemidef_transpose_iff, ← transpose_one_sub]
where
  transpose_one_sub : (1 - P)ᵀ = 1 - Pᵀ := by simp

omit [DecidableEq O] in
theorem physicalError_transpose (W₀ W₁ : Matrix O E ℂ) (P : Matrix E E ℂ) :
    physicalError W₀ W₁ Pᵀ = fairError W₀ W₁ P := by
  have hp : (1 - P)ᵀ = 1 - Pᵀ := by simp
  simp only [physicalError, fairError, environmentDensity_eq_transpose, ← hp,
    ← transpose_mul, trace_transpose, trace_mul_comm (environmentGram W₀),
    trace_mul_comm (environmentGram W₁)]

/-- The support decoder in Gram coordinates. Its transpose acts on the physical environment. -/
def supportDecoder (W : Matrix O E ℂ) : Matrix E E ℂ :=
  Wᴴ * (W * Wᴴ)⁻¹ * W

omit [DecidableEq E] in
private theorem mul_supportDecoder (W : Matrix O E ℂ) (hR : (W * Wᴴ).PosDef) :
    W * supportDecoder W = W := by
  unfold supportDecoder
  rw [← Matrix.mul_assoc W (Wᴴ * _) W, ← Matrix.mul_assoc W Wᴴ,
    mul_nonsing_inv _ (((W * Wᴴ).isUnit_iff_isUnit_det).mp hR.isUnit), Matrix.one_mul]

/-- The decoder is an orthogonal projection onto the range of the environment Gram matrix. -/
theorem supportDecoder_projector (W : Matrix O E ℂ) (hR : (W * Wᴴ).PosDef) :
    IsEffect (supportDecoder W) ∧ supportDecoder W * supportDecoder W = supportDecoder W ∧
    Set.range (fun v => supportDecoder W *ᵥ v) =
      Set.range (fun v => environmentGram W *ᵥ v) := by
  have hP : (supportDecoder W).PosSemidef :=
    hR.inv.posSemidef.conjTranspose_mul_mul_same W
  have hPP : supportDecoder W * supportDecoder W = supportDecoder W := by
    change (Wᴴ * (W * Wᴴ)⁻¹ * W) * supportDecoder W = _
    rw [Matrix.mul_assoc, mul_supportDecoder W hR]
    rfl
  have hQ : (1 - supportDecoder W).PosSemidef := by
    have he : (1 - supportDecoder W)ᴴ * (1 - supportDecoder W) = 1 - supportDecoder W := by
      rw [conjTranspose_sub, conjTranspose_one, hP.isHermitian.eq, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
        Matrix.mul_one, hPP, sub_self, sub_zero]
    rw [← he]
    exact posSemidef_conjTranspose_mul_self _
  have hPE : supportDecoder W * environmentGram W = environmentGram W := by
    have he : environmentGram W * supportDecoder W = environmentGram W := by
      unfold environmentGram
      rw [Matrix.mul_assoc, mul_supportDecoder W hR]
    have hh := congrArg Matrix.conjTranspose he
    simpa only [conjTranspose_mul, hP.isHermitian.eq, environmentGram,
      conjTranspose_conjTranspose] using hh
  refine ⟨⟨hP, hQ⟩, hPP, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨(Wᴴ * (W * Wᴴ)⁻¹ * (W * Wᴴ)⁻¹ * W) *ᵥ v, ?_⟩
    change environmentGram W *ᵥ (_ *ᵥ v) = supportDecoder W *ᵥ v
    rw [mulVec_mulVec]
    congr 1
    calc
      _ = Wᴴ * ((W * Wᴴ) * (W * Wᴴ)⁻¹) * ((W * Wᴴ)⁻¹ * W) := by
        simp only [environmentGram, Matrix.mul_assoc]
      _ = supportDecoder W := by
        rw [mul_nonsing_inv _ (((W * Wᴴ).isUnit_iff_isUnit_det).mp hR.isUnit), Matrix.mul_one]
        simp only [supportDecoder, Matrix.mul_assoc]
  · rintro _ ⟨v, rfl⟩
    refine ⟨environmentGram W *ᵥ v, ?_⟩
    change supportDecoder W *ᵥ (environmentGram W *ᵥ v) = environmentGram W *ᵥ v
    rw [mulVec_mulVec, hPE]

/-- The support measurement has no label-zero error and has the stated exact fair error. -/
theorem supportDecoder_error (W₀ W₁ : Matrix O E ℂ) (hR : (W₀ * W₀ᴴ).PosDef) :
    (1 - supportDecoder W₀) * environmentGram W₀ = 0 ∧
    fairError W₀ W₁ (supportDecoder W₀) =
      (trace ((W₀ * W₀ᴴ)⁻¹ * (W₀ * W₁ᴴ) * (W₀ * W₁ᴴ)ᴴ)).re / 2 := by
  have hP := (supportDecoder_projector W₀ hR).1.1.isHermitian.eq
  have hEW : environmentGram W₀ * supportDecoder W₀ = environmentGram W₀ := by
    unfold environmentGram
    rw [Matrix.mul_assoc, mul_supportDecoder W₀ hR]
  have hWE : supportDecoder W₀ * environmentGram W₀ = environmentGram W₀ := by
    simpa only [conjTranspose_mul, hP, environmentGram, conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hEW
  have hzero : (1 - supportDecoder W₀) * environmentGram W₀ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hWE, sub_self]
  refine ⟨hzero, ?_⟩
  unfold fairError
  rw [hzero, trace_zero, Complex.zero_re, zero_add]
  congr 2
  unfold supportDecoder environmentGram
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using
    trace_mul_comm W₀ᴴ ((W₀ * W₀ᴴ)⁻¹ * (W₀ * (W₁ᴴ * W₁)))

omit [DecidableEq O] [DecidableEq E] in
private theorem gramPairing_nonneg (W : Matrix O E ℂ) {P : Matrix E E ℂ}
    (hP : P.PosSemidef) : 0 ≤ (trace (P * environmentGram W)).re := by
  rw [environmentGram, ← Matrix.mul_assoc, trace_mul_comm (P * Wᴴ), ← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (hP.mul_mul_conjTranspose_same W).trace_nonneg).1

omit [DecidableEq O] in
private theorem gramPairing_le_one (W : Matrix O E ℂ) (hW : trace (environmentGram W) = 1)
    {P : Matrix E E ℂ} (hP : IsEffect P) : (trace (P * environmentGram W)).re ≤ 1 := by
  have hn := gramPairing_nonneg W hP.2
  rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re, hW, Complex.one_re] at hn
  linarith

omit [DecidableEq O] [DecidableEq E] in
private theorem norm_trace_mul_adjoint_le (U V : Matrix O E ℂ) :
    ‖trace (U * Vᴴ)‖ ≤ Real.sqrt (trace (U * Uᴴ)).re * Real.sqrt (trace (V * Vᴴ)).re := by
  have hf (A : Matrix O E ℂ) :
      (trace (A * Aᴴ)).re = ∑ x : O × E, ‖A x.1 x.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum,
      Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  rw [hf, hf]
  have htrace : trace (U * Vᴴ) = ∑ x : O × E, U x.1 x.2 * star (V x.1 x.2) := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [htrace]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_star]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

omit [DecidableEq O] in
private theorem norm_weighted_trace_le (W₀ W₁ : Matrix O E ℂ) {P : Matrix E E ℂ}
    (hP : P.PosSemidef) :
    ‖trace (W₀ * P * W₁ᴴ)‖ ≤
      Real.sqrt (trace (P * environmentGram W₀)).re *
        Real.sqrt (trace (P * environmentGram W₁)).re := by
  let B := CFC.sqrt P
  have hB : Bᴴ = B := (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq
  have hBB : B * B = P := by
    simpa only [pow_two] using CFC.sq_sqrt P hP.nonneg
  have hprod (U V : Matrix O E ℂ) : (U * B) * (V * B)ᴴ = U * P * Vᴴ := by
    rw [conjTranspose_mul, hB, ← Matrix.mul_assoc, Matrix.mul_assoc U B B, hBB]
  have htrace (W : Matrix O E ℂ) : trace (W * P * Wᴴ) = trace (P * environmentGram W) := by
    rw [environmentGram, Matrix.mul_assoc W, trace_mul_comm W, Matrix.mul_assoc]
  simpa only [hprod, htrace] using norm_trace_mul_adjoint_le (W₀ * B) (W₁ * B)

omit [DecidableEq O] in
/-- Splitting the global overlap by the two effects bounds it by the square roots of
their two error probabilities. -/
theorem overlap_le_error_sqrt (W₀ W₁ : Matrix O E ℂ)
    (h₀ : trace (environmentGram W₀) = 1) (h₁ : trace (environmentGram W₁) = 1)
    {P : Matrix E E ℂ} (hP : IsEffect P) :
    ‖trace (W₀ * W₁ᴴ)‖ ≤ Real.sqrt (trace ((1 - P) * environmentGram W₀)).re +
      Real.sqrt (trace (P * environmentGram W₁)).re := by
  have hQ : IsEffect (1 - P) := ⟨hP.2, by simpa using hP.1⟩
  have hsum : trace (W₀ * W₁ᴴ) =
      trace (W₀ * (1 - P) * W₁ᴴ) + trace (W₀ * P * W₁ᴴ) := by
    rw [← trace_add, ← Matrix.add_mul, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
  have ha := norm_weighted_trace_le W₀ W₁ hQ.1
  have hb := norm_weighted_trace_le W₀ W₁ hP.1
  have hc := Real.sqrt_le_sqrt (gramPairing_le_one W₁ h₁ hQ)
  have hd := Real.sqrt_le_sqrt (gramPairing_le_one W₀ h₀ hP)
  rw [Real.sqrt_one] at hc hd
  rw [hsum]
  refine (norm_add_le _ _).trans (add_le_add (ha.trans ?_) (hb.trans ?_))
  · simpa using mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
  · simpa using mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)

omit [DecidableEq O] in
/-- Every binary effect obeys the same quadratic lower bound. -/
theorem fairError_lower (W₀ W₁ : Matrix O E ℂ)
    (h₀ : trace (environmentGram W₀) = 1) (h₁ : trace (environmentGram W₁) = 1)
    {P : Matrix E E ℂ} (hP : IsEffect P) :
    ‖trace (W₀ * W₁ᴴ)‖ ^ 2 / 4 ≤ fairError W₀ W₁ P := by
  have ha := Real.sq_sqrt (gramPairing_nonneg W₀ hP.2)
  have hb := Real.sq_sqrt (gramPairing_nonneg W₁ hP.1)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (overlap_le_error_sqrt W₀ W₁ h₀ h₁ hP) 2
  unfold fairError
  nlinarith [sq_nonneg (Real.sqrt (trace ((1 - P) * environmentGram W₀)).re -
    Real.sqrt (trace (P * environmentGram W₁)).re)]


open PeriodicMPSPrimitiveCollision
open PeriodicMPSParentIntersection (Word)
open PeriodicMPSProjectiveCoordinates (mass outer projector)
open PeriodicMPSUniformHardCoreMarginalWitness (Pair pairGram mass_eq_trace)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal)
open UniformMPSExpectedDimensionRefutation (traceWord)
open Filter
open scoped Topology

/-- The normalized actual periodic amplitudes, with sites zero and one as the row. -/
def collisionFlattening (b : Bool) (m : ℕ) : Matrix Pair (Word m) ℂ :=
  fun p w =>
    traceWord 2 2 (2 + m) (cores b) (Fin.append ![p.1, p.2] w) /
      (Real.sqrt (mass (traceWord 2 2 (2 + m) (cores b))) : ℂ)

private theorem normalized_mul_conj (x y : ℂ) (a b : ℝ) :
    (x / (a : ℂ)) * star (y / (b : ℂ)) = x * star y / ((a * b : ℝ) : ℂ) := by
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal, Complex.ofReal_mul,
    div_mul_div_comm]

private theorem collisionFlattening_gram (b c : Bool) (m : ℕ) (p q : Pair) :
    (collisionFlattening b m * (collisionFlattening c m)ᴴ) p q =
      (∑ w : Word m, traceWord 2 2 (2 + m) (cores b) (Fin.append ![p.1, p.2] w) *
        star (traceWord 2 2 (2 + m) (cores c) (Fin.append ![q.1, q.2] w))) /
      ((Real.sqrt (mass (traceWord 2 2 (2 + m) (cores b))) *
        Real.sqrt (mass (traceWord 2 2 (2 + m) (cores c)))) : ℝ) := by
  simp only [mul_apply, conjTranspose_apply, collisionFlattening, normalized_mul_conj,
    Finset.sum_div]

theorem collisionFlattening_cross (m : ℕ) :
    collisionFlattening false m * (collisionFlattening true m)ᴴ = collisionNormalizedCross m := by
  ext p q
  exact collisionFlattening_gram false true m p q

theorem collisionFlattening_visible (b : Bool) (m : ℕ) :
    collisionFlattening b m * (collisionFlattening b m)ᴴ = normalizedMarginal m (cores b) := by
  have hmass : 0 ≤ mass (traceWord 2 2 (2 + m) (cores b)) := by
    rw [collision_word_mass b (2 + m) (by omega)]
    cases b <;> positivity
  ext p q
  rw [collisionFlattening_gram, Real.mul_self_sqrt hmass]
  change pairGram (traceWord 2 2 (2 + m) (cores b)) p q / _ = _
  have htrace : mass (traceWord 2 2 (2 + m) (cores b)) =
      (pairGram (traceWord 2 2 (2 + m) (cores b))).trace.re :=
    mass_eq_trace (traceWord 2 2 (2 + m) (cores b))
  rw [htrace, normalizedMarginal]
  simp only [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

theorem collisionFlattening_common_visible (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    collisionFlattening b m * (collisionFlattening b m)ᴴ = collisionMarginal := by
  rw [collisionFlattening_visible]
  have h := (primitive_two_site_collision (2 + m) (by omega)).2.2.1 b
  rwa [show 2 + m - 2 = m by omega] at h

private theorem collisionFlattening_trace (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    trace (environmentGram (collisionFlattening b m)) = 1 := by
  rw [environmentGram, trace_mul_comm, collisionFlattening_common_visible b m hm]
  exact (primitive_two_site_collision (2 + m) (by omega)).2.2.2.2.1

/-- The literal complementary reduction is a density matrix. -/
theorem collision_environment_state (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    (environmentDensity (collisionFlattening b m)).PosSemidef ∧
    trace (environmentDensity (collisionFlattening b m)) = 1 := by
  rw [environmentDensity_eq_transpose, trace_transpose, posSemidef_transpose_iff]
  exact ⟨posSemidef_conjTranspose_mul_self _, collisionFlattening_trace b m hm⟩

theorem collisionFlattening_overlap (m : ℕ) :
    trace (collisionFlattening false m * (collisionFlattening true m)ᴴ) =
      collisionNormalizedOverlap (2 + m) := by
  let e : Pair × Word m ≃ Word (2 + m) :=
    (Equiv.prodCongr (finTwoArrowEquiv (Fin 2)).symm (Equiv.refl _)).trans (Fin.appendEquiv 2 m)
  unfold collisionNormalizedOverlap
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [trace, diag_apply, collisionFlattening_gram, ← Finset.sum_div]
  rfl

/-- The reduction on the last `m` qubits of the actual normalized periodic trace state. -/
theorem collision_environment_density (b : Bool) (m : ℕ) (w v : Word m) :
    environmentDensity (collisionFlattening b m) w v =
      ∑ p : Pair, projector (traceWord 2 2 (2 + m) (cores b))
        (Fin.append ![p.1, p.2] w) (Fin.append ![p.1, p.2] v) := by
  have hmass : 0 ≤ mass (traceWord 2 2 (2 + m) (cores b)) := by
    rw [collision_word_mass b (2 + m) (by omega)]
    cases b <;> positivity
  unfold environmentDensity
  apply Finset.sum_congr rfl
  intro p _
  rw [collisionFlattening, collisionFlattening, normalized_mul_conj, Real.mul_self_sqrt hmass]
  simp only [projector, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_inv, outer,
    Complex.star_def, div_eq_mul_inv]
  ring

/-- The physical measurement outcome that guesses label zero. -/
def collisionDecoder (m : ℕ) : Matrix (Word m) (Word m) ℂ :=
  (supportDecoder (collisionFlattening false m))ᵀ

/-- The literal complementary measurement on the primitive periodic MPS has zero
label-zero error and an exact trace formula for its equiprobable error. -/
theorem collisionDecoder_spec (m : ℕ) (hm : 5 ≤ m) :
    IsEffect (collisionDecoder m) ∧ collisionDecoder m * collisionDecoder m = collisionDecoder m ∧
    trace ((1 - collisionDecoder m) * environmentDensity (collisionFlattening false m)) = 0 ∧
    physicalError (collisionFlattening false m) (collisionFlattening true m) (collisionDecoder m) =
      (trace (collisionMarginal⁻¹ * collisionNormalizedCross m *
        (collisionNormalizedCross m)ᴴ)).re / 2 := by
  have hvisible := collisionFlattening_common_visible false m hm
  have hR : (collisionFlattening false m * (collisionFlattening false m)ᴴ).PosDef := by
    rw [hvisible]
    exact (primitive_two_site_collision (2 + m) (by omega)).2.2.2.1
  obtain ⟨hP, hsq, _⟩ := supportDecoder_projector (collisionFlattening false m) hR
  obtain ⟨hzero, herr⟩ :=
    supportDecoder_error (collisionFlattening false m) (collisionFlattening true m) hR
  have hsub : 1 - collisionDecoder m = (1 - supportDecoder (collisionFlattening false m))ᵀ := by
    simp [collisionDecoder]
  refine ⟨(isEffect_transpose_iff _).2 hP, ?_, ?_, ?_⟩
  · rw [collisionDecoder, ← transpose_mul, hsq]
  · rw [hsub, environmentDensity_eq_transpose, ← transpose_mul, trace_transpose,
      trace_mul_comm, hzero, trace_zero]
  · rw [collisionDecoder, physicalError_transpose, herr, hvisible, collisionFlattening_cross]

/-- Every physical complementary binary effect obeys the global-overlap lower bound. -/
theorem collisionError_lower (m : ℕ) (hm : 5 ≤ m) {Q : Matrix (Word m) (Word m) ℂ}
    (hQ : IsEffect Q) :
    ‖collisionNormalizedOverlap (2 + m)‖ ^ 2 / 4 ≤
      physicalError (collisionFlattening false m) (collisionFlattening true m) Q := by
  rw [← transpose_transpose Q, physicalError_transpose, ← collisionFlattening_overlap]
  exact fairError_lower _ _ (collisionFlattening_trace false m hm)
    (collisionFlattening_trace true m hm) ((isEffect_transpose_iff Q).2 hQ)


/-- The leading normalized mixed-transfer eigenvalue magnitude. -/
def collisionAlpha : ℝ := (3 + Real.sqrt 41) / 10

private theorem collisionAlpha_pos : 0 < collisionAlpha := by
  unfold collisionAlpha
  positivity

theorem collisionAlpha_lt_one : collisionAlpha < 1 := by
  have hs : Real.sqrt 41 < 7 :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  unfold collisionAlpha
  linarith

private theorem normalized_eigenvalue_le_alpha (p : Pair) :
    ‖collisionMixedEigenvalues p / (Real.sqrt 200 : ℂ)‖ ≤ collisionAlpha := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg collisionAlpha_pos.le (Real.sqrt_nonneg 200)),
    Complex.sq_norm, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)]
  have hs := Real.sqrt_nonneg 41
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · change Complex.normSq ((1 + Complex.I) * (3 + (Real.sqrt 41 : ℂ))) ≤ _
    unfold collisionAlpha
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    ring_nf
    linarith
  · change Complex.normSq ((1 + Complex.I) * (3 + -(Real.sqrt 41 : ℂ))) ≤ _
    unfold collisionAlpha
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.neg_re, Complex.neg_im]
    nlinarith
  · change Complex.normSq (8 * Complex.I) ≤ _
    unfold collisionAlpha
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    nlinarith
  · change Complex.normSq (-8 : ℂ) ≤ _
    unfold collisionAlpha
    norm_num [Complex.normSq_apply, Complex.neg_re, Complex.neg_im]
    nlinarith

/-- A length-independent bound on the sum of absolute spectral weights for one entry. -/
def collisionCrossCoefficient (p q : Pair) : ℝ :=
  (∑ k, ‖collisionCrossWeight p q k‖) / 200

private theorem collisionCrossCoefficient_nonneg (p q : Pair) : 0 ≤ collisionCrossCoefficient p q := by
  unfold collisionCrossCoefficient
  positivity

/-- The compiled spectral contraction gives an entrywise bound at the sharp base. -/
theorem collision_cross_sharp_bound (m : ℕ) (p q : Pair) :
    ‖collisionNormalizedCross m p q‖ ≤ collisionCrossCoefficient p q * collisionAlpha ^ m := by
  rw [collision_cross_contraction, norm_div]
  rw [show ‖(200 : ℂ)‖ = (200 : ℝ) by
    rw [← Complex.ofReal_ofNat, Complex.norm_real]
    norm_num]
  calc
    _ ≤ (∑ k, ‖collisionCrossWeight p q k‖ * collisionAlpha ^ m) / 200 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (normalized_eigenvalue_le_alpha k) _)
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold collisionCrossCoefficient; ring

/-- A uniform coefficient for the decoder error obtained by expanding the trace entrywise. -/
def collisionErrorCoefficient : ℝ :=
  (∑ p : Pair, ∑ q : Pair, ∑ k : Pair,
    ‖collisionMarginal⁻¹ p q‖ * collisionCrossCoefficient q k * collisionCrossCoefficient p k) / 2

private theorem collisionErrorCoefficient_nonneg : 0 ≤ collisionErrorCoefficient := by
  unfold collisionErrorCoefficient
  exact div_nonneg (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (norm_nonneg _) (collisionCrossCoefficient_nonneg q k))
        (collisionCrossCoefficient_nonneg p k)) (by norm_num)

/-- The explicit decoder has a uniform quadratic upper bound at the sharp spectral base. -/
theorem collisionDecoder_error_upper (m : ℕ) (hm : 5 ≤ m) :
    physicalError (collisionFlattening false m) (collisionFlattening true m) (collisionDecoder m)
      ≤ collisionErrorCoefficient * collisionAlpha ^ (2 * m) := by
  rw [(collisionDecoder_spec m hm).2.2.2]
  let S := collisionNormalizedCross m
  let H := collisionMarginal⁻¹
  have htrace : trace (H * S * Sᴴ) = ∑ p : Pair, ∑ k : Pair, ∑ q : Pair,
      H p q * S q k * star (S p k) := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Finset.sum_mul]
  change (trace (H * S * Sᴴ)).re / 2 ≤ _
  rw [htrace, collisionErrorCoefficient]
  have hn : 0 ≤ collisionAlpha ^ m := pow_nonneg collisionAlpha_pos.le _
  have hterm (p q k : Pair) :
      (H p q * S q k * star (S p k)).re ≤
        (‖H p q‖ * collisionCrossCoefficient q k * collisionCrossCoefficient p k) * collisionAlpha ^ (2 * m) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_star]
    calc
      _ ≤ ‖H p q‖ * (collisionCrossCoefficient q k * collisionAlpha ^ m) *
        (collisionCrossCoefficient p k * collisionAlpha ^ m) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (collision_cross_sharp_bound m q k) (norm_nonneg _))
            (collision_cross_sharp_bound m p k) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (mul_nonneg (collisionCrossCoefficient_nonneg _ _) hn))
      _ = _ := by
        rw [pow_mul, pow_two, mul_pow]
        ring
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Pair)) fun p _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Pair)) fun k _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset Pair)) fun q _ => hterm p q k
  simp only [Complex.re_sum] at *
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  simp only [Finset.sum_mul]
  exact hsum.trans_eq (Finset.sum_congr rfl fun p _ => Finset.sum_comm)


/-- Equiprobable error of the explicit support measurement, indexed by full ring length. -/
def collisionSupportError (n : ℕ) : ℝ :=
  physicalError (collisionFlattening false (n - 2)) (collisionFlattening true (n - 2))
    (collisionDecoder (n - 2))

/-- The optimal equiprobable error is the infimum over all physical binary effects on
the last `n - 2` qubits. -/
def collisionOptimalError (n : ℕ) : ℝ :=
  ⨅ Q : { Q : Matrix (Word (n - 2)) (Word (n - 2)) ℂ // IsEffect Q },
    physicalError (collisionFlattening false (n - 2)) (collisionFlattening true (n - 2)) Q.1

private theorem error_squeeze (n : ℕ) (hn : 7 ≤ n) :
    ‖collisionNormalizedOverlap n‖ ^ 2 / 4 ≤ collisionOptimalError n ∧
    collisionOptimalError n ≤ collisionSupportError n := by
  have hm : 5 ≤ n - 2 := by omega
  have hlen : 2 + (n - 2) = n := by omega
  let Q₀ : {Q : Matrix (Word (n - 2)) (Word (n - 2)) ℂ // IsEffect Q} :=
    ⟨collisionDecoder (n - 2), (collisionDecoder_spec (n - 2) hm).1⟩
  let : Nonempty {Q : Matrix (Word (n - 2)) (Word (n - 2)) ℂ // IsEffect Q} := ⟨Q₀⟩
  have hlo (Q : {Q : Matrix (Word (n - 2)) (Word (n - 2)) ℂ // IsEffect Q}) :
      ‖collisionNormalizedOverlap n‖ ^ 2 / 4 ≤
        physicalError (collisionFlattening false (n - 2)) (collisionFlattening true (n - 2)) Q.1 := by
    simpa only [hlen] using collisionError_lower (n - 2) hm Q.2
  refine ⟨le_ciInf hlo, ciInf_le ?_ Q₀⟩
  refine ⟨‖collisionNormalizedOverlap n‖ ^ 2 / 4, ?_⟩
  rintro _ ⟨Q, rfl⟩
  exact hlo Q

private theorem supportError_bound (n : ℕ) (hn : 7 ≤ n) :
    collisionSupportError n ≤
      ((collisionErrorCoefficient + 1) / collisionAlpha ^ 4) * (collisionAlpha ^ 2) ^ n := by
  have h := collisionDecoder_error_upper (n - 2) (by omega)
  refine h.trans ?_
  have hfactor : (collisionAlpha ^ 2) ^ n =
      collisionAlpha ^ (2 * (n - 2)) * collisionAlpha ^ 4 := by
    rw [← pow_add, ← pow_mul, show 2 * (n - 2) + 4 = 2 * n by omega]
  rw [hfactor, div_mul_eq_mul_div₀, ← mul_assoc,
    mul_div_cancel_right₀ _ (pow_ne_zero _ collisionAlpha_pos.ne')]
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg collisionAlpha_pos.le _)

private theorem lowerRoot_tendsto :
    Tendsto (fun n : ℕ => (‖collisionNormalizedOverlap n‖ ^ 2 / 4) ^ (1 / (n : ℝ)))
      atTop (𝓝 (collisionAlpha ^ 2)) := by
  have h := (collision_overlap_sharp_rate.pow 2).div
    ((tendsto_const_nhds (x := (4 : ℝ))).rpow
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) (Or.inl (by norm_num)))
      (by rw [Real.rpow_zero]; norm_num)
  rw [Real.rpow_zero, div_one] at h
  apply h.congr
  intro n
  dsimp
  have hn := norm_nonneg (collisionNormalizedOverlap n)
  rw [Real.div_rpow (pow_nonneg hn _) (by norm_num : (0 : ℝ) ≤ 4),
    ← Real.rpow_natCast_mul hn, ← Real.rpow_mul_natCast hn, mul_comm (1 / (n : ℝ))]

private theorem upperRoot_tendsto (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => (C * (collisionAlpha ^ 2) ^ n) ^ (1 / (n : ℝ)))
      atTop (𝓝 (collisionAlpha ^ 2)) := by
  have h := ((tendsto_const_nhds (x := C)).rpow
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) (Or.inl hC.ne')).mul_const (collisionAlpha ^ 2)
  rw [Real.rpow_zero, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hα : 0 ≤ collisionAlpha ^ 2 := sq_nonneg _
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.mul_rpow hC.le (pow_nonneg hα _), ← Real.rpow_natCast_mul hα,
    show (n : ℝ) * (1 / (n : ℝ)) = 1 by field_simp, Real.rpow_one]

private theorem collision_error_rate_of_bounds (f : ℕ → ℝ)
    (hf : ∀ n, 7 ≤ n → ‖collisionNormalizedOverlap n‖ ^ 2 / 4 ≤ f n ∧
      f n ≤ collisionSupportError n) :
    Tendsto (fun n : ℕ => f n ^ (1 / (n : ℝ))) atTop (𝓝 (collisionAlpha ^ 2)) := by
  have hC : 0 < (collisionErrorCoefficient + 1) / collisionAlpha ^ 4 :=
    div_pos (by linarith [collisionErrorCoefficient_nonneg]) (pow_pos collisionAlpha_pos _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowerRoot_tendsto
    (upperRoot_tendsto _ hC) ?_ ?_
  · filter_upwards [eventually_ge_atTop 7] with n hn
    exact Real.rpow_le_rpow (by positivity) (hf n hn).1 (by positivity)
  · filter_upwards [eventually_ge_atTop 7] with n hn
    exact Real.rpow_le_rpow ((by positivity : 0 ≤ ‖collisionNormalizedOverlap n‖ ^ 2 / 4).trans
      (hf n hn).1) ((hf n hn).2.trans (supportError_bound n hn)) (by positivity)

/-- The support measurement and the best possible complementary measurement have the
same exact nth-root error limit, with `n` the total number of qubits. -/
theorem collision_complementary_record_rate :
    Tendsto (fun n : ℕ => collisionSupportError n ^ (1 / (n : ℝ))) atTop
      (𝓝 (((3 + Real.sqrt 41) / 10) ^ 2)) ∧
    Tendsto (fun n : ℕ => collisionOptimalError n ^ (1 / (n : ℝ))) atTop
      (𝓝 (((3 + Real.sqrt 41) / 10) ^ 2)) := by
  refine ⟨collision_error_rate_of_bounds _ ?_, collision_error_rate_of_bounds _ ?_⟩
  · intro n hn
    obtain ⟨h₁, h₂⟩ := error_squeeze n hn
    exact ⟨h₁.trans h₂, le_rfl⟩
  · exact error_squeeze


/-- The explicit complementary measurement recovers the hidden label with vanishing error. -/
theorem collision_support_error_tendsto_zero :
    Tendsto collisionSupportError atTop (𝓝 0) := by
  have hα : collisionAlpha ^ 2 < 1 := by
    nlinarith [mul_pos collisionAlpha_pos (sub_pos.mpr collisionAlpha_lt_one)]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg collisionAlpha) hα).const_mul
    ((collisionErrorCoefficient + 1) / collisionAlpha ^ 4)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_ge_atTop 7] with n hn
    exact (div_nonneg (sq_nonneg _) (by norm_num)).trans
      ((error_squeeze n hn).1.trans (error_squeeze n hn).2)
  · exact (eventually_ge_atTop 7).mono fun n hn => supportError_bound n hn

end

end D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate

open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms supportDecoder_projector
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms supportDecoder_error
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms overlap_le_error_sqrt
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms fairError_lower
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collision_environment_state
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collision_environment_density
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collisionDecoder_spec
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collisionError_lower
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collisionDecoder_error_upper
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collision_complementary_record_rate
open D5.S3.Quantum.TensorNetworks.ComplementaryRecordRate in
#print axioms collision_support_error_tendsto_zero
