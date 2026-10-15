/- GID: D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every pure data qubit admits a delayed remote-control witness of 4√2. -/

import D5.S3.QuantumBounds.CHSHWitness
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence

namespace D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness

open scoped BigOperators ComplexConjugate
open Matrix

noncomputable section

private def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

/-- The source's controlled-A data gate. -/
def gateA (β δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, phase (β + δ)]

/-- The source's controlled-B data gate. -/
def gateB (β δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; phase (β - δ), 0]

/-- The controlled gate is |0><0| ⊗ A + |1><1| ⊗ B. -/
private def controlledGate (β δ : ℝ) (p p' i j : Fin 2) : ℂ :=
  (if p = 0 ∧ p' = 0 then 1 else 0) * gateA β δ i j +
    (if p = 1 ∧ p' = 1 then 1 else 0) * gateB β δ i j

/-- Bell input on P,R, controlled gate on P,D, then Hadamard on P; order P,D,R. -/
def circuitState (d : Fin 2 → ℂ) (β δ : ℝ) : (Fin 2 × Fin 2 × Fin 2) → ℂ :=
  fun k => ∑ p : Fin 2,
    D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard k.1 p *
      ∑ p' : Fin 2, ∑ j : Fin 2, controlledGate β δ p p' k.2.1 j *
        D5.S3.QuantumBounds.CHSHWitness.bellVector (p', k.2.2) * d j

/-- Conjugates of the source's a₀,a₁, with its irrelevant global phase α = 0. -/
def remote (β δ γ : ℝ) : Fin 2 → ℂ :=
  ![conj (phase (-(β + δ) / 2) * (Real.cos (γ / 2) : ℂ)),
    conj (phase (-(β - δ) / 2) * (Real.sin (γ / 2) : ℂ))]

/-- Outcome zero is |b><b|; outcome one is its complement. -/
def dataProjector (b : Fin 2 → ℂ) (n : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if n = 0 then vecMulVec b (star b) else 1 - vecMulVec b (star b)

private def projected (d b : Fin 2 → ℂ) (β δ : ℝ) (x : Fin 4) (r i : Fin 2) : ℂ :=
  ∑ j : Fin 2, dataProjector b ⟨x.val % 2, Nat.mod_lt _ (by norm_num)⟩ i j *
    circuitState d β δ (⟨x.val / 2, by omega⟩, j, r)

/-- Probability of preparation x = 2m+n after the program and data measurements. -/
def prepProb (d : Fin 2 → ℂ) (β δ : ℝ) (b : Fin 2 → ℂ) (x : Fin 4) : ℝ :=
  ∑ r : Fin 2, ∑ i : Fin 2, Complex.normSq (projected d b β δ x r i)

/-- Joint probability of preparation x and remote outcome zero at setting y. -/
def jointProb (d : Fin 2 → ℂ) (β δ γ₀ γ₁ : ℝ) (b : Fin 2 → ℂ)
    (x : Fin 4) (y : Fin 2) : ℝ :=
  ∑ i : Fin 2, Complex.normSq (∑ r : Fin 2,
    conj (remote β δ (if y = 0 then γ₀ else γ₁) r) * projected d b β δ x r i)

/-- Binary correlator from the circuit's conditional probability. -/
def E (d : Fin 2 → ℂ) (β δ γ₀ γ₁ : ℝ) (b : Fin 2 → ℂ)
    (x : Fin 4) (y : Fin 2) : ℝ :=
  2 * (jointProb d β δ γ₀ γ₁ b x y / prepProb d β δ b x) - 1

/-- Equation (2), with the source's first preparation labeling. -/
def S (d : Fin 2 → ℂ) (β δ γ₀ γ₁ : ℝ) (b : Fin 2 → ℂ) : ℝ :=
  E d β δ γ₀ γ₁ b 0 0 - E d β δ γ₀ γ₁ b 0 1 -
    E d β δ γ₀ γ₁ b 1 0 + E d β δ γ₀ γ₁ b 1 1 -
    E d β δ γ₀ γ₁ b 2 0 - E d β δ γ₀ γ₁ b 2 1 +
    E d β δ γ₀ γ₁ b 3 0 + E d β δ γ₀ γ₁ b 3 1

/-- Every Euclidean-unit data vector admits positive preparations and S > 4. -/
def claim : Prop :=
  ∀ d : Fin 2 → ℂ, ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 2))‖ = 1 →
    ∃ β δ γ₀ γ₁ : ℝ, ∃ b : Fin 2 → ℂ,
      ‖(WithLp.toLp 2 b : EuclideanSpace ℂ (Fin 2))‖ = 1 ∧
        (∀ x : Fin 4, 0 < prepProb d β δ b x) ∧ 4 < S d β δ γ₀ γ₁ b

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  rw [phase.eq_1, phase.eq_1, phase.eq_1, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  simp only [phase.eq_1, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul]

private theorem phase_cancel (t : ℝ) : phase t * phase (-t) = 1 := by
  rw [← phase_add, add_neg_cancel, phase.eq_1]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]

private theorem phase_normSq (t : ℝ) : Complex.normSq (phase t) = 1 := by
  rw [phase.eq_1, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

private theorem unit_coordinates (d : Fin 2 → ℂ)
    (hd : ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 2))‖ = 1) :
    Complex.normSq (d 0) + Complex.normSq (d 1) = 1 := by
  have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 2))
  simpa only [hd, one_pow, Fin.sum_univ_two, PiLp.toLp_apply,
    ← Complex.normSq_eq_norm_sq] using h.symm

private theorem circuit_coordinates (d : Fin 2 → ℂ) (β δ : ℝ) (m i r : Fin 2) :
    circuitState d β δ (m, i, r) =
      if r = 0 then (gateA β δ *ᵥ d) i / 2
      else (if m = 0 then 1 else -1) * (gateB β δ *ᵥ d) i / 2 := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  fin_cases m <;> fin_cases i <;> fin_cases r <;>
    simp only [circuitState.eq_1, controlledGate.eq_1, gateA.eq_1, gateB.eq_1,
      D5.S3.QuantumBounds.CHSHWitness.bellVector.eq_1,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients.eq_1,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard.eq_1,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.eq_1,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_2,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix.eq_4,
      D5.S3.Quantum.FiniteDimensional.qubitX.eq_1,
      D5.S3.Quantum.FiniteDimensional.qubitZ.eq_1,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Fin.isValue, ite_true, and_self,
      one_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  all_goals norm_num
  all_goals field_simp (disch := first | exact hs | exact two_ne_zero)

private theorem relative_phase (z : ℂ) :
    phase (-Complex.arg z) * z = (‖z‖ : ℂ) := by
  have hz := Complex.norm_mul_exp_arg_mul_I z
  change (‖z‖ : ℂ) * phase (Complex.arg z) = z at hz
  calc
    phase (-Complex.arg z) * z =
        phase (-Complex.arg z) * ((‖z‖ : ℂ) * phase (Complex.arg z)) :=
      congrArg (phase (-Complex.arg z) * ·) hz.symm
    _ =
        (‖z‖ : ℂ) * (phase (Complex.arg z) * phase (-Complex.arg z)) := by ring
    _ = (‖z‖ : ℂ) := by rw [phase_cancel, mul_one]

private theorem frame_coordinates (d : Fin 2 → ℂ)
    (hd : Complex.normSq (d 0) + Complex.normSq (d 1) = 1) :
    let δ := -Complex.arg (conj (d 0) * d 1)
    let u := gateA 0 δ *ᵥ d
    let w := fun i => phase δ * (gateB 0 δ *ᵥ d) i
    star u ⬝ᵥ u = 1 ∧ star w ⬝ᵥ w = 1 ∧
      star u ⬝ᵥ w = 0 ∧ star w ⬝ᵥ u = 0 := by
  let δ := -Complex.arg (conj (d 0) * d 1)
  have hp := phase_cancel δ
  have hr : phase δ * (conj (d 0) * d 1) =
      conj (phase δ * (conj (d 0) * d 1)) := by
    rw [relative_phase, Complex.conj_ofReal]
  have hd' : conj (d 0) * d 0 + conj (d 1) * d 1 = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_add, hd, Complex.ofReal_one]
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
    Matrix.mulVec, gateA.eq_1, gateB.eq_1, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply, zero_add, zero_sub,
    zero_mul, one_mul, add_zero, map_add, map_mul,
    map_neg, map_zero, map_one, phase_conj, neg_neg, neg_mul, mul_neg,
    starRingEnd_self_apply] at hr ⊢
  have harg : Complex.arg (conj (d 0) * d 1) = -δ := by
    dsimp only [δ]
    rw [neg_neg]
  simp only [harg, neg_neg]
  constructor
  · calc
      _ = conj (d 0) * d 0 + (phase δ * phase (-δ)) * (conj (d 1) * d 1) := by ring
      _ = 1 := by rw [hp, one_mul, hd']
  constructor
  · calc
      _ = (phase δ * phase (-δ)) * (conj (d 1) * d 1) +
          (phase δ * phase (-δ)) ^ 2 * (conj (d 0) * d 0) := by ring
      _ = 1 := by rw [hp]; simpa only [one_mul, one_pow, add_comm] using hd'
  constructor
  · linear_combination -hr + phase (-δ) * d 0 * conj (d 1) * hp
  · linear_combination hr + phase δ * conj (d 0) * d 1 * hp

private theorem rotation_inner (u w : Fin 2 → ℂ) (C T : ℝ)
    (hu : star u ⬝ᵥ u = 1) (hw : star w ⬝ᵥ w = 1)
    (huw : star u ⬝ᵥ w = 0) (hwu : star w ⬝ᵥ u = 0)
    (hCT : C ^ 2 + T ^ 2 = 1) :
    let b := (C : ℂ) • u + (T : ℂ) • w
    let k := (T : ℂ) • u - (C : ℂ) • w
    star b ⬝ᵥ b = 1 ∧ star k ⬝ᵥ k = 1 ∧
      star b ⬝ᵥ u = (C : ℂ) ∧ star b ⬝ᵥ w = (T : ℂ) := by
  dsimp only
  simp only [star_add, star_sub, star_smul, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    Complex.star_def, Complex.conj_ofReal, smul_eq_mul, hu, hw, huw, hwu,
    mul_zero, mul_one, zero_add, add_zero, sub_zero, zero_sub, mul_neg]
  have h : (C : ℂ) * C + (T : ℂ) * T = 1 := by
    exact_mod_cast (by simpa only [pow_two] using hCT : C * C + T * T = 1)
  constructor
  · exact h
  constructor
  · linear_combination h
  exact ⟨trivial, trivial⟩

private theorem projector_action (b v : Fin 2 → ℂ) (n : Fin 2) (i : Fin 2) :
    (dataProjector b n *ᵥ v) i =
      if n = 0 then (star b ⬝ᵥ v) * b i else v i - (star b ⬝ᵥ v) * b i := by
  rw [dataProjector.eq_1]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos hn, vecMulVec_mulVec]
    change b i * (star b ⬝ᵥ v) = (star b ⬝ᵥ v) * b i
    exact mul_comm _ _
  · rw [if_neg hn, if_neg hn, sub_mulVec, one_mulVec, vecMulVec_mulVec]
    change v i - b i * (star b ⬝ᵥ v) = v i - (star b ⬝ᵥ v) * b i
    rw [mul_comm (b i)]

private theorem rotation_projectors (u w : Fin 2 → ℂ) (C T : ℝ)
    (hbu : star ((C : ℂ) • u + (T : ℂ) • w) ⬝ᵥ u = (C : ℂ))
    (hbw : star ((C : ℂ) • u + (T : ℂ) • w) ⬝ᵥ w = (T : ℂ))
    (hCT : C ^ 2 + T ^ 2 = 1) (n i : Fin 2) :
    let b := (C : ℂ) • u + (T : ℂ) • w
    let k := (T : ℂ) • u - (C : ℂ) • w
    (dataProjector b n *ᵥ u) i =
      (if n = 0 then (C : ℂ) * b i else (T : ℂ) * k i) ∧
    (dataProjector b n *ᵥ w) i =
      (if n = 0 then (T : ℂ) * b i else -(C : ℂ) * k i) := by
  have h : (C : ℂ) ^ 2 + (T : ℂ) ^ 2 = 1 := by exact_mod_cast hCT
  dsimp only
  rw [projector_action, projector_action, hbu, hbw]
  by_cases hn : n = 0
  · simp only [if_pos hn, and_self]
  · simp only [if_neg hn, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · linear_combination -u i * h
    · linear_combination -w i * h

private theorem inner_unit_sum (v : Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    Complex.normSq (v 0) + Complex.normSq (v 1) = 1 := by
  have h := congrArg Complex.re hv
  simpa only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.add_re, Complex.ofReal_re,
    Complex.one_re] using h

private theorem angle_coefficients :
    let C := Real.cos (Real.pi / 8)
    let T := Real.sin (Real.pi / 8)
    C ^ 2 + T ^ 2 = 1 ∧ 2 * C * T = Real.sqrt 2 / 2 ∧
      C ^ 2 - T ^ 2 = Real.sqrt 2 / 2 := by
  have hc := Real.cos_two_mul (Real.pi / 8)
  have hs := Real.sin_two_mul (Real.pi / 8)
  have hangle : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [hangle, Real.cos_pi_div_four] at hc
  rw [hangle, Real.sin_pi_div_four] at hs
  have hCT := Real.cos_sq_add_sin_sq (Real.pi / 8)
  exact ⟨hCT, by nlinarith [hs], by nlinarith [hc, hCT]⟩

private theorem projected_mulVec (d b : Fin 2 → ℂ) (β δ : ℝ)
    (x : Fin 4) (r i : Fin 2) :
    projected d b β δ x r i =
      if r = 0 then
        (dataProjector b ⟨x.val % 2, Nat.mod_lt _ (by norm_num)⟩ *ᵥ
          (gateA β δ *ᵥ d)) i / 2
      else (if (⟨x.val / 2, by omega⟩ : Fin 2) = 0 then 1 else -1) *
        (dataProjector b ⟨x.val % 2, Nat.mod_lt _ (by norm_num)⟩ *ᵥ
          (gateB β δ *ᵥ d)) i / 2 := by
  rw [projected.eq_1]
  simp only [circuit_coordinates]
  by_cases hr : r = 0
  · simp only [if_pos hr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp only [if_neg hr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

private theorem probabilities_from_branches (d b v : Fin 2 → ℂ)
    (δ a t : ℝ) (x : Fin 4)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1)
    (h0 : ∀ i, projected d b 0 δ x 0 i = (a : ℂ) * v i / 2)
    (h1 : ∀ i, projected d b 0 δ x 1 i = phase (-δ) * (t : ℂ) * v i / 2) :
    prepProb d 0 δ b x = (a ^ 2 + t ^ 2) / 4 ∧
      ∀ γ₀ γ₁ (y : Fin 2), jointProb d 0 δ γ₀ γ₁ b x y =
        (a * Real.cos ((if y = 0 then γ₀ else γ₁) / 2) +
          t * Real.sin ((if y = 0 then γ₀ else γ₁) / 2)) ^ 2 / 4 := by
  constructor
  · rw [prepProb.eq_1]
    simp only [Fin.sum_univ_two, h0, h1, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofNat, phase_normSq, one_mul]
    calc
      _ = (a ^ 2 + t ^ 2) / 4 * (Complex.normSq (v 0) + Complex.normSq (v 1)) := by ring
      _ = _ := by rw [hv, mul_one]
  · intro γ₀ γ₁ y
    let γ := if y = 0 then γ₀ else γ₁
    have hp : phase (δ / 2) * phase (-δ) = phase (-δ / 2) := by
      rw [← phase_add]
      congr 1
      ring
    have hamp (i : Fin 2) :
        ∑ r : Fin 2, conj (remote 0 δ γ r) * projected d b 0 δ x r i =
          phase (-δ / 2) *
            ((a * Real.cos (γ / 2) + t * Real.sin (γ / 2) : ℝ) : ℂ) * v i / 2 := by
      simp only [Fin.sum_univ_two, remote.eq_1, Matrix.cons_val_zero,
        Matrix.cons_val_one, h0, h1, starRingEnd_self_apply, zero_add, zero_sub,
        neg_neg, Complex.ofReal_add, Complex.ofReal_mul]
      calc
        _ = phase (-δ / 2) * (a : ℂ) * (Real.cos (γ / 2) : ℂ) * v i / 2 +
            (phase (δ / 2) * phase (-δ)) * (t : ℂ) *
              (Real.sin (γ / 2) : ℂ) * v i / 2 := by ring
        _ = _ := by rw [hp]; ring
    rw [jointProb.eq_1]
    change (∑ i : Fin 2, Complex.normSq
      (∑ r : Fin 2, conj (remote 0 δ γ r) * projected d b 0 δ x r i)) = _
    simp only [hamp, Fin.sum_univ_two, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofNat, phase_normSq, one_mul]
    calc
      _ = (a * Real.cos (γ / 2) + t * Real.sin (γ / 2)) ^ 2 / 4 *
          (Complex.normSq (v 0) + Complex.normSq (v 1)) := by ring
      _ = _ := by rw [hv, mul_one]

private theorem rotation_branches (d : Fin 2 → ℂ) (δ C T : ℝ)
    (hCT : C ^ 2 + T ^ 2 = 1)
    (hbu : star ((C : ℂ) • (gateA 0 δ *ᵥ d) +
      (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) ⬝ᵥ (gateA 0 δ *ᵥ d) = (C : ℂ))
    (hbw : star ((C : ℂ) • (gateA 0 δ *ᵥ d) +
      (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) ⬝ᵥ
        (fun i => phase δ * (gateB 0 δ *ᵥ d) i) = (T : ℂ)) (x : Fin 4) :
    let u := gateA 0 δ *ᵥ d
    let w := fun i => phase δ * (gateB 0 δ *ᵥ d) i
    let b := (C : ℂ) • u + (T : ℂ) • w
    let k := (T : ℂ) • u - (C : ℂ) • w
    (∀ i, projected d b 0 δ x 0 i =
      (if x.val % 2 = 0 then (C : ℂ) * b i else (T : ℂ) * k i) / 2) ∧
    (∀ i, projected d b 0 δ x 1 i = phase (-δ) *
      (if x = 0 then (T : ℂ) * b i else if x = 1 then -(C : ℂ) * k i
        else if x = 2 then -(T : ℂ) * b i else (C : ℂ) * k i) / 2) := by
  let u := gateA 0 δ *ᵥ d
  let w := fun i => phase δ * (gateB 0 δ *ᵥ d) i
  let b := (C : ℂ) • u + (T : ℂ) • w
  let k := (T : ℂ) • u - (C : ℂ) • w
  have hgate : gateB 0 δ *ᵥ d = phase (-δ) • w := by
    funext i
    change (gateB 0 δ *ᵥ d) i = phase (-δ) * (phase δ * (gateB 0 δ *ᵥ d) i)
    rw [← mul_assoc, mul_comm (phase (-δ)), phase_cancel, one_mul]
  have hpu0 (i) : (dataProjector b 0 *ᵥ u) i = (C : ℂ) * b i := by
    simpa only [if_pos rfl, ite_true] using (rotation_projectors u w C T hbu hbw hCT 0 i).1
  have hpw0 (i) : (dataProjector b 0 *ᵥ w) i = (T : ℂ) * b i := by
    simpa only [if_pos rfl, ite_true] using (rotation_projectors u w C T hbu hbw hCT 0 i).2
  have hpu1 (i) : (dataProjector b 1 *ᵥ u) i = (T : ℂ) * k i := by
    simpa only [if_neg (by decide : (1 : Fin 2) ≠ 0)] using
      (rotation_projectors u w C T hbu hbw hCT 1 i).1
  have hpw1 (i) : (dataProjector b 1 *ᵥ w) i = -(C : ℂ) * k i := by
    simpa only [if_neg (by decide : (1 : Fin 2) ≠ 0)] using
      (rotation_projectors u w C T hbu hbw hCT 1 i).2
  constructor
  · intro i
    rw [projected_mulVec]
    fin_cases x
    · change (dataProjector b 0 *ᵥ u) i / 2 = (C : ℂ) * b i / 2
      rw [hpu0]
    · change (dataProjector b 1 *ᵥ u) i / 2 = (T : ℂ) * k i / 2
      rw [hpu1]
    · change (dataProjector b 0 *ᵥ u) i / 2 = (C : ℂ) * b i / 2
      rw [hpu0]
    · change (dataProjector b 1 *ᵥ u) i / 2 = (T : ℂ) * k i / 2
      rw [hpu1]
  · intro i
    rw [projected_mulVec]
    fin_cases x
    · change 1 * (dataProjector b 0 *ᵥ (gateB 0 δ *ᵥ d)) i / 2 =
        phase (-δ) * ((T : ℂ) * b i) / 2
      rw [hgate, Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hpw0, one_mul]
    · change 1 * (dataProjector b 1 *ᵥ (gateB 0 δ *ᵥ d)) i / 2 =
        phase (-δ) * (-(C : ℂ) * k i) / 2
      rw [hgate, Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hpw1, one_mul]
    · change -1 * (dataProjector b 0 *ᵥ (gateB 0 δ *ᵥ d)) i / 2 =
        phase (-δ) * (-(T : ℂ) * b i) / 2
      rw [hgate, Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hpw0]
      ring
    · change -1 * (dataProjector b 1 *ᵥ (gateB 0 δ *ᵥ d)) i / 2 =
        phase (-δ) * ((C : ℂ) * k i) / 2
      rw [hgate, Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hpw1]
      ring

set_option maxHeartbeats 800000 in
-- This certificate contains eight finite-index polynomial calculations.
private theorem correlator_table (d : Fin 2 → ℂ) (δ C T : ℝ)
    (hCT : C ^ 2 + T ^ 2 = 1)
    (hprod : 2 * C * T = Real.sqrt 2 / 2)
    (hdiff : C ^ 2 - T ^ 2 = Real.sqrt 2 / 2)
    (hbu : star ((C : ℂ) • (gateA 0 δ *ᵥ d) +
      (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) ⬝ᵥ (gateA 0 δ *ᵥ d) = (C : ℂ))
    (hbw : star ((C : ℂ) • (gateA 0 δ *ᵥ d) +
      (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) ⬝ᵥ
        (fun i => phase δ * (gateB 0 δ *ᵥ d) i) = (T : ℂ))
    (hb : star ((C : ℂ) • (gateA 0 δ *ᵥ d) +
      (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) ⬝ᵥ
        ((C : ℂ) • (gateA 0 δ *ᵥ d) +
          (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) = 1)
    (hk : star ((T : ℂ) • (gateA 0 δ *ᵥ d) -
      (C : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) ⬝ᵥ
        ((T : ℂ) • (gateA 0 δ *ᵥ d) -
          (C : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)) = 1) :
    let b := (C : ℂ) • (gateA 0 δ *ᵥ d) +
      (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)
    (∀ x, prepProb d 0 δ b x = 1 / 4) ∧
      (∀ x y, E d 0 δ (Real.pi / 2) Real.pi b x y =
        (if (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ x = 3 then 1 else -1) *
          (Real.sqrt 2 / 2)) ∧
      S d 0 δ (Real.pi / 2) Real.pi b = 4 * Real.sqrt 2 := by
  let b := (C : ℂ) • (gateA 0 δ *ᵥ d) +
    (T : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)
  let k := (T : ℂ) • (gateA 0 δ *ᵥ d) -
    (C : ℂ) • (fun i => phase δ * (gateB 0 δ *ᵥ d) i)
  have hb' := inner_unit_sum b hb
  have hk' := inner_unit_sum k hk
  have hrows := rotation_branches d δ C T hCT hbu hbw
  have h0 := probabilities_from_branches d b b δ C T 0 hb'
    (by
      intro i
      have h := (hrows 0).1 i
      change projected d b 0 δ 0 0 i = (C : ℂ) * b i / 2 at h
      exact h)
    (by
      intro i
      have h := (hrows 0).2 i
      change projected d b 0 δ 0 1 i = phase (-δ) * ((T : ℂ) * b i) / 2 at h
      simpa only [mul_assoc] using h)
  have h1 := probabilities_from_branches d b k δ T (-C) 1 hk'
    (by
      intro i
      have h := (hrows 1).1 i
      change projected d b 0 δ 1 0 i = (T : ℂ) * k i / 2 at h
      exact h)
    (by
      intro i
      have h := (hrows 1).2 i
      change projected d b 0 δ 1 1 i = phase (-δ) * (-(C : ℂ) * k i) / 2 at h
      simpa only [Complex.ofReal_neg, mul_assoc] using h)
  have h2 := probabilities_from_branches d b b δ C (-T) 2 hb'
    (by
      intro i
      have h := (hrows 2).1 i
      change projected d b 0 δ 2 0 i = (C : ℂ) * b i / 2 at h
      exact h)
    (by
      intro i
      have h := (hrows 2).2 i
      change projected d b 0 δ 2 1 i = phase (-δ) * (-(T : ℂ) * b i) / 2 at h
      simpa only [Complex.ofReal_neg, mul_assoc] using h)
  have h3 := probabilities_from_branches d b k δ T C 3 hk'
    (by
      intro i
      have h := (hrows 3).1 i
      change projected d b 0 δ 3 0 i = (T : ℂ) * k i / 2 at h
      exact h)
    (by
      intro i
      have h := (hrows 3).2 i
      change projected d b 0 δ 3 1 i = phase (-δ) * ((C : ℂ) * k i) / 2 at h
      simpa only [mul_assoc] using h)
  have hprep (x) : prepProb d 0 δ b x = 1 / 4 := by
    fin_cases x
    · change prepProb d 0 δ b 0 = 1 / 4
      rw [h0.1, hCT]
    · change prepProb d 0 δ b 1 = 1 / 4
      rw [h1.1, neg_sq]; nlinarith [hCT]
    · change prepProb d 0 δ b 2 = 1 / 4
      rw [h2.1, neg_sq, hCT]
    · change prepProb d 0 δ b 3 = 1 / 4
      rw [h3.1]; nlinarith [hCT]
  have he (x y) : E d 0 δ (Real.pi / 2) Real.pi b x y =
      (if (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ x = 3 then 1 else -1) *
        (Real.sqrt 2 / 2) := by
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hangle : Real.pi / 2 / 2 = Real.pi / 4 := by ring
    fin_cases x <;> fin_cases y
    · change E d 0 δ (Real.pi / 2) Real.pi b 0 0 = (1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h0.2]
      rw [if_pos rfl]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      simp only [hs]
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 0 1 = (-1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h0.2]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 1 0 = (-1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h1.2]
      rw [if_pos rfl]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      simp only [hs]
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 1 1 = (1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h1.2]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 2 0 = (-1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h2.2]
      rw [if_pos rfl]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      simp only [hs]
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 2 1 = (-1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h2.2]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 3 0 = (1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h3.2]
      rw [if_pos rfl]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      simp only [hs]
      nlinarith [hCT, hprod, hdiff]
    · change E d 0 δ (Real.pi / 2) Real.pi b 3 1 = (1 : ℝ) * (Real.sqrt 2 / 2)
      rw [E.eq_1, hprep, h3.2]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      norm_num only [Fin.isValue, ite_true, ite_false, hangle,
        Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring_nf
      nlinarith [hCT, hprod, hdiff]
  refine ⟨hprep, he, ?_⟩
  change S d 0 δ (Real.pi / 2) Real.pi b = 4 * Real.sqrt 2
  rw [S.eq_1]
  simp only [he]
  change (1 : ℝ) * (Real.sqrt 2 / 2) - (-1) * (Real.sqrt 2 / 2) -
    (-1) * (Real.sqrt 2 / 2) + 1 * (Real.sqrt 2 / 2) -
    (-1) * (Real.sqrt 2 / 2) - (-1) * (Real.sqrt 2 / 2) +
    1 * (Real.sqrt 2 / 2) + 1 * (Real.sqrt 2 / 2) = 4 * Real.sqrt 2
  ring

/-- The explicit construction attains S = 4√2 for every unit data qubit. -/
theorem result : claim := by
  rw [claim.eq_1]
  intro d hd
  let δ := -Complex.arg (conj (d 0) * d 1)
  let C := Real.cos (Real.pi / 8)
  let T := Real.sin (Real.pi / 8)
  let u := gateA 0 δ *ᵥ d
  let w := fun i => phase δ * (gateB 0 δ *ᵥ d) i
  let b := (C : ℂ) • u + (T : ℂ) • w
  obtain ⟨hCT, hprod, hdiff⟩ := angle_coefficients
  obtain ⟨hu, hw, huw, hwu⟩ := frame_coordinates d (unit_coordinates d hd)
  obtain ⟨hb, hk, hbu, hbw⟩ := rotation_inner u w C T hu hw huw hwu hCT
  obtain ⟨hprep, _, hs⟩ := correlator_table d δ C T hCT hprod hdiff hbu hbw hb hk
  refine ⟨0, δ, Real.pi / 2, Real.pi, b, ?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change Real.sqrt (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2) = 1
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      inner_unit_sum b hb, Real.sqrt_one]
  · intro x
    rw [hprep]
    norm_num
  · rw [hs]
    nlinarith [Real.one_lt_sqrt_two]

end

end D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness
