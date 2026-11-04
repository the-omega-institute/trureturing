/- GID: D5/S3/Quantum/Recovery/CoherentUniformAmplification
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/CoherentUniformAmplification
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Uniform source rotation and an exact finite coin circuit with a source-query bound. -/

/-
proof_shape: uniform_operator_rotation: content
escape_witness: rotation_power proves the unbounded whole-source power identity
by induction and is used on the live path of uniform_operator_rotation.
admission_basis: escape-witness (candidate; independent review pending)
direct_frozen_dependencies: none (Mathlib only).
exact_coherent_amplification: content; the known block coin, the finite word,
and the ceiling/angle estimate construct an exact all-source circuit.
Its live construction uses coin_data, word_semantics, and exact_angle_choice.
exact_angle_choice: content estimate chain; consumer: exact_coherent_amplification.
word_semantics: content induction; consumer: exact_coherent_amplification.
source_gram, frame_rotation, unit_success, coin_unitary, coin_data,
word_unitary: bind-only consumed helpers; the coin helpers are consumed by
exact_coherent_amplification and its word lemmas.
coinEmbed, coinLift, coinRotation, coinGood, AmplificationGate, gateMatrix,
evaluateWord, reflectionBlock, amplificationWord, sourceQueries are definitions
consumed by exact_coherent_amplification and its live helper proofs.
rotation_power: content; consumer: uniform_operator_rotation.
utility: none; the result is a uniform theorem for arbitrary finite spaces,
not a certified finite instance, enumeration, checker, or numeric reduction.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! The same two reflections act on every source column. The standard
amplitude-amplification rotation is expressed as a rectangular operator
identity, rather than a reflection chosen from an unknown input vector.
The finite coin circuit below uses the same operator rotation directly. -/

noncomputable section
open scoped Matrix Kronecker ComplexOrder

namespace D5.S3.Quantum.Recovery.CoherentUniformAmplification

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {s l : Type*} [Fintype s] [DecidableEq s] [Fintype l] [DecidableEq l]

/-- The normalized successful source isometry. -/
def success (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ) : Matrix l s ℂ :=
  (Real.sqrt p : ℂ)⁻¹ • (P * U)

/-- The normalized failed source isometry, for success strictly below one. -/
def failure (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ) : Matrix l s ℂ :=
  (Real.sqrt (1 - p) : ℂ)⁻¹ • ((1 - P) * U)

/-- Reflection in the prepared source subspace, followed by a good-flag flip. -/
def iterate (U : Matrix l s ℂ) (P : Matrix l l ℂ) : Matrix l l ℂ :=
  ((2 : ℂ) • (U * Uᴴ) - 1) * ((1 : Matrix l l ℂ) - (2 : ℂ) • P)

omit [Fintype s] [DecidableEq s] in
private theorem rotation_power (Q : Matrix l l ℂ) (W B : Matrix l s ℂ) (θ : ℝ)
    (hW : Q * W = (Real.cos (2 * θ) : ℂ) • W - (Real.sin (2 * θ) : ℂ) • B)
    (hB : Q * B = (Real.sin (2 * θ) : ℂ) • W + (Real.cos (2 * θ) : ℂ) • B)
    (n : ℕ) :
    Q ^ n * ((Real.sin θ : ℂ) • W + (Real.cos θ : ℂ) • B) =
      (Real.sin ((2 * n + 1) * θ) : ℂ) • W +
      (Real.cos ((2 * n + 1) * θ) : ℂ) • B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, hW, hB]
    have ha : (2 * (↑(n + 1) : ℝ) + 1) * θ = (2 * n + 1) * θ + 2 * θ := by
      push_cast
      ring
    rw [ha, Real.sin_add, Real.cos_add]
    push_cast
    simp only [smul_add, smul_sub, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

omit [Fintype s] in
private theorem source_gram (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ)
    (hU : Uᴴ * U = 1) (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * U)ᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ)) :
    Uᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ) ∧
    ((1 - P) * U)ᴴ * ((1 - P) * U) = (1 - (p : ℂ)) • (1 : Matrix s s ℂ) ∧
    (P * U)ᴴ * ((1 - P) * U) = 0 := by
  have hg : Uᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ) := by
    simpa only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc,
      ← Matrix.mul_assoc P P, hPP] using hA
  refine ⟨hg, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      hP, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P U, hPP, hg, hU]
    module
  · simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P (1 - P) U, Matrix.mul_sub, Matrix.mul_one, hPP,
      sub_self, Matrix.zero_mul, Matrix.mul_zero]

private theorem frame_rotation (U : Matrix l s ℂ) (P : Matrix l l ℂ) (p : ℝ)
    (hp : 0 < p) (hpl : p < 1) (hU : Uᴴ * U = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * U)ᴴ * (P * U) = (p : ℂ) • (1 : Matrix s s ℂ)) :
    let θ := Real.arcsin (Real.sqrt p)
    let W := success U P p
    let B := failure U P p
    Wᴴ * W = 1 ∧ Bᴴ * B = 1 ∧ Wᴴ * B = 0 ∧
    U = (Real.sin θ : ℂ) • W + (Real.cos θ : ℂ) • B ∧
    iterate U P * W = (Real.cos (2 * θ) : ℂ) • W - (Real.sin (2 * θ) : ℂ) • B ∧
    iterate U P * B = (Real.sin (2 * θ) : ℂ) • W + (Real.cos (2 * θ) : ℂ) • B := by
  have hs : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  have ht : (Real.sqrt (1 - p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (sub_pos.2 hpl)).ne'
  have hs2 : (Real.sqrt p : ℂ) ^ 2 = p := by
    exact_mod_cast Real.sq_sqrt hp.le
  have ht2 : (Real.sqrt (1 - p) : ℂ) ^ 2 = 1 - (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_pos.2 hpl).le
  have hsin : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) ((Real.sqrt_le_one).2 hpl.le)
  have hcos : Real.cos (Real.arcsin (Real.sqrt p)) = Real.sqrt (1 - p) := by
    rw [Real.cos_arcsin, Real.sq_sqrt hp.le]
  obtain ⟨hg, hb, ho⟩ := source_gram U P p hU hP hPP hA
  have hPA : P * (P * U) = P * U := by rw [← Matrix.mul_assoc, hPP]
  have hPD : P * ((1 - P) * U) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, Matrix.zero_mul]
  have hFA : (U * Uᴴ) * (P * U) = (p : ℂ) • U := by
    rw [Matrix.mul_assoc, hg, Matrix.mul_smul, Matrix.mul_one]
  have hFD : (U * Uᴴ) * ((1 - P) * U) = (1 - (p : ℂ)) • U := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hU, hg,
      Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    module
  have hflipA : ((1 : Matrix l l ℂ) - (2 : ℂ) • P) * (P * U) = -(P * U) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hPA]
    module
  have hflipD : ((1 : Matrix l l ℂ) - (2 : ℂ) • P) * ((1 - P) * U) = (1 - P) * U := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hPD, smul_zero, sub_zero]
  have hQA : iterate U P * (P * U) = P * U - (2 * (p : ℂ)) • U := by
    rw [iterate, Matrix.mul_assoc, hflipA, Matrix.mul_neg, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, hFA]
    module
  have hQD : iterate U P * ((1 - P) * U) =
      (2 * (1 - (p : ℂ))) • U - (1 - P) * U := by
    rw [iterate, Matrix.mul_assoc, hflipD, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, hFD]
    module
  have hstarS : star ((Real.sqrt p : ℂ)⁻¹) = (Real.sqrt p : ℂ)⁻¹ := by
    simp
  have hstarT : star ((Real.sqrt (1-p) : ℂ)⁻¹) = (Real.sqrt (1-p) : ℂ)⁻¹ := by
    simp
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [success, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hA, hstarS]
    have hc : (Real.sqrt p : ℂ)⁻¹ * (Real.sqrt p : ℂ)⁻¹ * (p : ℂ) = 1 := by
      rw [← hs2]
      field_simp
    rw [← mul_assoc, hc, one_smul]
  · simp only [failure, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hb, hstarT]
    have hc : (Real.sqrt (1-p) : ℂ)⁻¹ * (Real.sqrt (1-p) : ℂ)⁻¹ * (1-(p:ℂ)) = 1 := by
      rw [← ht2]
      field_simp
    rw [← mul_assoc, hc, one_smul]
  · simp only [success, failure, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, ho, smul_zero]
  · rw [hsin, hcos]
    simp only [success, failure, smul_smul, mul_inv_cancel₀ hs, mul_inv_cancel₀ ht,
      one_smul, Matrix.sub_mul, Matrix.one_mul]
    module
  · rw [Real.cos_two_mul, Real.sin_two_mul, hsin, hcos]
    simp only [success, failure, Matrix.mul_smul, hQA, smul_smul, Matrix.sub_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    field_simp [hs, ht]
    ring_nf
    simp only [hs2, ht2]
    ring
  · rw [Real.cos_two_mul, Real.sin_two_mul, hsin, hcos]
    simp only [success, failure]
    rw [Matrix.mul_smul, hQD]
    simp only [smul_smul, Matrix.sub_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    field_simp [hs, ht]
    ring_nf
    simp only [hs2, ht2]
    ring

private theorem unit_success (U : Matrix l s ℂ) (P : Matrix l l ℂ)
    (hU : Uᴴ * U = 1) (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * U)ᴴ * (P * U) = 1) : U = success U P 1 := by
  have hg : (P * U)ᴴ * (P * U) = ((1 : ℝ) : ℂ) • (1 : Matrix s s ℂ) := by
    simpa using hA
  have hb := (source_gram U P 1 hU hP hPP hg).2.1
  have hz : (1 - P) * U = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa using hb)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hz
  simpa [success] using hz

/-- The normalized success and failure operators are orthogonal isometries,
and every power of the same reflection product rotates the whole source.
The equality remains an operator equality after tensoring any reference matrix.
This establishes the uniform-rotation part of coherent amplification; it
does not assert the auxiliary-coin construction or a gate-count bound. -/
theorem uniform_operator_rotation
    (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (p : ℝ)
    (hJ : Jᴴ * J = 1) (hC : Cᴴ * C = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * (C * J))ᴴ * (P * (C * J)) = (p : ℂ) • (1 : Matrix s s ℂ))
    (hp : 0 < p) (hple : p ≤ 1) :
    let U := C * J
    let W := success U P p
    let B := failure U P p
    let θ := Real.arcsin (Real.sqrt p)
    if p = 1 then U = W else
    Wᴴ * W = 1 ∧ Bᴴ * B = 1 ∧ Wᴴ * B = 0 ∧
    ∀ n : ℕ,
      iterate U P ^ n * U =
        (Real.sin ((2 * n + 1) * θ) : ℂ) • W +
        (Real.cos ((2 * n + 1) * θ) : ℂ) • B ∧
      ∀ (z : Type*) (R : Matrix z z ℂ),
        (iterate U P ^ n * U) ⊗ₖ R =
          (Real.sin ((2 * n + 1) * θ) : ℂ) • (W ⊗ₖ R) +
          (Real.cos ((2 * n + 1) * θ) : ℂ) • (B ⊗ₖ R) := by
  classical
  dsimp only
  have hU : (C * J)ᴴ * (C * J) = 1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Cᴴ C J, hC, Matrix.one_mul, hJ]
  by_cases hp1 : p = 1
  · subst p
    simp only [if_pos rfl]
    exact unit_success (C * J) P hU hP hPP (by simpa using hA)
  rw [if_neg hp1]
  have hpl : p < 1 := lt_of_le_of_ne hple hp1
  obtain ⟨hW, hB, hWB, hsplit, hrW, hrB⟩ :=
    frame_rotation (C * J) P p hp hpl hU hP hPP hA
  refine ⟨hW, hB, hWB, ?_⟩
  intro n
  have he := rotation_power (iterate (C * J) P)
    (success (C * J) P p) (failure (C * J) P p)
    (Real.arcsin (Real.sqrt p)) hrW hrB n
  rw [← hsplit] at he
  refine ⟨he, ?_⟩
  intro z R
  rw [he, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]

#print axioms uniform_operator_rotation

/-- The fixed initialized coin label, without changing the source space. -/
def coinEmbed (J : Matrix l s ℂ) : Matrix (l ⊕ l) s ℂ :=
  Matrix.fromRows J 0

/-- The old operation acts on both labels of the extra coin. -/
def coinLift (C : Matrix l l ℂ) : Matrix (l ⊕ l) (l ⊕ l) ℂ :=
  Matrix.fromBlocks C 0 0 C

/-- A known real coin rotation; its first column has success probability q. -/
def coinRotation (q : ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℂ :=
  Matrix.fromBlocks ((Real.sqrt q : ℂ) • 1) (-(Real.sqrt (1-q) : ℂ) • 1)
    ((Real.sqrt (1-q) : ℂ) • 1) ((Real.sqrt q : ℂ) • 1)

/-- Both the original flag and the fixed coin label must be successful. -/
def coinGood (P : Matrix l l ℂ) : Matrix (l ⊕ l) (l ⊕ l) ℂ :=
  Matrix.fromBlocks P 0 0 0

private theorem coin_unitary (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (coinRotation (l := l) q)ᴴ * coinRotation q = 1 := by
  have ha : (Real.sqrt q : ℂ)^2 = q := by exact_mod_cast Real.sq_sqrt hq
  have hb : (Real.sqrt (1-q) : ℂ)^2 = 1-(q:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hq1)
  have hsa : star (Real.sqrt q : ℂ) = (Real.sqrt q : ℂ) := by simp
  have hsb : star (Real.sqrt (1-q) : ℂ) = (Real.sqrt (1-q) : ℂ) := by simp
  simp only [coinRotation, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_neg, hsa, hsb, Matrix.fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  all_goals (ring_nf <;> simp only [ha, hb] <;> ring)

private theorem coin_data (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (p r : ℝ)
    (hp : 0 < p) (hr : 0 < r) (hrp : r ≤ p)
    (hJ : Jᴴ * J = 1) (hC : Cᴴ * C = 1)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hA : (P * (C * J))ᴴ * (P * (C * J)) = (p:ℂ) • (1 : Matrix s s ℂ)) :
    let K := coinEmbed J
    let D := coinRotation (l := l) (r/p) * coinLift C
    let G := coinGood P
    Kᴴ*K = 1 ∧ Dᴴ*D = 1 ∧ Gᴴ = G ∧ G*G = G ∧
    (G*(D*K))ᴴ*(G*(D*K)) = (r:ℂ) • (1 : Matrix s s ℂ) ∧
    success (D*K) G r = coinEmbed (success (C*J) P p) := by
  have hq : 0 ≤ r/p := (div_pos hr hp).le
  have hq1 : r/p ≤ 1 := (div_le_one hp).mpr hrp
  have hcoin := coin_unitary (l := l) (r/p) hq hq1
  have hL : (coinLift C)ᴴ * coinLift C = 1 := by
    simp [coinLift, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hC,
      Matrix.fromBlocks_one]
  have hK : (coinEmbed J)ᴴ * coinEmbed J = 1 := by
    simp [coinEmbed, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hJ]
  have hgood : (coinGood P)ᴴ = coinGood P := by
    simp [coinGood, Matrix.fromBlocks_conjTranspose, hP]
  have hgg : coinGood P * coinGood P = coinGood P := by
    simp [coinGood, Matrix.fromBlocks_multiply, hPP]
  have hd : (coinRotation (r/p) * coinLift C)ᴴ *
      (coinRotation (r/p) * coinLift C) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (coinRotation (r/p))ᴴ, hcoin, Matrix.one_mul, hL]
  have hg : coinGood P * ((coinRotation (r/p) * coinLift C) * coinEmbed J) =
      coinEmbed ((Real.sqrt (r/p) : ℂ) • (P*(C*J))) := by
    simp [coinGood, coinRotation, coinLift, coinEmbed, Matrix.fromBlocks_mul_fromRows,
      Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  have hs : (Real.sqrt (r/p) : ℂ)^2 = (r/p:ℝ) := by
    exact_mod_cast Real.sq_sqrt hq
  have hratio : (r/p:ℝ) * p = r := div_mul_cancel₀ _ hp.ne'
  have hnorm : (Real.sqrt r : ℂ)⁻¹ * (Real.sqrt (r/p) : ℂ) =
      (Real.sqrt p : ℂ)⁻¹ := by
    rw [Real.sqrt_div hr.le p]
    push_cast
    field_simp [show (Real.sqrt r : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr hr).ne',
      show (Real.sqrt p : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr hp).ne']
  dsimp only
  refine ⟨hK, hd, hgood, hgg, ?_, ?_⟩
  · rw [hg]
    simp only [coinEmbed, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_zero, Matrix.zero_mul,
      add_zero, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, show star (Real.sqrt (r/p) : ℂ) = (Real.sqrt (r/p) : ℂ) by simp, ← pow_two, hs, hA]
    apply congrArg (fun z : ℂ => z • (1 : Matrix s s ℂ))
    calc
      _ = (Real.sqrt (r/p):ℂ)^2 * (p:ℂ) := by ring
      _ = (r/p:ℝ) * (p:ℂ) := by rw [hs]
      _ = (r:ℂ) := by exact_mod_cast hratio
  · rw [success, hg]
    simp only [coinEmbed]
    ext i j
    rcases i with i | i <;> simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.smul_apply,
      Matrix.zero_apply, smul_eq_mul, mul_zero, ← mul_assoc, hnorm, success]

/-- The source's ceiling choice has positive attenuated success, the exact final
angle, and an explicit reciprocal-square-root query bound. -/
private theorem exact_angle_choice (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let n := ⌈Real.pi / (4 * Real.arcsin (Real.sqrt p)) - 1/2⌉₊
    let r := Real.sin (Real.pi / (4*(n:ℝ)+2)) ^ 2
    0 < r ∧ r ≤ p ∧ r < 1 ∧
    (2*(n:ℝ)+1) * Real.arcsin (Real.sqrt r) = Real.pi/2 ∧
    2*(n:ℝ)+1 ≤ (Real.pi/2+2) / Real.sqrt p := by
  let t := Real.arcsin (Real.sqrt p)
  have ht : 0 < t := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp)
  have ht1 : t < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr ((Real.sqrt_lt hp.le (by norm_num)).mpr (by simpa using hp1))
  have hsin : Real.sin t = Real.sqrt p :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) ((Real.sqrt_le_one).mpr hp1.le)
  have hx : 0 ≤ Real.pi / (4*t) - 1/2 := by
    have := (le_div_iff₀ (show 0 < 4*t by positivity)).mpr (by linarith : (1/2:ℝ)*(4*t) ≤ Real.pi)
    linarith
  let n := ⌈Real.pi/(4*t)-1/2⌉₊
  have hn := Nat.le_ceil (Real.pi/(4*t)-1/2)
  have hn' := Nat.ceil_lt_add_one hx
  change Real.pi/(4*t)-1/2 ≤ (n:ℝ) at hn
  change (n:ℝ) < Real.pi/(4*t)-1/2+1 at hn'
  have hd : 0 < 4*(n:ℝ)+2 := by positivity
  let a := Real.pi/(4*(n:ℝ)+2)
  have ha : 0 < a := div_pos Real.pi_pos hd
  have hat : a ≤ t := by
    apply (div_le_iff₀ hd).mpr
    have := (div_le_iff₀ (show 0 < 4*t by positivity)).mp (by linarith : Real.pi/(4*t) ≤ (n:ℝ)+1/2)
    nlinarith
  have ha1 : a < Real.pi/2 := hat.trans_lt ht1
  have hspos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsle : Real.sin a ≤ Real.sqrt p := by
    rw [← hsin]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht1.le hat
  have hrp : Real.sin a ^ 2 ≤ p := by nlinarith [Real.sq_sqrt hp.le]
  have harc : Real.arcsin (Real.sqrt (Real.sin a ^ 2)) = a := by
    rw [Real.sqrt_sq hspos.le, Real.arcsin_sin (by linarith [Real.pi_pos]) ha1.le]
  have he : (2*(n:ℝ)+1)*a = Real.pi/2 := by dsimp [a]; field_simp; ring
  have hts : Real.sqrt p ≤ t := by rw [← hsin]; exact Real.sin_le ht.le
  have hroot : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hroot1 : Real.sqrt p ≤ 1 := (Real.sqrt_le_one).mpr hp1.le
  have hcount : 2*(n:ℝ)+1 ≤ (Real.pi/2+2)/Real.sqrt p := by
    have heq : Real.pi/(2*t) = 2*(Real.pi/(4*t)) := by field_simp; ring
    have hb : 2*(n:ℝ)+1 < Real.pi/(2*t)+2 := by rw [heq]; linarith
    have hdiv : Real.pi/(2*t) ≤ Real.pi/(2*Real.sqrt p) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
    apply (le_div_iff₀ hroot).mpr
    have hb' : 2*(n:ℝ)+1 ≤ Real.pi/(2*Real.sqrt p)+2 := (hb.trans_le (by linarith)).le
    have := (le_div_iff₀ (show 0 < 2*Real.sqrt p by positivity)).mp (by linarith : 2*(n:ℝ)+1-2 ≤ Real.pi/(2*Real.sqrt p))
    nlinarith
  exact ⟨sq_pos_of_pos hspos, hrp, hrp.trans_lt hp1, by rw [harc]; exact he, hcount⟩


/-- The supplied operations used by the finite coherent circuit. -/
inductive AmplificationGate
  | source | sourceAdjoint | coin | coinAdjoint | initializedReflection | goodReflection
  deriving DecidableEq

/-- Evaluation of a gate never uses the desired successful isometry. -/
def gateMatrix (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (q : ℝ) :
    AmplificationGate → Matrix (l ⊕ l) (l ⊕ l) ℂ
  | .source => coinLift C
  | .sourceAdjoint => (coinLift C)ᴴ
  | .coin => coinRotation q
  | .coinAdjoint => (coinRotation q)ᴴ
  | .initializedReflection => (2:ℂ) • (coinEmbed J * (coinEmbed J)ᴴ) - 1
  | .goodReflection => 1 - (2:ℂ) • coinGood P

/-- Words are written in matrix-product order, so the rightmost gate acts first. -/
def evaluateWord (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (q : ℝ)
    (w : List AmplificationGate) : Matrix (l ⊕ l) (l ⊕ l) ℂ :=
  (w.map (gateMatrix J C P q)).prod

/-- Each iterate conjugates the fixed initialization reflection by the prepared circuit. -/
def reflectionBlock : List AmplificationGate :=
  [.coin, .source, .initializedReflection, .sourceAdjoint, .coinAdjoint, .goodReflection]

/-- A finite circuit, initially preparing the source and then applying n iterates. -/
def amplificationWord : ℕ → List AmplificationGate
  | 0 => [.coin, .source]
  | n+1 => reflectionBlock ++ amplificationWord n

/-- Only original forward and inverse source calls contribute to this query count. -/
def sourceQueries (w : List AmplificationGate) : ℕ :=
  w.count .source + w.count .sourceAdjoint

private theorem word_semantics (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (q : ℝ)
    (hD : (coinRotation q * coinLift C)ᴴ * (coinRotation q * coinLift C) = 1)
    (n : ℕ) :
    evaluateWord J C P q (amplificationWord n) * coinEmbed J =
      iterate ((coinRotation q * coinLift C) * coinEmbed J) (coinGood P) ^ n *
        ((coinRotation q * coinLift C) * coinEmbed J) ∧
    sourceQueries (amplificationWord n) = 2*n+1 := by
  let D := coinRotation (l := l) q * coinLift C
  let K := coinEmbed J
  let G := coinGood P
  have hDD : D*Dᴴ = 1 := mul_eq_one_comm.mp hD
  have he : evaluateWord J C P q reflectionBlock = iterate (D*K) G := by
    simp only [evaluateWord, reflectionBlock, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Matrix.mul_one, gateMatrix]
    change coinRotation q * (coinLift C * (((2:ℂ) • (K*Kᴴ)-1) *
      ((coinLift C)ᴴ * ((coinRotation q)ᴴ * (1-(2:ℂ) • G))))) = _
    have hconj : D * ((2:ℂ) • (K*Kᴴ)-1) * Dᴴ = (2:ℂ) • ((D*K)*(D*K)ᴴ)-1 := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc] at hDD ⊢
      rw [hDD]
    calc
      _ = (D * ((2:ℂ) • (K*Kᴴ)-1) * Dᴴ) * (1-(2:ℂ) • G) := by
        simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = iterate (D*K) G := by rw [hconj]; rfl
  induction n with
  | zero => simp [amplificationWord, evaluateWord, gateMatrix, sourceQueries]
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · simp only [amplificationWord, evaluateWord, List.map_append, List.prod_append]
      change (evaluateWord J C P q reflectionBlock *
        evaluateWord J C P q (amplificationWord n)) * coinEmbed J = _
      rw [Matrix.mul_assoc, ih.1, he, pow_succ']
      simp only [D, K, G, Matrix.mul_assoc]
    · have hc := ih.2
      simp [amplificationWord, sourceQueries, List.count_append, reflectionBlock] at hc ⊢
      omega

private theorem word_unitary (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (q : ℝ)
    (hJ : Jᴴ*J = 1) (hC : Cᴴ*C = 1) (hP : Pᴴ = P) (hPP : P*P = P)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (w : List AmplificationGate) :
    (evaluateWord J C P q w)ᴴ * evaluateWord J C P q w = 1 := by
  have hK : (coinEmbed J)ᴴ * coinEmbed J = 1 := by
    simp [coinEmbed, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hJ]
  have hL : (coinLift C)ᴴ * coinLift C = 1 := by
    simp [coinLift, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hC,
      Matrix.fromBlocks_one]
  have hG : (coinGood P)ᴴ = coinGood P := by
    simp [coinGood, Matrix.fromBlocks_conjTranspose, hP]
  have hGG : coinGood P * coinGood P = coinGood P := by
    simp [coinGood, Matrix.fromBlocks_multiply, hPP]
  have href (E : Matrix (l ⊕ l) (l ⊕ l) ℂ) (hE : Eᴴ = E) (hEE : E*E = E) :
      ((2:ℂ) • E - 1)ᴴ * ((2:ℂ) • E - 1) = 1 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hE, show star (2:ℂ) = (2:ℂ) by norm_num, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hEE, smul_smul]
    module
  have hinit := href (coinEmbed J * (coinEmbed J)ᴴ)
    (by simp [Matrix.conjTranspose_mul]) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (coinEmbed J)ᴴ, hK, Matrix.one_mul])
  have hgood : (1-(2:ℂ) • coinGood P)ᴴ * (1-(2:ℂ) • coinGood P) = 1 := by
    have he : 1-(2:ℂ) • coinGood P = -((2:ℂ) • coinGood P-1) := by module
    rw [he, Matrix.conjTranspose_neg, neg_mul_neg]
    exact href _ hG hGG
  have hu (g : AmplificationGate) : (gateMatrix J C P q g)ᴴ * gateMatrix J C P q g = 1 := by
    cases g with
    | source => exact hL
    | sourceAdjoint => simpa [gateMatrix] using (mul_eq_one_comm.mp hL)
    | coin => exact coin_unitary q hq hq1
    | coinAdjoint => simpa [gateMatrix] using (mul_eq_one_comm.mp (coin_unitary (l := l) q hq hq1))
    | initializedReflection => exact hinit
    | goodReflection => exact hgood
  induction w with
  | nil => simp [evaluateWord]
  | cons g w ih =>
    change (gateMatrix J C P q g * evaluateWord J C P q w)ᴴ *
      (gateMatrix J C P q g * evaluateWord J C P q w) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gateMatrix J C P q g)ᴴ, hu, Matrix.one_mul, ih]

/-- The exact known-probability coherent circuit is one common finite word on
all source columns, with strictly zero failure and the same identity on every
reference extension. No unknown input vector occurs in its gates. -/
theorem exact_coherent_amplification
    (J : Matrix l s ℂ) (C P : Matrix l l ℂ) (p : ℝ)
    (hJ : Jᴴ*J = 1) (hC : Cᴴ*C = 1) (hP : Pᴴ = P) (hPP : P*P = P)
    (hA : (P*(C*J))ᴴ*(P*(C*J)) = (p:ℂ) • (1 : Matrix s s ℂ))
    (hp : 0 < p) (hp1 : p ≤ 1) :
    let n := ⌈Real.pi/(4*Real.arcsin (Real.sqrt p))-1/2⌉₊
    let r := Real.sin (Real.pi/(4*(n:ℝ)+2))^2
    let q := r/p
    let w := if p = 1 then [AmplificationGate.source] else amplificationWord n
    let V := evaluateWord J C P q w * coinEmbed J
    V = coinEmbed (success (C*J) P p) ∧
    (1-coinGood P)*V = 0 ∧
    (∀ (z : Type*) (R : Matrix z z ℂ),
      V ⊗ₖ R = coinEmbed (success (C*J) P p) ⊗ₖ R) ∧
    (sourceQueries w : ℝ) ≤ (Real.pi/2+2)/Real.sqrt p ∧
    (evaluateWord J C P q w)ᴴ * evaluateWord J C P q w = 1 ∧
    (if p = 1 then sourceQueries w = 1 else
      0 < r ∧ r ≤ p ∧ r < 1 ∧ 0 < q ∧ q ≤ 1 ∧
      (2*(n:ℝ)+1)*Real.arcsin (Real.sqrt r) = Real.pi/2 ∧
      sourceQueries w = 2*n+1 ∧
      (coinRotation (l := l) q)ᴴ*coinRotation q = 1 ∧
      success ((coinRotation q*coinLift C)*coinEmbed J) (coinGood P) r =
        coinEmbed (success (C*J) P p)) := by
  classical
  dsimp only
  let n := ⌈Real.pi/(4*Real.arcsin (Real.sqrt p))-1/2⌉₊
  let r := Real.sin (Real.pi/(4*(n:ℝ)+2))^2
  have hPV : coinGood P * coinEmbed (success (C*J) P p) =
      coinEmbed (success (C*J) P p) := by
    simp only [coinGood, coinEmbed, Matrix.fromBlocks_mul_fromRows,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, success,
      Matrix.mul_smul, ← Matrix.mul_assoc P P, hPP, smul_zero]
  have hfail : (1-coinGood P)*coinEmbed (success (C*J) P p) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPV, sub_self]
  by_cases hpone : p = 1
  · subst p
    have hbase := uniform_operator_rotation.{_,_,0} J C P 1 hJ hC hP hPP hA (by norm_num) (by norm_num)
    simp only [ite_true] at hbase ⊢
    have hv : evaluateWord J C P (r/1) [.source] * coinEmbed J =
        coinEmbed (success (C*J) P 1) := by
      simpa [evaluateWord, gateMatrix, coinLift, coinEmbed,
        Matrix.fromBlocks_mul_fromRows] using congrArg coinEmbed hbase
    rw [hv]
    refine ⟨rfl, hfail, fun _ _ => rfl, ?_, ?_, ?_⟩
    · norm_num [sourceQueries]
      linarith [Real.pi_pos]
    · simpa [evaluateWord, gateMatrix, coinLift, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_one, hC]
    · norm_num [sourceQueries]
  · have hplt : p < 1 := lt_of_le_of_ne hp1 hpone
    obtain ⟨hr, hrp, hr1, ha, hbound⟩ := exact_angle_choice p hp hplt
    change 0 < r at hr
    change r ≤ p at hrp
    change r < 1 at hr1
    change (2*(n:ℝ)+1)*Real.arcsin (Real.sqrt r) = Real.pi/2 at ha
    change 2*(n:ℝ)+1 ≤ (Real.pi/2+2)/Real.sqrt p at hbound
    obtain ⟨hK, hD, hG, hGG, hGram, hsuccess⟩ :=
      coin_data J C P p r hp hr hrp hJ hC hP hPP hA
    obtain ⟨hsem, hcount⟩ := word_semantics J C P (r/p) hD n
    have hrot := uniform_operator_rotation.{_,_,0} (coinEmbed J)
      (coinRotation (r/p)*coinLift C) (coinGood P) r
      hK hD hG hGG hGram hr hr1.le
    dsimp only at hrot
    rw [if_neg (ne_of_lt hr1)] at hrot
    have hrotN := (hrot.2.2.2 n).1
    rw [ha, Real.sin_pi_div_two, Real.cos_pi_div_two] at hrotN
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero] at hrotN
    have hv := hsem.trans (hrotN.trans hsuccess)
    simp only [hpone, ↓reduceIte]
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    rw [hv]
    refine ⟨rfl, hfail, fun _ _ => rfl, ?_, ?_, ?_⟩
    · rw [hcount]
      exact_mod_cast hbound
    · exact word_unitary J C P (r/p) hJ hC hP hPP (div_pos hr hp).le
        ((div_le_one hp).mpr hrp) _
    · exact ⟨hr, hrp, hr1, div_pos hr hp, (div_le_one hp).mpr hrp,
        ha, hcount, coin_unitary (r/p) (div_pos hr hp).le ((div_le_one hp).mpr hrp), hsuccess⟩

#print axioms exact_coherent_amplification

end D5.S3.Quantum.Recovery.CoherentUniformAmplification
