/- GID: D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Characteristic-three finite-field Weyl-Heisenberg orbits with a uniform positive projector-Gram floor. -/

/-
proof_shape: result: bind-only. Every private theorem is bind-only and lies on the proof path of
  result (CLAUDE.md §3.2, consumed helpers): the character facts ψ_eq, ψ_add, ψ_zero, ψ_norm, ψ_star,
  ψ_sum, ψ_cube, ψ_one_add_lower; the displacement algebra D_mulVec, D_mul, D_adjoint, D_zero,
  D_unitary, D_trace, D_orthogonal, D_conjugation; the Gram reduction proj_selfAdjoint,
  proj_coefficient, flat_inner, gram_form, DV_orthonormal, DV_coefficient, gram_fourier, κ_sum,
  κ_orthogonal, KV_orthonormal, fourier_norm; the witness bounds sqrt_data, witness_norm,
  spike_ambiguity, witness_ambiguity, shifted_root_lower, witness_floor, witness_gram_lower and
  uniform_floor.
escape_witness: none.
admission_basis: open-problem-resolution (#13556; Proved)
Direct frozen dependencies: none; only pinned Mathlib is imported.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open scoped BigOperators Matrix ComplexConjugate

set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Measurement.CharacteristicThreeUniformWeylHeisenbergStability

attribute [local instance] Classical.propDecidable

abbrev F (r : ℕ) := GaloisField 3 r

noncomputable instance fintypeF (r : ℕ) : Fintype (F r) := Fintype.ofFinite (F r)

def psi {r : ℕ} (x : F r) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace (ZMod 3) (F r) x).val : ℂ) / 3)

def D {r : ℕ} (a b : F r) : Matrix (F r) (F r) ℂ :=
  by classical exact fun y x => if y = x + a then psi (b * x) else 0

def proj {r : ℕ} (φ : F r → ℂ) (g : F r × F r) : Matrix (F r) (F r) ℂ :=
  by
    classical
    exact D g.1 g.2 * Matrix.vecMulVec φ (star φ) * (D g.1 g.2)ᴴ

def gram {r : ℕ} (φ : F r → ℂ) : Matrix (F r × F r) (F r × F r) ℂ :=
  by
    classical
    exact fun u v => Matrix.trace (proj φ u * proj φ v)

def StableWith {r : ℕ} (φ : F r → ℂ) (c : ℝ) : Prop :=
  by
    classical
    exact ∀ w : F r × F r → ℂ, ∑ g, w g = 0 →
      c * ∑ g, ‖w g‖ ^ 2 ≤ (star w ⬝ᵥ (gram φ).mulVec w).re

def claim : Prop := ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∃ φ : F r → ℂ,
  ∑ x, ‖φ x‖ ^ 2 = 1 ∧ StableWith φ (c * (3 ^ r : ℝ) / (3 ^ r + 1))

private def χ (r : ℕ) : AddChar (F r) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod 3) (F r)).toAddMonoidHom

private theorem ψ_eq {r : ℕ} (x : F r) : psi x = χ r x := by
  simp only [χ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
    ZMod.stdAddChar_apply, ZMod.toCircle_apply, psi]
  norm_num

private theorem ψ_add {r : ℕ} (x y : F r) : psi (x + y) = psi x * psi y := by
  simp only [ψ_eq, AddChar.map_add_eq_mul]

private theorem ψ_zero {r : ℕ} : psi (0 : F r) = 1 := by
  simp only [ψ_eq, AddChar.map_zero_eq_one]

private theorem ψ_norm {r : ℕ} (x : F r) : ‖psi x‖ = 1 := by
  rw [ψ_eq]
  change ‖(ZMod.toCircle (Algebra.trace (ZMod 3) (F r) x) : ℂ)‖ = 1
  exact Circle.norm_coe _

private theorem ψ_star {r : ℕ} (x : F r) : star (psi x) = psi (-x) := by
  rw [ψ_eq, ψ_eq, AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (by simpa only [← ψ_eq] using ψ_norm x)).symm

private theorem ψ_sum {r : ℕ} (c : F r) :
    ∑ x, psi (c * x) = if c = 0 then (Fintype.card (F r) : ℂ) else 0 := by
  classical
  have hn : χ r ≠ 1 := by
    have ht : ∃ b : F r, Algebra.trace (ZMod 3) (F r) b ≠ 0 := by
      by_contra! h
      apply one_ne_zero (α := F r)
      apply (traceForm_nondegenerate (ZMod 3) (F r)).1 (1 : F r)
      simpa only [Algebra.traceForm_apply, one_mul] using h
    obtain ⟨b, hb⟩ := ht
    apply AddChar.ne_one_iff.mpr
    refine ⟨b, ?_⟩
    intro he
    apply hb
    apply ZMod.injective_stdAddChar
    simpa only [χ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
      AddChar.map_zero_eq_one] using he
  simpa only [ψ_eq, mul_comm c, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift c (AddChar.IsPrimitive.of_ne_one hn)

private theorem ψ_cube {r : ℕ} (x : F r) : psi x ^ 3 = 1 := by
  rw [ψ_eq]
  change ZMod.stdAddChar (Algebra.trace (ZMod 3) (F r) x) ^ 3 = 1
  rw [← AddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]

private theorem ψ_one_add_lower {r : ℕ} (x : F r) : 1 ≤ ‖1 + psi x‖ ^ 2 := by
  have hz : Complex.normSq (psi x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, ψ_norm]
    norm_num
  by_cases hx : psi x = 1
  · norm_num [hx]
  have hn : psi x ≠ 0 := by
    intro h
    simpa [h] using ψ_norm x
  have hs : star (psi x) = psi x ^ 2 := by
    apply mul_right_cancel₀ hn
    calc star (psi x) * psi x = 1 := by
           change (starRingEnd ℂ) (psi x) * psi x = 1
           rw [← Complex.normSq_eq_conj_mul_self, hz]
           rfl
         _ = psi x ^ 2 * psi x := by simpa only [pow_succ] using (ψ_cube x).symm
  have hp : psi x ^ 2 + psi x + 1 = 0 := by
    have hf : (psi x - 1) * (psi x ^ 2 + psi x + 1) = 0 := by
      calc _ = psi x ^ 3 - 1 := by ring
           _ = 0 := by rw [ψ_cube]; ring
    exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hx)
  have he : psi x + star (psi x) = -1 := by
    calc _ = (psi x ^ 2 + psi x + 1) - 1 := by rw [hs]; ring
         _ = -1 := by rw [hp]; ring
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.neg_re,
    Complex.one_re] at hre
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_one, hz]
  simp only [one_mul, Complex.conj_re]
  linarith

private def q (r : ℕ) : ℝ := Fintype.card (F r)

private def s (r : ℕ) : ℝ := Real.sqrt (q r)

private theorem sqrt_data (r : ℕ) : 0 < s r ∧ s r ^ 2 = q r := by
  have hq : 0 < q r := by
    change 0 < (Fintype.card (F r) : ℝ)
    exact_mod_cast (Fintype.card_pos (α := F r))
  exact ⟨Real.sqrt_pos.mpr hq, Real.sq_sqrt hq.le⟩

private def witness (r : ℕ) (x : F r) : ℂ :=
  ((1 / s r + if x = 0 then 1 else 0 : ℝ) : ℂ) /
    (Real.sqrt (2 + 2 / s r) : ℂ)

private theorem witness_norm (r : ℕ) : ∑ x, ‖witness r x‖ ^ 2 = 1 := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hd : 0 < 2 + 2 / s r := by positivity
  have hden : Real.sqrt (2 + 2 / s r) ^ 2 = 2 + 2 / s r :=
    Real.sq_sqrt hd.le
  have he (x : F r) :
      (1 / s r + if x = 0 then 1 else 0 : ℝ) ^ 2 =
        (1 / s r) ^ 2 + if x = 0 then 2 / s r + 1 else 0 := by
    by_cases hx : x = 0 <;> simp only [hx, ite_true, ite_false] <;> ring
  have hsum : ∑ x : F r, (1 / s r + if x = 0 then 1 else 0 : ℝ) ^ 2 =
      q r * (1 / s r) ^ 2 + 2 / s r + 1 := by
    simp_rw [he]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [q, add_assoc]
  have ht : q r * (1 / s r) ^ 2 = 1 := by
    rw [← hsq]
    field_simp
  simp only [← Complex.normSq_eq_norm_sq, witness, Complex.normSq_div,
    Complex.normSq_ofReal, ← pow_two]
  rw [hden, ← Finset.sum_div, hsum, ht]
  field_simp
  ring

private theorem D_mulVec {r : ℕ} (a b : F r) (v : F r → ℂ) (y : F r) :
    (D a b).mulVec v y = psi (b * (y - a)) * v (y - a) := by
  have he (x : F r) : y = x + a ↔ x = y - a := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  simp only [Matrix.mulVec, dotProduct, D, ite_mul, zero_mul, he,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def spike {r : ℕ} (t : ℝ) (x : F r) : ℂ := t + if x = 0 then 1 else 0

private theorem spike_ambiguity {r : ℕ} (t : ℝ) (a b : F r) :
    star (spike t) ⬝ᵥ (D a b).mulVec (spike t) =
      (t : ℂ) ^ 2 * (if b = 0 then (Fintype.card (F r) : ℂ) else 0) +
        (if a = 0 then 1 else 0) + t * (1 + psi (-a * b)) := by
  have hr : (star (spike t) ⬝ᵥ (D a b).mulVec (spike t)) =
      ∑ x : F r, star (spike t (x + a)) * psi (b * x) * spike t x := by
    simp only [dotProduct, Pi.star_apply, D_mulVec]
    symm
    apply Fintype.sum_bijective (fun x : F r => x + a) (AddGroup.addRight_bijective a)
    intro x
    simp only [add_sub_cancel_right, mul_assoc]
  have he (x : F r) : star (spike t (x + a)) * psi (b * x) * spike t x =
      (t : ℂ) ^ 2 * psi (b * x) + (if x = 0 then (t : ℂ) else 0) +
        (if x = -a then (t : ℂ) * psi (-a * b) else 0) +
        (if x = 0 then (if a = 0 then (1 : ℂ) else 0) else 0) := by
    by_cases hx : x = 0
    · subst x
      by_cases ha : a = 0 <;> simp [spike, ha, ψ_zero] <;> ring
    · by_cases hxa : x = -a
      · have ha : a ≠ 0 := by intro ha; apply hx; simpa [ha] using hxa
        rw [hxa]
        simp [spike, ha, show b * -a = -a * b by ring]
        ring
      · have hxa' : x + a ≠ 0 := by
          intro h
          apply hxa
          calc x = x + a - a := by simp
               _ = -a := by rw [h]; simp
        simp [spike, hx, hxa, hxa']
        ring
  rw [hr]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ψ_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private def A {r : ℕ} (v : F r → ℂ) (h : F r × F r) : ℂ :=
  star v ⬝ᵥ (D h.1 h.2).mulVec v

private theorem witness_ambiguity {r : ℕ} (a b : F r) :
    A (witness r) (a, b) =
      ((if b = 0 then 1 else 0) + (if a = 0 then 1 else 0) +
        (1 + psi (-a * b)) / (s r : ℂ)) / (2 + 2 / (s r : ℂ)) := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hd : 0 < 2 + 2 / s r := by positivity
  let n := Real.sqrt (2 + 2 / s r)
  have hn : (n : ℂ) ^ 2 = 2 + 2 / (s r : ℂ) := by
    have he := Real.sq_sqrt hd.le
    change n ^ 2 = 2 + 2 / s r at he
    exact_mod_cast he
  have hf : witness r = (n : ℂ)⁻¹ • (spike (1 / s r) : F r → ℂ) := by
    ext x
    by_cases hx : x = 0 <;>
      simp [witness, spike, n, hx, div_eq_mul_inv, mul_comm]
  have hscale : A (witness r) (a, b) =
      (star (spike (1 / s r)) ⬝ᵥ (D a b).mulVec (spike (1 / s r))) /
        (n : ℂ) ^ 2 := by
    have hns : star ((n : ℂ)⁻¹) = (n : ℂ)⁻¹ := by simp
    simp only [A, hf, Matrix.mulVec_smul, star_smul, hns,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have ht : ((1 / s r : ℝ) : ℂ) ^ 2 * (Fintype.card (F r) : ℂ) = 1 := by
    have he : (1 / s r) ^ 2 * q r = 1 := by rw [← hsq]; field_simp
    unfold q at he
    exact_mod_cast he
  rw [hscale, spike_ambiguity, hn]
  by_cases hb : b = 0
  · simp only [hb, ↓reduceIte]
    rw [ht]
    push_cast
    ring
  · simp only [hb, ↓reduceIte, mul_zero, zero_add, Complex.ofReal_div, Complex.ofReal_one]
    ring

private theorem shifted_root_lower {r : ℕ} (x : F r) (t d : ℝ)
    (ht : 0 ≤ t) (hd : 0 ≤ d) : t ^ 2 ≤ ‖(d : ℂ) + t * (1 + psi x)‖ ^ 2 := by
  have hp := ψ_one_add_lower x
  rw [← Complex.normSq_eq_norm_sq] at hp
  have hz : Complex.normSq (psi x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, ψ_norm]
    norm_num
  have hre : 0 ≤ (1 + psi x).re := by
    have hh := hp
    rw [Complex.normSq_add, Complex.normSq_one, hz] at hh
    simp only [one_mul, Complex.conj_re] at hh
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg t)
  have hc := mul_nonneg hd (mul_nonneg ht hre)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    zero_mul, sub_zero]
  nlinarith [sq_nonneg d]

private theorem witness_floor {r : ℕ} (h : F r × F r) :
    1 / (4 * (s r + 1) ^ 2) ≤ ‖A (witness r) h‖ ^ 2 := by
  obtain ⟨hs, _⟩ := sqrt_data r
  rcases h with ⟨a, b⟩
  let t : ℝ := 1 / s r
  let d : ℝ := (if b = 0 then 1 else 0) + (if a = 0 then 1 else 0)
  have ht : 0 < t := by dsimp [t]; positivity
  have hd : 0 ≤ d := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [d, ha, hb]
  have hdc : (d : ℂ) = (if b = 0 then 1 else 0) + (if a = 0 then 1 else 0) := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [d, ha, hb]
  have hf : A (witness r) (a, b) =
      ((d : ℂ) + t * (1 + psi (-a * b))) / ((2 + 2 * t : ℝ) : ℂ) := by
    rw [witness_ambiguity, hdc]
    dsimp [t]
    push_cast
    ring
  have hb := shifted_root_lower (-a * b) t d ht.le hd
  rw [hf, ← Complex.normSq_eq_norm_sq, Complex.normSq_div, Complex.normSq_ofReal,
    ← pow_two]
  rw [← Complex.normSq_eq_norm_sq] at hb
  have hn : 0 < (2 + 2 * t) ^ 2 := by positivity
  have he : t ^ 2 / (2 + 2 * t) ^ 2 = 1 / (4 * (s r + 1) ^ 2) := by
    dsimp [t]
    field_simp
    ring
  rw [← he]
  exact div_le_div_of_nonneg_right hb hn.le

private theorem D_mul {r : ℕ} (a b c d : F r) :
    D a b * D c d = psi (b * c) • D (a + c) (b + d) := by
  ext y x
  simp only [Matrix.mul_apply, D, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.smul_apply, smul_eq_mul]
  rw [show x + c + a = x + (a + c) by ring]
  by_cases h : y = x + (a + c)
  · simp only [h, ↓reduceIte, mul_add, add_mul, ψ_add]
    ring
  · simp only [h, ↓reduceIte, zero_mul]

private theorem D_adjoint {r : ℕ} (a b : F r) :
    (D a b)ᴴ = psi (a * b) • D (-a) (-b) := by
  ext y x
  simp only [Matrix.conjTranspose_apply, D, Matrix.smul_apply, smul_eq_mul]
  have he : x = y + a ↔ y = x + -a := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  rw [he]
  by_cases hy : y = x + -a
  · simp only [hy, ↓reduceIte, ψ_star]
    rw [← ψ_add]
    congr 1
    ring
  · simp only [hy, ↓reduceIte, star_zero, mul_zero]

private theorem D_zero {r : ℕ} : D (0 : F r) 0 = 1 := by
  ext y x
  simp only [D, add_zero, zero_mul, ψ_zero, Matrix.one_apply]

private theorem D_unitary {r : ℕ} (a b : F r) :
    (D a b)ᴴ * D a b = 1 ∧ D a b * (D a b)ᴴ = 1 := by
  constructor
  · rw [D_adjoint, Matrix.smul_mul, D_mul, smul_smul]
    rw [← ψ_add, show a * b + -b * a = 0 by ring, ψ_zero]
    simp only [neg_add_cancel, D_zero, one_smul]
  · rw [D_adjoint, Matrix.mul_smul, D_mul, smul_smul]
    rw [← ψ_add, show a * b + b * -a = 0 by ring, ψ_zero]
    simp only [add_neg_cancel, D_zero, one_smul]

private theorem D_trace {r : ℕ} (a b : F r) :
    Matrix.trace (D a b) =
      if a = 0 then (if b = 0 then (Fintype.card (F r) : ℂ) else 0) else 0 := by
  have he (x : F r) : x = x + a ↔ a = 0 := by
    constructor
    · intro h
      have hh := congrArg (fun y : F r => y - x) h
      simpa using hh.symm
    · intro h; simp [h]
  simp only [Matrix.trace, Matrix.diag_apply, D, he]
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte, ψ_sum]
  · simp only [ha, ↓reduceIte, Finset.sum_const_zero]

private theorem D_orthogonal {r : ℕ} (h k : F r × F r) :
    Matrix.trace ((D h.1 h.2)ᴴ * D k.1 k.2) =
      if h = k then (Fintype.card (F r) : ℂ) else 0 := by
  rcases h with ⟨a, b⟩
  rcases k with ⟨c, d⟩
  simp only [D_adjoint, Matrix.smul_mul, D_mul, Matrix.trace_smul, smul_eq_mul]
  rw [← mul_assoc, ← ψ_add, D_trace]
  rw [show a * b + -b * c = b * (a - c) by ring]
  by_cases ha : a = c <;> by_cases hb : b = d <;>
    simp [ha, hb, neg_add_eq_sub, sub_eq_zero, eq_comm, ψ_zero]

private def κ {r : ℕ} (h g : F r × F r) : ℂ := psi (g.2 * h.1 - g.1 * h.2)

private theorem D_conjugation {r : ℕ} (h g : F r × F r) :
    D g.1 g.2 * D h.1 h.2 * (D g.1 g.2)ᴴ = κ h g • D h.1 h.2 := by
  rcases h with ⟨c, d⟩
  rcases g with ⟨a, b⟩
  simp only [D_adjoint, Matrix.mul_smul, Matrix.smul_mul, D_mul, smul_smul]
  rw [show a + c + -a = c by ring, show b + d + -b = d by ring]
  simp only [← ψ_add, κ]
  congr 2
  ring

private theorem proj_selfAdjoint {r : ℕ} (v : F r → ℂ) (g : F r × F r) :
    (proj v g)ᴴ = proj v g := by
  simp only [proj, Matrix.conjTranspose_mul, Matrix.conjTranspose_vecMulVec,
    star_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem proj_coefficient {r : ℕ} (v : F r → ℂ) (h g : F r × F r) :
    Matrix.trace ((D h.1 h.2)ᴴ * proj v g) = κ h g * star (A v h) := by
  let G := D g.1 g.2
  let H := D h.1 h.2
  let R := Matrix.vecMulVec v (star v)
  have hG : Gᴴ * G = 1 := (D_unitary g.1 g.2).1
  have hc : κ h g * star (κ h g) = 1 := by
    simp only [κ, ψ_star, ← ψ_add, add_neg_cancel, ψ_zero]
  have hscov : G * Hᴴ * Gᴴ = star (κ h g) • Hᴴ := by
    have he := congrArg (fun M : Matrix (F r) (F r) ℂ => Mᴴ) (D_conjugation h g)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.mul_assoc] using he
  have hcov : Gᴴ * Hᴴ * G = κ h g • Hᴴ := by
    calc Gᴴ * Hᴴ * G = κ h g • (Gᴴ * (star (κ h g) • Hᴴ) * G) := by
           simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hc, one_smul]
         _ = κ h g • (Gᴴ * (G * Hᴴ * Gᴴ) * G) := by rw [← hscov]
         _ = κ h g • Hᴴ := by
           congr 1
           calc Gᴴ * (G * Hᴴ * Gᴴ) * G = (Gᴴ * G) * Hᴴ * (Gᴴ * G) := by
                  simp only [Matrix.mul_assoc]
                _ = Hᴴ := by rw [hG, Matrix.one_mul, Matrix.mul_one]
  have hR : Rᴴ = R := by
    simp only [R, Matrix.conjTranspose_vecMulVec, star_star]
  have hb : Matrix.trace (H * R) = A v h := by
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  have hb' : Matrix.trace (Hᴴ * R) = star (A v h) := by
    calc Matrix.trace (Hᴴ * R) = Matrix.trace ((R * H)ᴴ) := by
           rw [Matrix.conjTranspose_mul, hR]
         _ = star (Matrix.trace (R * H)) := Matrix.trace_conjTranspose _
         _ = star (A v h) := by rw [Matrix.trace_mul_comm, hb]
  change Matrix.trace (Hᴴ * (G * R * Gᴴ)) = _
  calc Matrix.trace (Hᴴ * (G * R * Gᴴ)) =
         Matrix.trace ((Hᴴ * G * R) * Gᴴ) := by simp only [Matrix.mul_assoc]
       _ = Matrix.trace (Gᴴ * (Hᴴ * G * R)) := Matrix.trace_mul_comm _ _
       _ = Matrix.trace ((Gᴴ * Hᴴ * G) * R) := by simp only [Matrix.mul_assoc]
       _ = κ h g * Matrix.trace (Hᴴ * R) := by
         rw [hcov, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
       _ = κ h g * star (A v h) := by rw [hb']

private def flat {r : ℕ} :
    Matrix (F r) (F r) ℂ →ₗ[ℂ] EuclideanSpace ℂ (F r × F r) where
  toFun M := WithLp.toLp 2 (fun h => M h.1 h.2)
  map_add' M N := by ext h; rfl
  map_smul' c M := by ext h; rfl

private theorem flat_inner {r : ℕ} (M N : Matrix (F r) (F r) ℂ) :
    inner ℂ (flat M) (flat N) = Matrix.trace (Mᴴ * N) := by
  change inner ℂ (WithLp.toLp 2 (fun h : F r × F r => M h.1 h.2))
    (WithLp.toLp 2 (fun h : F r × F r => N h.1 h.2)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

private theorem gram_form {r : ℕ} (v : F r → ℂ) (w : F r × F r → ℂ) :
    (star w ⬝ᵥ (gram v).mulVec w).re = ‖flat (∑ g, w g • proj v g)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, flat_inner, proj_selfAdjoint, gram, Matrix.mulVec,
    dotProduct, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  simp only [Complex.star_def]
  ring

private def DV {r : ℕ} (h : F r × F r) : EuclideanSpace ℂ (F r × F r) :=
  (s r : ℂ)⁻¹ • flat (D h.1 h.2)

private theorem DV_orthonormal (r : ℕ) : Orthonormal ℂ (@DV r) := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hc : (s r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsqc : (s r : ℂ) ^ 2 = (Fintype.card (F r) : ℂ) := by
    unfold q at hsq
    exact_mod_cast hsq
  apply orthonormal_iff_ite.mpr
  intro h k
  simp only [DV, inner_smul_left, inner_smul_right, flat_inner, D_orthogonal]
  have hstar : (starRingEnd ℂ) ((s r : ℂ)⁻¹) = (s r : ℂ)⁻¹ := by simp
  rw [hstar]
  by_cases he : h = k
  · simp only [he, ↓reduceIte]
    rw [← hsqc]
    field_simp
  · simp only [he, ↓reduceIte, mul_zero]

private theorem κ_sum {r : ℕ} (h : F r × F r) :
    ∑ g, κ h g = if h = 0 then (Fintype.card (F r) : ℂ) ^ 2 else 0 := by
  rcases h with ⟨c, d⟩
  have he (a b : F r) : b * c - a * d = (-d) * a + c * b := by ring
  simp only [κ, Fintype.sum_prod_type]
  simp_rw [he, ψ_add]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ψ_sum]
  by_cases hc : c = 0 <;> by_cases hd : d = 0 <;>
    simp [hc, hd, Prod.ext_iff, pow_two]

private theorem κ_orthogonal {r : ℕ} (h k : F r × F r) :
    ∑ g, star (κ h g) * κ k g =
      if h = k then (Fintype.card (F r) : ℂ) ^ 2 else 0 := by
  have he (g : F r × F r) : star (κ h g) * κ k g = κ (k - h) g := by
    simp only [κ, ψ_star, ← ψ_add]
    change psi (-(g.2 * h.1 - g.1 * h.2) + (g.2 * k.1 - g.1 * k.2)) =
      psi (g.2 * (k.1 - h.1) - g.1 * (k.2 - h.2))
    congr 1
    ring
  simp_rw [he]
  rw [κ_sum]
  simp only [sub_eq_zero, eq_comm]

private def KV {r : ℕ} (h : F r × F r) : EuclideanSpace ℂ (F r × F r) :=
  (q r : ℂ)⁻¹ • WithLp.toLp 2 (fun g => star (κ h g))

private theorem KV_orthonormal (r : ℕ) : Orthonormal ℂ (@KV r) := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hq : 0 < q r := by rw [← hsq]; positivity
  have hc : (q r : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqc : (Fintype.card (F r) : ℂ) = (q r : ℂ) := by simp only [q, Complex.ofReal_natCast]
  have hi (h k : F r × F r) :
      inner ℂ (WithLp.toLp 2 (fun g => star (κ h g)))
        (WithLp.toLp 2 (fun g => star (κ k g))) = ∑ g, star (κ k g) * κ h g := by
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    apply Finset.sum_congr rfl
    intro g _
    simp
  apply orthonormal_iff_ite.mpr
  intro h k
  simp only [KV, inner_smul_left, inner_smul_right, hi, κ_orthogonal, hqc]
  have hstar : (starRingEnd ℂ) ((q r : ℂ)⁻¹) = (q r : ℂ)⁻¹ := by simp
  rw [hstar]
  by_cases he : h = k
  · simp only [he, ↓reduceIte]
    field_simp
  · simp only [Ne.symm he, he, ↓reduceIte, mul_zero]

private def fourier {r : ℕ} (w : F r × F r → ℂ) (h : F r × F r) : ℂ :=
  ∑ g, w g * κ h g

private theorem fourier_norm {r : ℕ} (w : F r × F r → ℂ) :
    ∑ h, ‖fourier w h‖ ^ 2 = q r ^ 2 * ∑ g, ‖w g‖ ^ 2 := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hq : 0 < q r := by rw [← hsq]; positivity
  have hk := KV_orthonormal r
  let B : Module.Basis (F r × F r) ℂ (EuclideanSpace ℂ (F r × F r)) :=
    basisOfOrthonormalOfCardEqFinrank hk (by simp)
  have hb : Orthonormal ℂ B := by
    simpa only [B, coe_basisOfOrthonormalOfCardEqFinrank] using hk
  let OB := B.toOrthonormalBasis hb
  have hcoe : (OB : F r × F r → EuclideanSpace ℂ (F r × F r)) = KV := by
    simp only [OB, Module.Basis.coe_toOrthonormalBasis, B,
      coe_basisOfOrthonormalOfCardEqFinrank]
  have hi (h : F r × F r) : inner ℂ (KV h) (WithLp.toLp 2 w) =
      fourier w h / (q r : ℂ) := by
    simp only [KV, inner_smul_left, PiLp.inner_apply, RCLike.inner_apply]
    simp
    simp only [fourier, div_eq_mul_inv]
    ring
  have hp := OB.sum_sq_norm_inner_right (WithLp.toLp 2 w)
  change ∑ h, ‖inner ℂ (OB h) (WithLp.toLp 2 w)‖ ^ 2 = _ at hp
  simp_rw [hcoe, hi, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hq, div_pow] at hp
  rw [← Finset.sum_div, EuclideanSpace.norm_sq_eq] at hp
  have he := (div_eq_iff (pow_ne_zero 2 hq.ne')).mp hp
  simpa only [mul_comm] using he

private theorem DV_coefficient {r : ℕ} (v : F r → ℂ)
    (w : F r × F r → ℂ) (h : F r × F r) :
    inner ℂ (DV h) (flat (∑ g, w g • proj v g)) =
      star (A v h) * fourier w h / (s r : ℂ) := by
  simp only [DV, inner_smul_left, map_sum, map_smul, inner_sum, inner_smul_right,
    flat_inner, proj_coefficient]
  have hstar : (starRingEnd ℂ) ((s r : ℂ)⁻¹) = (s r : ℂ)⁻¹ := by simp
  rw [hstar]
  simp only [fourier, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  ring

private theorem gram_fourier {r : ℕ} (v : F r → ℂ) (w : F r × F r → ℂ) :
    (star w ⬝ᵥ (gram v).mulVec w).re =
      (∑ h, ‖A v h‖ ^ 2 * ‖fourier w h‖ ^ 2) / q r := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hk := DV_orthonormal r
  let B : Module.Basis (F r × F r) ℂ (EuclideanSpace ℂ (F r × F r)) :=
    basisOfOrthonormalOfCardEqFinrank hk (by simp)
  have hb : Orthonormal ℂ B := by
    simpa only [B, coe_basisOfOrthonormalOfCardEqFinrank] using hk
  let OB := B.toOrthonormalBasis hb
  have hcoe : (OB : F r × F r → EuclideanSpace ℂ (F r × F r)) = DV := by
    simp only [OB, Module.Basis.coe_toOrthonormalBasis, B,
      coe_basisOfOrthonormalOfCardEqFinrank]
  have hp := OB.sum_sq_norm_inner_right (flat (∑ g, w g • proj v g))
  change ∑ h, ‖inner ℂ (OB h) (flat (∑ g, w g • proj v g))‖ ^ 2 = _ at hp
  simp_rw [hcoe, DV_coefficient, norm_div, norm_mul, norm_star, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, div_pow, mul_pow, hsq] at hp
  rw [← Finset.sum_div] at hp
  rw [gram_form]
  exact hp.symm

private theorem witness_gram_lower {r : ℕ} (w : F r × F r → ℂ) :
    q r / (4 * (s r + 1) ^ 2) * ∑ g, ‖w g‖ ^ 2 ≤
      (star w ⬝ᵥ (gram (witness r)).mulVec w).re := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hq : 0 < q r := by rw [← hsq]; positivity
  have hsum : ∑ h, (1 / (4 * (s r + 1) ^ 2)) * ‖fourier w h‖ ^ 2 ≤
      ∑ h, ‖A (witness r) h‖ ^ 2 * ‖fourier w h‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro h _
    exact mul_le_mul_of_nonneg_right (witness_floor h) (sq_nonneg _)
  rw [← Finset.mul_sum, fourier_norm] at hsum
  rw [gram_fourier]
  calc q r / (4 * (s r + 1) ^ 2) * ∑ g, ‖w g‖ ^ 2 =
         ((1 / (4 * (s r + 1) ^ 2)) * (q r ^ 2 * ∑ g, ‖w g‖ ^ 2)) / q r := by
           field_simp
       _ ≤ (∑ h, ‖A (witness r) h‖ ^ 2 * ‖fourier w h‖ ^ 2) / q r :=
         div_le_div_of_nonneg_right hsum hq.le

private theorem uniform_floor (r : ℕ) :
    (1 / 8 : ℝ) * q r / (q r + 1) ≤ q r / (4 * (s r + 1) ^ 2) := by
  obtain ⟨hs, hsq⟩ := sqrt_data r
  have hq : 0 < q r := by rw [← hsq]; positivity
  have he : (s r + 1) ^ 2 ≤ 2 * (q r + 1) := by
    nlinarith [sq_nonneg (s r - 1)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left he hq.le]

theorem result : claim := by
  refine ⟨(1 / 8 : ℝ), by norm_num, ?_⟩
  intro r hr
  refine ⟨witness r, witness_norm r, ?_⟩
  intro w _hw
  have hq : q r = (3 ^ r : ℝ) := by
    unfold q
    rw [← Nat.card_eq_fintype_card,
      GaloisField.card (p := 3) (n := r) (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr))]
    norm_cast
  rw [← hq]
  calc (1 / 8 : ℝ) * q r / (q r + 1) * ∑ g, ‖w g‖ ^ 2 ≤
         q r / (4 * (s r + 1) ^ 2) * ∑ g, ‖w g‖ ^ 2 :=
           mul_le_mul_of_nonneg_right (uniform_floor r)
             (Finset.sum_nonneg fun g _ => sq_nonneg ‖w g‖)
       _ ≤ (star w ⬝ᵥ (gram (witness r)).mulVec w).re := witness_gram_lower w

end D5.S3.Quantum.Measurement.CharacteristicThreeUniformWeylHeisenbergStability
