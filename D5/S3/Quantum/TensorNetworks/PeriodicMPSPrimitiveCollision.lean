/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSPrimitiveCollision
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSPrimitiveCollision
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionRank, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity]
   utility: none
   digest: Two-site ambiguity at primitive periodic matrix product states. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionRank
import D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity

/-! The Ising-weight collision of distinct actual trace rays with primitive transfer. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

open Matrix Complex
open scoped Matrix ComplexOrder
open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_cons TwoSiteSpanning)
open PeriodicMPSAmbiguityDensity (changePhysical)
open PeriodicMPSUniformAntisymmetricTransfer (conjugateCore)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal)
open UniformMPSExpectedDimensionRefutation (traceWord)

noncomputable section

private def hadamard : Bond := !![1, 1; 1, -1]
private def xCore (b : Bool) : Fin 2 → Bond := changePhysical ((4 : ℂ)⁻¹ • hadamard) (cores b)

private theorem wordMatrix_mix (U : Bond) (A : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    wordMatrix (changePhysical U A) w =
      ∑ v : Word n, (∏ i, U (w i) (v i)) • wordMatrix A v := by
  induction n with
  | zero => simp [wordMatrix, List.ofFn_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
    simp only [changePhysical, Fin.cons_zero, Finset.sum_mul, Finset.mul_sum,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, Fin.consEquiv, Equiv.coe_fn_mk,
      wordMatrix_cons, Fin.prod_univ_succ, Fin.cons_succ]
    rw [Finset.sum_comm]
    simp only [mul_comm (U _ _)]

private theorem trace_mixing (U : Bond) (A : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    traceWord 2 2 n (changePhysical U A) w =
    ∑ v : Word n, (∏ i, U (w i) (v i)) * traceWord 2 2 n A v := by
  change (wordMatrix (changePhysical U A) w).trace = _
  rw [wordMatrix_mix, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]
  rfl

private theorem mix_proportional {n : ℕ} {c : ℂ}
    (h : traceWord 2 2 n (cores true) = c • traceWord 2 2 n (cores false)) (w : Word n) :
    traceWord 2 2 n (xCore true) w = c * traceWord 2 2 n (xCore false) w := by
  rw [xCore, xCore, trace_mixing, trace_mixing, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  change _ * (c * _) = _
  ring

private def z : ℂ := I / 2
private def virtual : Fin 2 → Bond := ![Matrix.diagonal ![1, z], !![0, z; 1, 0]]

private theorem hadamard_square : hadamard * hadamard = (2 : ℂ) • (1 : Bond) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [hadamard, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem intertwine (i : Fin 2) : hadamard * xCore false i = virtual i * hadamard := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [xCore, ising_cores, virtual, hadamard, z, changePhysical, Matrix.mul_apply,
      Matrix.diagonal_apply, Fin.sum_univ_two] <;> ring

private theorem word_intertwine {n : ℕ} (w : Word n) :
    hadamard * wordMatrix (xCore false) w = wordMatrix virtual w * hadamard := by
  induction n with
  | zero => simp [wordMatrix, List.ofFn_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, wordMatrix_cons, ← mul_assoc, intertwine,
      mul_assoc, ih, mul_assoc]

private theorem virtual_trace {n : ℕ} (w : Word n) :
    traceWord 2 2 n (xCore false) w = (wordMatrix virtual w).trace := by
  change (wordMatrix (xCore false) w).trace = _
  have h := congrArg (fun M : Bond => (M * hadamard).trace) (word_intertwine w)
  change (hadamard * wordMatrix (xCore false) w * hadamard).trace =
    (wordMatrix virtual w * hadamard * hadamard).trace at h
  rw [Matrix.trace_mul_cycle, hadamard_square, Matrix.smul_mul, one_mul,
    Matrix.trace_smul, mul_assoc, hadamard_square, Matrix.mul_smul, mul_one,
    Matrix.trace_smul] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

private def zeros (n : ℕ) : Word n := fun _ => 0
private def twiceMinus (m : ℕ) : Word (m + 3) :=
  Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (zeros m)))

private theorem word_zeros (C : Fin 2 → Bond) (n : ℕ) :
    wordMatrix C (zeros n) = C 0 ^ n := by
  simp [wordMatrix, zeros, List.ofFn_const, List.prod_replicate]

private theorem a0 (m : ℕ) :
    traceWord 2 2 (m + 3) (xCore false) (zeros (m + 3)) = 1 + z ^ (m + 3) := by
  rw [virtual_trace, word_zeros]
  simp [virtual, Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_two]

private theorem a2 (m : ℕ) :
    traceWord 2 2 (m + 3) (xCore false) (twiceMinus m) = z ^ 2 + z ^ (m + 1) := by
  rw [virtual_trace, twiceMinus, wordMatrix_cons, wordMatrix_cons, wordMatrix_cons, word_zeros,
    ← mul_assoc, ← mul_assoc]
  have h : virtual 1 * virtual 0 * virtual 1 = Matrix.diagonal ![z ^ 2, z] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [virtual, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, pow_two]
  rw [h]
  simp [virtual, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Fin.sum_univ_two, pow_succ']

private def phase (i : Fin 2) : ℂ := if i = 0 then 1 - I else 1 + I

private theorem mixed_partner (i : Fin 2) :
    xCore true i = phase i • conjugateCore (xCore false) i := by
  ext j k
  fin_cases i <;>
    simp [xCore, phase, hadamard, changePhysical, partner_core, conjugateCore,
      Matrix.map_apply, Fin.sum_univ_two, map_ofNat] <;> ring

private theorem x_partner_word {n : ℕ} (w : Word n) :
    traceWord 2 2 n (xCore true) w =
      (∏ i, phase (w i)) * star (traceWord 2 2 n (xCore false) w) := by
  let f : Bond →+* Bond := (starRingEnd ℂ).mapMatrix
  have h : wordMatrix (xCore true) w = (∏ i, phase (w i)) • f (wordMatrix (xCore false) w) := by
    induction n with
    | zero => simp [wordMatrix, List.ofFn_zero]
    | succ n ih =>
      rw [← Fin.cons_self_tail w, wordMatrix_cons, wordMatrix_cons, ih, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, mixed_partner, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, map_mul]
      rw [mul_comm (∏ i : Fin n, phase (Fin.tail w i))]
      rfl
  change (wordMatrix (xCore true) w).trace = _ * star (wordMatrix (xCore false) w).trace
  rw [h, Matrix.trace_smul, smul_eq_mul]
  congr 1
  exact (AddMonoidHom.map_trace (starRingEnd ℂ) _).symm

private theorem phase_square : (1 + I) ^ 2 = -(1 - I) ^ 2 := by
  apply Complex.ext <;> norm_num [pow_two, Complex.mul_re, Complex.mul_im]

private theorem b0 (m : ℕ) :
    traceWord 2 2 (m + 3) (xCore true) (zeros (m + 3)) =
      (1 - I) ^ (m + 3) * star (1 + z ^ (m + 3)) := by
  rw [x_partner_word, a0]
  simp [zeros, phase]

private theorem b2 (m : ℕ) :
    traceWord 2 2 (m + 3) (xCore true) (twiceMinus m) =
      -((1 - I) ^ (m + 3)) * star (z ^ 2 + z ^ (m + 1)) := by
  rw [x_partner_word, a2]
  congr 1
  simp only [twiceMinus, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp [zeros, phase]
  linear_combination ((1 - I) ^ m * (1 - I)) * phase_square

private theorem negative_overlap (m : ℕ) (hm : 4 ≤ m) :
    ((z ^ 2 + z ^ (m + 1)) * star (1 + z ^ (m + 3))).re < 0 := by
  have hz2 : z ^ 2 = -(1 / 4 : ℂ) := by unfold z; rw [div_pow, Complex.I_sq]; norm_num
  have hz : z ^ (m + 1) = -4 * z ^ (m + 3) := by
    rw [show m + 3 = (m + 1) + 2 by omega, pow_add z (m + 1) 2, hz2]
    ring
  have hn : ‖z ^ (m + 3)‖ ≤ (1 / 2 : ℝ) ^ 7 := by
    rw [norm_pow, z, norm_div, Complex.norm_I, Complex.norm_two]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hre := (abs_le.mp (le_trans (Complex.abs_re_le_norm (z ^ (m + 3))) hn)).1
  rw [hz2, hz]
  generalize z ^ (m + 3) = t at hre ⊢
  norm_num [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im, Complex.star_def,
    Complex.div_re, Complex.div_im] at hre ⊢
  nlinarith [sq_nonneg t.re, sq_nonneg t.im]

private theorem phase_ne_zero (m : ℕ) : (1 - I) ^ (m + 3) ≠ 0 :=
  pow_ne_zero _ (fun h => by have := congrArg Complex.re h; norm_num at this)

private theorem rays_distinct_aux (m : ℕ) (hm : 4 ≤ m) (c : ℂ) :
    traceWord 2 2 (m + 3) (cores true) ≠ c • traceWord 2 2 (m + 3) (cores false) := by
  intro h
  have h0 := mix_proportional h (zeros (m + 3))
  have h2 := mix_proportional h (twiceMinus m)
  rw [a0, b0] at h0
  rw [a2, b2] at h2
  let u := 1 + z ^ (m + 3)
  let v := z ^ 2 + z ^ (m + 1)
  let k := (1 - I) ^ (m + 3)
  change k * star u = c * u at h0
  change -k * star v = c * v at h2
  have hsum : k * (v * star u + u * star v) = 0 := by
    linear_combination v * h0 - u * h2
  have hzero := (mul_eq_zero.mp hsum).resolve_left (phase_ne_zero m)
  have hre := congrArg Complex.re hzero
  have hn := negative_overlap m hm
  change (v * star u).re < 0 at hn
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.zero_re] at hre hn
  nlinarith

private theorem nonzero_rays_aux (m : ℕ) (hm : 4 ≤ m) (b : Bool) :
    traceWord 2 2 (m + 3) (cores b) ≠ 0 := by
  intro h
  have hmix := trace_mixing ((4 : ℂ)⁻¹ • hadamard) (cores b) (zeros (m + 3))
  rw [h] at hmix
  have hzero : traceWord 2 2 (m + 3) (xCore b) (zeros (m + 3)) = 0 := by simpa [xCore] using hmix
  have ha : 1 + z ^ (m + 3) ≠ 0 := by
    intro he
    have hn := negative_overlap m hm
    rw [he, star_zero, mul_zero, Complex.zero_re] at hn
    exact (lt_irrefl 0) hn
  cases b
  · exact ha (a0 m ▸ hzero)
  · rw [b0] at hzero
    exact (mul_ne_zero (phase_ne_zero m) (star_ne_zero.mpr ha)) hzero

/-- At every length at least seven, the Ising pair are nonzero distinct
actual periodic rays with the same positive-definite trace-one two-site
marginal. Both pairs span the bond space at length two and both transfers
send every nonzero positive semidefinite matrix to a positive definite
matrix after two steps. The real Pauli observation Jacobian has rank eight
at both members of the pair. -/
theorem primitive_two_site_collision (n : ℕ) (hn : 7 ≤ n) :
    (∀ b, traceWord 2 2 n (cores b) ≠ 0) ∧
    (∀ c : ℂ, traceWord 2 2 n (cores true) ≠ c • traceWord 2 2 n (cores false)) ∧
    (∀ b, normalizedMarginal (n - 2) (cores b) = collisionMarginal) ∧
    collisionMarginal.PosDef ∧ collisionMarginal.trace = 1 ∧
    (∀ b, TwoSiteSpanning (cores b)) ∧
    (∀ b (H : Bond), H.PosSemidef → H ≠ 0 → (transferStep b (transferStep b H)).PosDef) ∧
    (∀ b, (isingObservationJacobian b (n - 4)).rank = 8) := by
  let m := n - 3
  have hlen : m + 3 = n := by dsimp [m]; omega
  have hm : 4 ≤ m := by dsimp [m]; omega
  refine ⟨?_, ?_, ?_, collision_marginal_posDef, collision_marginal_trace,
    twoSiteSpanning_cores, (fun b _ => transferStep_twice_posDef b), ?_⟩
  · rw [← hlen]
    exact nonzero_rays_aux m hm
  · rw [← hlen]
    exact rays_distinct_aux m hm
  · intro b
    have h : n - 2 = (n - 4) + 2 := by omega
    rw [h, normalized_collision_marginal]
  · intro b
    exact isingObservationJacobian_rank b (n - 4) (by omega)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.primitive_two_site_collision

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.collision_marginal_charpoly
