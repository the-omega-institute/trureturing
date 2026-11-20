/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionVariation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionVariation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionTransfer]
   utility: none
   digest: The normalized marginal variation at the primitive collision. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionTransfer
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv

/-! Stabilization of the normalized first variation at the two Ising cores. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

open Matrix
open scoped Matrix Kronecker
open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSTwoSiteAmbiguity (rawTwo rawTwo_star_swap)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal normalizedMarginal_eq_rawTwo)
open PeriodicMPSUniformAntisymmetricTransfer
  (TransferMatrix mixedTransfer mixedRaw conjugateCore rawTwo_eq_mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (binaryInsertion binaryTransfer)

noncomputable section

private abbrev Pair := Fin 2 × Fin 2
private abbrev Transfer := TransferMatrix ℂ
private abbrev Core := Fin 2 → Bond

private def variationPower (T D : Transfer) : ℕ → Transfer
  | 0 => 0
  | m+1 => variationPower T D m * T + T ^ m * D

private theorem power_stable {T : Transfer} (hT : T ^ 3 = T ^ 2) (m : ℕ) :
    T ^ (m + 2) = T ^ 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ, ih, ← pow_succ, hT]

private theorem variationPower_stable {T : Transfer} (hT : T ^ 3 = T ^ 2)
    (D : Transfer) (m : ℕ) :
    variationPower T D (m + 5) =
      (1 + T) * D * T ^ 2 + T ^ 2 * D * (1 + T) + (m + 1) • (T ^ 2 * D * T ^ 2) := by
  have hP : T ^ 2 * T = T ^ 2 := by rw [← pow_succ, hT]
  have h3 : T * (T * T) = T * T := by simpa [pow_succ', mul_assoc] using hT
  induction m with
  | zero =>
    simp only [variationPower, zero_mul, pow_zero, one_mul, zero_add, pow_one, hT,
      power_stable hT 2, zero_add, one_nsmul, add_mul, mul_add]
    simp only [pow_two, mul_assoc, h3]
    noncomm_ring
  | succ m ih =>
    rw [show m + 1 + 5 = (m + 5) + 1 by omega, variationPower, ih,
      show m + 5 = (m + 3) + 2 by omega, power_stable hT (m + 3)]
    simp only [add_mul, smul_mul_assoc, mul_assoc, hP, one_mul, ← pow_two, mul_add,
      mul_one, add_nsmul, one_nsmul]
    abel

private theorem rankOne_sandwich (u v : Pair → ℂ) (D : Transfer) :
    vecMulVec u v * D * vecMulVec u v =
      ((vecMulVec u v * D).trace) • vecMulVec u v := by
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private def scaledTransfer (s : ℝ) (A : Core) : Transfer :=
  s⁻¹ • mixedTransfer A (conjugateCore A)

private def insertion (A : Core) (p q : Pair) : Transfer :=
  binaryInsertion (conjugateCore A) A q p

private def scaledRaw (s : ℝ) (A : Core) (m : ℕ) : Transfer :=
  fun p q => (insertion A p q * scaledTransfer s A ^ m).trace

private theorem scaledRaw_eq (s : ℝ) (A : Core) (r : ℕ) :
    scaledRaw s A (r + 2) = (s⁻¹) ^ (r + 2) • rawTwo A r := by
  rw [rawTwo_eq_mixedRaw]
  ext p q
  change (_ * (s⁻¹ • mixedTransfer A (conjugateCore A)) ^ (r + 2)).trace = _
  rw [smul_pow, Matrix.mul_smul, Matrix.trace_smul, Matrix.smul_apply]
  rfl

private theorem raw_trace_real (A : Core) (r : ℕ) :
    ((rawTwo A r).trace.re : ℂ) = (rawTwo A r).trace := by
  have h : star (rawTwo A r).trace = (rawTwo A r).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, star_sum, rawTwo_star_swap]
  exact Complex.ext (by simp) (by simpa using (Complex.conj_eq_iff_im.mp h).symm)

private theorem scaledRaw_normalize (s : ℝ) (hs : s ≠ 0) (A : Core) (r : ℕ) :
    (scaledRaw s A (r + 2)).trace⁻¹ • scaledRaw s A (r + 2) =
      normalizedMarginal (r + 2) A := by
  rw [normalizedMarginal_eq_rawTwo, scaledRaw_eq]
  have he (a : ℝ) (M : Transfer) : a • M = (a : ℂ) • M := by
    ext i j
    simp [Complex.real_smul, smul_eq_mul]
  rw [he, he, Matrix.trace_smul, smul_eq_mul, _root_.mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast pow_ne_zero _ (inv_ne_zero hs)), mul_one,
    Complex.ofReal_inv, raw_trace_real]

private def Jet {ι : Type*} (M : ℝ → Matrix ι ι ℂ) (D : Matrix ι ι ℂ) : Prop :=
  ∀ i j, HasDerivAt (fun t => M t i j) (D i j) 0

private theorem jet_mul {ι : Type*} [Fintype ι]
    {M N : ℝ → Matrix ι ι ℂ} {D E : Matrix ι ι ℂ} (hM : Jet M D) (hN : Jet N E) :
    Jet (fun t => M t * N t) (D * N 0 + M 0 * E) := by
  intro i j
  simpa only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib, Pi.mul_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hM i k).mul (hN k j))

private theorem jet_pow {M : ℝ → Transfer} {D : Transfer} (hM : Jet M D) (m : ℕ) :
    Jet (fun t => M t ^ m) (variationPower (M 0) D m) := by
  induction m with
  | zero => intro i j; simpa [variationPower] using hasDerivAt_const (x := (0 : ℝ)) ((1 : Transfer) i j)
  | succ m ih =>
    simpa only [pow_succ, variationPower] using jet_mul ih hM

private theorem jet_trace {M : ℝ → Transfer} {D : Transfer} (hM : Jet M D) :
    HasDerivAt (fun t => (M t).trace) D.trace 0 := by
  simpa only [Matrix.trace, Matrix.diag_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hM k k)

private theorem jet_readout {T : ℝ → Transfer} {Ins : Pair → Pair → ℝ → Transfer}
    {D : Transfer} {dIns : Pair → Pair → Transfer} (hT : Jet T D)
    (hI : ∀ p q, Jet (Ins p q) (dIns p q)) (m : ℕ) :
    Jet (fun t p q => (Ins p q t * T t ^ m).trace)
      (fun p q => (dIns p q * T 0 ^ m + Ins p q 0 * variationPower (T 0) D m).trace) := by
  intro p q
  exact jet_trace (jet_mul (hI p q) (jet_pow hT m))

private def normalizedDerivative (R D : Transfer) : Transfer :=
  R.trace⁻¹ • D - (D.trace / R.trace ^ 2) • R

private theorem jet_normalize {M : ℝ → Transfer} {D : Transfer}
    (hM : Jet M D) (hne : (M 0).trace ≠ 0) :
    Jet (fun t => (M t).trace⁻¹ • M t) (normalizedDerivative (M 0) D) := by
  intro i j
  have h := ((jet_trace hM).fun_inv hne).fun_mul (hM i j)
  simpa only [Matrix.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.inv_apply, normalizedDerivative,
    Matrix.sub_apply, sub_eq_add_neg, neg_div, neg_mul, add_comm] using h

private theorem normalizedDerivative_add (R D : Transfer) (a : ℂ) (h : R.trace ≠ 0) :
    normalizedDerivative R (D + a • R) = normalizedDerivative R D := by
  rw [normalizedDerivative, normalizedDerivative, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, smul_add, smul_smul]
  have he : (D.trace + a * R.trace) / R.trace ^ 2 =
      D.trace / R.trace ^ 2 + R.trace⁻¹ * a := by field_simp
  rw [he, add_smul]
  abel

/-- A real line through an Ising core pair, with arbitrary complex direction. -/
def coreLine (b : Bool) (V : Core) (t : ℝ) : Core := cores b + t • V

private theorem coreLine_zero (b : Bool) (V : Core) : coreLine b V 0 = cores b := by
  simp [coreLine]

private theorem scale_ne_zero (b : Bool) : (collisionScale b : ℝ) ≠ 0 := by
  cases b <;> norm_num [collisionScale]

private theorem scaledTransfer_at_center (b : Bool) :
    scaledTransfer (collisionScale b) (cores b) = stabilizedTransfer b := by
  ext p q
  simp [scaledTransfer, stabilizedTransfer, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

private theorem scaledRaw_at_center (b : Bool) {r : ℕ} :
    (scaledRaw (collisionScale b) (cores b) (r + 2)).trace ≠ 0 := by
  intro h
  have hnormalize := scaledRaw_normalize (collisionScale b) (scale_ne_zero b) (cores b) r
  rw [h, _root_.inv_zero, zero_smul, normalized_collision_marginal] at hnormalize
  have htrace := congrArg Matrix.trace hnormalize
  rw [Matrix.trace_zero, collision_marginal_trace] at htrace
  exact zero_ne_one htrace

section AlgebraicVariation

variable {R : Type*} [CommRing R]
private abbrev Tensors (R : Type*) := Fin 2 → Matrix (Fin 2) (Fin 2) R

/-- Variation of the transfer when the ket and bra cores vary independently. -/
def transferVariation (A B U V : Tensors R) : TransferMatrix R :=
  mixedTransfer U B + mixedTransfer A V

/-- Variation of the marked two-site block in bra-first transfer order. -/
def markedVariation (A B U V : Tensors R) (p q : Pair) : TransferMatrix R :=
  ((V q.1 * B q.2 + B q.1 * V q.2) ⊗ₖ (A p.1 * A p.2)) +
    ((B q.1 * B q.2) ⊗ₖ (U p.1 * A p.2 + A p.1 * U p.2))

end AlgebraicVariation

private theorem ket_line_jet (b : Bool) (V : Core) (i : Fin 2) :
    Jet (fun t => coreLine b V t i) (V i) := by
  intro j k
  change HasDerivAt (fun t : ℝ => cores b i j k + t • V i j k) _ 0
  simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (V i j k) |>.const_add _

private theorem bra_line_jet (b : Bool) (V : Core) (i : Fin 2) :
    Jet (fun t => conjugateCore (coreLine b V t) i) (conjugateCore V i) := by
  intro j k
  exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (ket_line_jet b V i j k)

private theorem jet_kronecker {M N : ℝ → Bond} {D E : Bond} (hM : Jet M D) (hN : Jet N E) :
    Jet (fun t => M t ⊗ₖ N t) ((D ⊗ₖ N 0) + (M 0 ⊗ₖ E)) := by
  intro p q
  simpa only [Matrix.kroneckerMap_apply, Matrix.add_apply, Pi.mul_apply] using
    (hM p.1 q.1).fun_mul (hN p.2 q.2)

private theorem jet_add {ι : Type*} {M N : ℝ → Matrix ι ι ℂ} {D E : Matrix ι ι ℂ}
    (hM : Jet M D) (hN : Jet N E) : Jet (fun t => M t + N t) (D + E) := by
  intro i j
  exact (hM i j).add (hN i j)

private theorem jet_const_smul {ι : Type*} {M : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ}
    (s : ℝ) (hM : Jet M D) : Jet (fun t => s • M t) (s • D) := by
  intro i j
  exact (hM i j).const_smul s

private theorem transfer_line_jet (b : Bool) (V : Core) :
    Jet (fun t => scaledTransfer (collisionScale b) (coreLine b V t))
      ((collisionScale b : ℝ)⁻¹ •
        transferVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)) := by
  have h₀ := jet_kronecker (bra_line_jet b V 0) (ket_line_jet b V 0)
  have h₁ := jet_kronecker (bra_line_jet b V 1) (ket_line_jet b V 1)
  have h := jet_const_smul ((collisionScale b : ℝ)⁻¹) (jet_add h₀ h₁)
  rw [coreLine_zero] at h
  have he :
      ((conjugateCore V 0 ⊗ₖ cores b 0) + (conjugateCore (cores b) 0 ⊗ₖ V 0)) +
        ((conjugateCore V 1 ⊗ₖ cores b 1) + (conjugateCore (cores b) 1 ⊗ₖ V 1)) =
        transferVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V) := by
    unfold transferVariation mixedTransfer binaryTransfer
    abel
  rw [he] at h
  exact h

private theorem insertion_line_jet (b : Bool) (V : Core) (p q : Pair) :
    Jet (fun t => insertion (coreLine b V t) p q)
      (markedVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V) p q) := by
  have h := jet_kronecker (jet_mul (bra_line_jet b V q.1) (bra_line_jet b V q.2))
    (jet_mul (ket_line_jet b V p.1) (ket_line_jet b V p.2))
  simpa only [insertion, binaryInsertion, markedVariation, coreLine_zero] using h

/-- A length-independent normalized first variation of the physical marginal. -/
def normalizedFirstVariation (b : Bool) (V : Core) : Transfer :=
  let T := stabilizedTransfer b
  let P := T ^ 2
  let D := (collisionScale b : ℝ)⁻¹ •
    transferVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)
  let dIns := markedVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)
  let edge := (1 + T) * D * P + P * D * (1 + T)
  let R : Transfer := fun p q => (insertion (cores b) p q * P).trace
  let first : Transfer := fun p q => (dIns p q * P + insertion (cores b) p q * edge).trace
  normalizedDerivative R first

/-- The edge contribution after removing the geometric transfer growth. -/
def firstVariationNumerator (b : Bool) (V : Core) : Transfer :=
  let T := stabilizedTransfer b
  let P := T ^ 2
  let D := (collisionScale b : ℝ)⁻¹ •
    transferVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)
  let dIns := markedVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)
  let edge := (1 + T) * D * P + P * D * (1 + T)
  fun p q => (dIns p q * P + insertion (cores b) p q * edge).trace

theorem normalizedFirstVariation_sub (b : Bool) (V : Core) :
    normalizedFirstVariation b V = ((collisionScale b : ℂ) ^ 2)⁻¹ •
      (firstVariationNumerator b V - (firstVariationNumerator b V).trace • collisionMarginal) := by
  let R : Transfer := fun p q => (insertion (cores b) p q * stabilizedTransfer b ^ 2).trace
  let F := firstVariationNumerator b V
  have hR : scaledRaw (collisionScale b) (cores b) 2 = R := by
    funext p q
    change (insertion (cores b) p q * scaledTransfer (collisionScale b) (cores b) ^ 2).trace = _
    rw [scaledTransfer_at_center]
  have hr : R.trace = (collisionScale b : ℂ) ^ 2 := by
    rw [← hR, scaledRaw_eq _ _ 0, Matrix.trace_smul, Complex.real_smul, rawTwo_trace_initial]
    cases b <;> norm_num [collisionScale]
  have hn := scaledRaw_normalize (collisionScale b) (scale_ne_zero b) (cores b) 0
  rw [normalized_collision_marginal] at hn
  change (scaledRaw (collisionScale b) (cores b) 2).trace⁻¹ •
    scaledRaw (collisionScale b) (cores b) 2 = _ at hn
  rw [hR] at hn
  change normalizedDerivative R F = _
  rw [← hr, ← hn, normalizedDerivative, smul_sub, smul_smul, smul_smul]
  congr 2
  rw [div_eq_mul_inv, ← inv_pow, pow_two]
  change _ = R.trace⁻¹ * F.trace * R.trace⁻¹
  ring

private theorem variation_stable_normalized
    (b : Bool) (V : Core) (r : ℕ) (hr : 3 ≤ r) :
    Jet (fun t => normalizedMarginal (r + 2) (coreLine b V t)) (normalizedFirstVariation b V) := by
  let T : ℝ → Transfer := fun t => scaledTransfer (collisionScale b) (coreLine b V t)
  let Ins : Pair → Pair → ℝ → Transfer := fun p q t => insertion (coreLine b V t) p q
  let D := (collisionScale b : ℝ)⁻¹ •
    transferVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)
  let dIns := markedVariation (cores b) (conjugateCore (cores b)) V (conjugateCore V)
  have hTj : Jet T D := transfer_line_jet b V
  have hIj (p q : Pair) : Jet (Ins p q) (dIns p q) := insertion_line_jet b V p q
  have ht0 : T 0 = stabilizedTransfer b := by
    simpa only [T, coreLine_zero] using scaledTransfer_at_center b
  have hi0 (p q : Pair) : Ins p q 0 = insertion (cores b) p q := by
    simp only [Ins, coreLine_zero]
  let M : ℝ → Transfer := fun t p q => (Ins p q t * T t ^ (r + 2)).trace
  have hM : M = fun t => scaledRaw (collisionScale b) (coreLine b V t) (r + 2) := by
    rfl
  have hne : (M 0).trace ≠ 0 := by
    simpa only [hM, coreLine_zero] using (scaledRaw_at_center b (r := r))
  have ht := stabilizedTransfer_cube b
  let P := stabilizedTransfer b ^ 2
  let R : Transfer := fun p q => (insertion (cores b) p q * P).trace
  let edge := (1 + stabilizedTransfer b) * D * P + P * D * (1 + stabilizedTransfer b)
  let first : Transfer := fun p q => (dIns p q * P + insertion (cores b) p q * edge).trace
  have hR : M 0 = R := by
    funext p q
    simp only [M, R, P, ht0, hi0, power_stable ht r]
  have hPd : P * D * P = (P * D).trace • P := by
    unfold P
    rw [stabilizedTransfer_square]
    exact rankOne_sandwich _ _ D
  let k := r - 3
  have hk : r + 2 = k + 5 := by dsimp [k]; omega
  have hedge := variationPower_stable ht D k
  rw [← hk, hPd] at hedge
  let c : ℂ := (k + 1 : ℕ) * (P * D).trace
  have hD : (fun p q => (dIns p q * T 0 ^ (r + 2) +
      Ins p q 0 * variationPower (T 0) D (r + 2)).trace) = first + c • R := by
    funext p q
    change _ = first p q + c • R p q
    simp only [ht0, hi0, power_stable ht r, hedge, ← Nat.cast_smul_eq_nsmul ℂ,
      Matrix.mul_add, Matrix.mul_smul, smul_smul, ← add_assoc, Matrix.trace_add,
      Matrix.trace_smul, first, edge, P, R, c]
  have hjet := jet_normalize (jet_readout hTj hIj (r + 2)) hne
  change Jet (fun t => (M t).trace⁻¹ • M t) (normalizedDerivative (M 0)
    (fun p q => (dIns p q * T 0 ^ (r + 2) +
      Ins p q 0 * variationPower (T 0) D (r + 2)).trace)) at hjet
  rw [hD, hR, normalizedDerivative_add R first c (hR ▸ hne)] at hjet
  have hchange : (fun t => (M t).trace⁻¹ • M t) =
      fun t => normalizedMarginal (r + 2) (coreLine b V t) := by
    funext t
    rw [hM, scaledRaw_normalize _ (scale_ne_zero b)]
  rw [hchange] at hjet
  exact hjet

theorem normalizedMarginal_hasDerivAt (b : Bool) (V : Core)
    (r : ℕ) (hr : 3 ≤ r) (p q : Pair) :
    HasDerivAt (fun t => normalizedMarginal (r + 2) (coreLine b V t) p q)
      (normalizedFirstVariation b V p q) 0 :=
  (variation_stable_normalized b V r hr) p q

/-- The stabilized finite transfer formula gives the actual directional derivative. -/
theorem normalizedMarginal_deriv_formula (b : Bool) (V : Core)
    (r : ℕ) (hr : 3 ≤ r) (p q : Pair) :
    deriv (fun t => normalizedMarginal (r + 2) (coreLine b V t) p q) 0 =
      normalizedFirstVariation b V p q :=
  ((variation_stable_normalized b V r hr) p q).deriv

/-- Normalization cancels the interior transfer insertions. The actual
two-site directional derivatives at both Ising cores are independent of
chain length from seven onward. -/
theorem normalizedMarginal_deriv_eq_seven (b : Bool) (V : Core)
    (r : ℕ) (hr : 3 ≤ r) (p q : Pair) :
    deriv (fun t => normalizedMarginal (r + 2) (coreLine b V t) p q) 0 =
      deriv (fun t => normalizedMarginal 5 (coreLine b V t) p q) 0 := by
  exact ((variation_stable_normalized b V r hr) p q).deriv.trans
    (((variation_stable_normalized b V 3 (by decide)) p q).deriv.symm)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision.normalizedMarginal_deriv_eq_seven
