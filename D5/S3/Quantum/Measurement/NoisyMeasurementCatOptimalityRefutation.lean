/- GID: D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.claim; result=D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result; claim=D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.claim
   digest: Under independent noisy readout, no cat pair need maximize the Fisher coefficient. -/

/-
proof_shape: probeOp, multiProbeOp, gamma: definition (M_x = Σ_i p(x|i) Π_i, the tensor product
  M_𝐱 = M_{x_1} ⊗ ⋯ ⊗ M_{x_N} through the frozen piKroneckerLinearEquiv, and Eq. (AgammaN) with
  V_Φ ψ = (ζ + ζ⊥)/√2, V_Φ ψ⊥ = (ζ − ζ⊥)/√2)
proof_shape: basisPower, catState, catPerp: definition (|j⟩^{⊗N} and the cat pair)
proof_shape: claim: definition (published conjecture, arXiv:2109.01160v2, Supplementary Note 5,
  "A note on optimality", read for every d ≥ 2, finite outcome set, classical noise channel with
  all p(x|i) > 0, so that an optimal pair exists, and N ≥ 1)
proof_shape: detector, witness, witnessPerp: definition (the counterexample)
proof_shape: result: bind-only (as local steps: the entries of the noisy operators, from
  multilinearity of the tensor product and pi_kronecker_linear_equiv_tprod_single; γ of a pair
  supported on two basis words; the reduction of every cat pair to that form; tangent-line upper
  bounds for t ↦ t(1−t)(a−b)²/(ta+(1−t)b); and rational evaluations)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12917; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/ObserverMemory/PrimePowerTensorTower.piKroneckerLinearEquiv
    sha256:61f87e3d03217f0969c03558727e4e6c694a72a49a9a1c046983576b1b652927
  D5/S3/ObserverMemory/PrimePowerTensorTower.pi_kronecker_linear_equiv_tprod_single
    sha256:8ab158d6073e3f6fd2cd92ff5bcecde7ea006c7f86bb1bb2be451cd647fb6723
-/

import D5.S3.ObserverMemory.PrimePowerTensorTower
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Measurement.NoisyMeasurementCatOptimalityRefutation

open Matrix
open D5.S3.ObserverMemory.PrimePowerTensorTower

/-- The single-probe noisy measurement operator `M_x = ∑_i p(x|i) Π_i` with `Π_i = |i⟩⟨i|`. -/
noncomputable def probeOp {d : ℕ} {X : Type*} (p : X → Fin d → ℝ) (x : X) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, (p x i : ℂ) • Matrix.single i i 1

/-- The operator `M_𝐱 = M_{x_1} ⊗ ⋯ ⊗ M_{x_N}` on `(Fin N → Fin d) → ℂ`, through the frozen
finite-family Kronecker equivalence. -/
noncomputable def multiProbeOp {d N : ℕ} {X : Type*} (p : X → Fin d → ℝ) (xs : Fin N → X) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  piKroneckerLinearEquiv (fun _ : Fin N => Fin d)
    (PiTensorProduct.tprod ℂ fun l => probeOp p (xs l))

/-- Eq. (AgammaN): `γ = ¼ ∑_𝐱 [⟨ψ⊥|V_Φ† M_𝐱 V_Φ|ψ⟩ + c.c.]² / ⟨ψ|V_Φ† M_𝐱 V_Φ|ψ⟩`, where
`V_Φ ψ = (ζ + ζ⊥)/√2` and `V_Φ ψ⊥ = (ζ − ζ⊥)/√2` invert `V_Φ (ψ ± ψ⊥)/√2 = ζ, ζ⊥`. -/
noncomputable def gamma {d N : ℕ} {X : Type*} [Fintype X] (p : X → Fin d → ℝ)
    (ζ ζp : (Fin N → Fin d) → ℂ) : ℝ :=
  let ψ : (Fin N → Fin d) → ℂ := (Real.sqrt 2 : ℂ)⁻¹ • (ζ + ζp)
  let ψp : (Fin N → Fin d) → ℂ := (Real.sqrt 2 : ℂ)⁻¹ • (ζ - ζp)
  ∑ xs : Fin N → X,
    (1 / 4 * (star ψp ⬝ᵥ (multiProbeOp p xs *ᵥ ψ) +
        star (star ψp ⬝ᵥ (multiProbeOp p xs *ᵥ ψ))) ^ 2 /
      (star ψ ⬝ᵥ (multiProbeOp p xs *ᵥ ψ))).re

/-- The product vector `|j⟩^{⊗N}`. -/
noncomputable def basisPower {d N : ℕ} (j : Fin d) : (Fin N → Fin d) → ℂ :=
  fun s => ∏ l, (Pi.single j 1 : Fin d → ℂ) (s l)

/-- The cat state `cos θ |j⟩^{⊗N} + sin θ |k⟩^{⊗N}`. -/
noncomputable def catState {d N : ℕ} (j k : Fin d) (θ : ℝ) : (Fin N → Fin d) → ℂ :=
  (Real.cos θ : ℂ) • basisPower j + (Real.sin θ : ℂ) • basisPower k

/-- Its partner `−sin θ |j⟩^{⊗N} + cos θ |k⟩^{⊗N}`. -/
noncomputable def catPerp {d N : ℕ} (j k : Fin d) (θ : ℝ) : (Fin N → Fin d) → ℂ :=
  (-Real.sin θ : ℂ) • basisPower j + (Real.cos θ : ℂ) • basisPower k

/-- The conjecture: for every classical noise channel with all entries positive, applied
independently to `N` probes, some cat pair maximizes `γ` over all orthonormal pairs. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (X : Type) [Fintype X] (p : X → Fin d → ℝ),
    (∀ x i, 0 < p x i) → (∀ i, ∑ x, p x i = 1) → ∀ N : ℕ, 1 ≤ N →
      ∃ j k : Fin d, j ≠ k ∧ ∃ θ : ℝ, ∀ ζ ζp : (Fin N → Fin d) → ℂ,
        star ζ ⬝ᵥ ζ = 1 → star ζp ⬝ᵥ ζp = 1 → star ζp ⬝ᵥ ζ = 0 →
          gamma p ζ ζp ≤ gamma p (catState (N := N) j k θ) (catPerp j k θ)

/-- The detector `p(x|i)`: row `x`, column `i`; each column is a probability vector. -/
noncomputable def detector : Fin 3 → Fin 3 → ℝ :=
  ![![1 / 20, 14 / 20, 2 / 20], ![15 / 20, 2 / 20, 17 / 20], ![4 / 20, 4 / 20, 1 / 20]]

/-- The witness `ζ = |10⟩`. -/
noncomputable def witness : (Fin 2 → Fin 3) → ℂ :=
  fun s => if s = ![1, 0] then ((1 : ℝ) : ℂ) else if s = ![2, 1] then ((0 : ℝ) : ℂ) else 0

/-- The witness `ζ⊥ = |21⟩`. -/
noncomputable def witnessPerp : (Fin 2 → Fin 3) → ℂ :=
  fun s => if s = ![1, 0] then ((0 : ℝ) : ℂ) else if s = ![2, 1] then ((1 : ℝ) : ℂ) else 0

set_option maxHeartbeats 1000000 in
-- the six rational tangent certificates are checked inside one declaration
/-- The conjecture fails for the detector `detector`, two probes and the pair `|10⟩`, `|21⟩`. -/
theorem result : ¬ claim := by
  intro h
  have hP : ∀ x i, 0 < detector x i := by
    intro x i
    fin_cases x <;> fin_cases i <;> norm_num [detector]
  have hcol : ∀ i, ∑ x, detector x i = 1 := by
    intro i
    fin_cases i <;> norm_num [detector, Fin.sum_univ_three, Matrix.cons_val_two]
  obtain ⟨j, k, hjk, θ, hmax⟩ :=
    h 3 (by norm_num) (Fin 3) detector hP hcol 2 (by norm_num)
  set m : (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → ℝ := fun xs s => ∏ l, detector (xs l) (s l)
    with hm
  have hexp : ∀ xs, multiProbeOp detector xs =
      ∑ f : Fin 2 → Fin 3, ((m xs f : ℝ) : ℂ) • Matrix.single f f (1 : ℂ) := by
    intro xs
    simp only [multiProbeOp, probeOp]
    rw [MultilinearMap.map_sum (PiTensorProduct.tprod ℂ)
      (fun l i => (detector (xs l) i : ℂ) • Matrix.single i i (1 : ℂ)), map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [MultilinearMap.map_smul_univ, map_smul, pi_kronecker_linear_equiv_tprod_single, hm]
    push_cast
    rfl
  have hM : ∀ xs s s', multiProbeOp detector xs s s' =
      if s = s' then ((m xs s : ℝ) : ℂ) else 0 := by
    intro xs s s'
    rw [hexp, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hss : s = s'
    · subst hss
      simp
    · simp only [hss, if_false]
      refine Finset.sum_eq_zero fun f _ => ?_
      have hf : ¬ (f = s ∧ f = s') := fun hf => hss (hf.1.symm.trans hf.2)
      simp [hf]
  have hmv : ∀ xs (ψ : (Fin 2 → Fin 3) → ℂ) s,
      (multiProbeOp detector xs *ᵥ ψ) s = (m xs s : ℂ) * ψ s := by
    intro xs ψ s
    simp only [Matrix.mulVec, dotProduct, hM, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hreal : ∀ f g : (Fin 2 → Fin 3) → ℝ,
      gamma detector (fun s => (f s : ℂ)) (fun s => (g s : ℂ)) =
        ∑ xs, 1 / 4 * (2 * ∑ s, (Real.sqrt 2)⁻¹ * (f s - g s) *
            (m xs s * ((Real.sqrt 2)⁻¹ * (f s + g s)))) ^ 2 /
          ∑ s, (Real.sqrt 2)⁻¹ * (f s + g s) *
            (m xs s * ((Real.sqrt 2)⁻¹ * (f s + g s))) := by
    intro f g
    simp only [gamma]
    refine Finset.sum_congr rfl fun xs _ => ?_
    have hz : ∀ u w : (Fin 2 → Fin 3) → ℝ,
        star ((Real.sqrt 2 : ℂ)⁻¹ • (fun s => (u s : ℂ))) ⬝ᵥ
            (multiProbeOp detector xs *ᵥ ((Real.sqrt 2 : ℂ)⁻¹ • (fun s => (w s : ℂ)))) =
          ((∑ s, (Real.sqrt 2)⁻¹ * u s * (m xs s * ((Real.sqrt 2)⁻¹ * w s)) : ℝ) : ℂ) := by
      intro u w
      simp only [dotProduct, hmv, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul',
        Complex.star_def, map_inv₀, Complex.conj_ofReal]
      push_cast
      rfl
    have e1 : ((Real.sqrt 2 : ℂ)⁻¹ • ((fun s => (f s : ℂ)) - fun s => (g s : ℂ))) =
        (Real.sqrt 2 : ℂ)⁻¹ • (fun s => ((f s - g s : ℝ) : ℂ)) := by
      funext s
      simp
    have e2 : ((Real.sqrt 2 : ℂ)⁻¹ • ((fun s => (f s : ℂ)) + fun s => (g s : ℂ))) =
        (Real.sqrt 2 : ℂ)⁻¹ • (fun s => ((f s + g s : ℝ) : ℂ)) := by
      funext s
      simp
    rw [e1, e2, hz, hz]
    simp only [Complex.conj_ofReal, Complex.star_def]
    rw [← Complex.ofReal_add, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    ring
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have htwo : ∀ u v : Fin 2 → Fin 3, u ≠ v → ∀ a b a' b' : ℝ,
      gamma detector (fun s => ((if s = u then a else if s = v then b else 0 : ℝ) : ℂ))
          (fun s => ((if s = u then a' else if s = v then b' else 0 : ℝ) : ℂ)) =
        ∑ xs, (((a - a') * (a + a') * m xs u + (b - b') * (b + b') * m xs v) / 2) ^ 2 /
          (((a + a') ^ 2 * m xs u + (b + b') ^ 2 * m xs v) / 2) := by
    intro u v huv a b a' b'
    have hvu : v ≠ u := fun e => huv e.symm
    rw [hreal]
    refine Finset.sum_congr rfl fun xs _ => ?_
    have hZ : ∑ s, (Real.sqrt 2)⁻¹ *
          ((if s = u then a else if s = v then b else 0) -
            (if s = u then a' else if s = v then b' else 0)) *
          (m xs s * ((Real.sqrt 2)⁻¹ * ((if s = u then a else if s = v then b else 0) +
            (if s = u then a' else if s = v then b' else 0)))) =
        ((a - a') * (a + a') * m xs u + (b - b') * (b + b') * m xs v) / 2 := by
      rw [Fintype.sum_eq_add u v huv fun w hw => by simp [hw.1, hw.2]]
      simp only [↓reduceIte, if_neg hvu]
      linear_combination ((a - a') * (a + a') * m xs u + (b - b') * (b + b') * m xs v) * hr
    have hW : ∑ s, (Real.sqrt 2)⁻¹ *
          ((if s = u then a else if s = v then b else 0) +
            (if s = u then a' else if s = v then b' else 0)) *
          (m xs s * ((Real.sqrt 2)⁻¹ * ((if s = u then a else if s = v then b else 0) +
            (if s = u then a' else if s = v then b' else 0)))) =
        ((a + a') ^ 2 * m xs u + (b + b') ^ 2 * m xs v) / 2 := by
      rw [Fintype.sum_eq_add u v huv fun w hw => by simp [hw.1, hw.2]]
      simp only [↓reduceIte, if_neg hvu]
      linear_combination ((a + a') ^ 2 * m xs u + (b + b') ^ 2 * m xs v) * hr
    rw [hZ, hW]
    ring
  have htan : ∀ (A B : (Fin 2 → Fin 3) → ℝ) (t t0 : ℝ), (∀ x, 0 < A x) → (∀ x, 0 < B x) →
      ∑ x, A x = 1 → ∑ x, B x = 1 → 0 ≤ t → t ≤ 1 → 0 < t0 → t0 < 1 →
      ∑ x, t * (1 - t) * (A x - B x) ^ 2 / (t * A x + (1 - t) * B x) ≤
        (1 - t) * (1 - ∑ x, A x * B x * (2 / (t0 * A x + (1 - t0) * B x) -
            B x / (t0 * A x + (1 - t0) * B x) ^ 2)) +
          t * (1 - ∑ x, A x * B x * (2 / (t0 * A x + (1 - t0) * B x) -
            A x / (t0 * A x + (1 - t0) * B x) ^ 2)) := by
    intro A B t t0 hA hB hA1 hB1 ht0 ht1 hs0 hs1
    have hterm : ∀ x, t * (1 - t) * (A x - B x) ^ 2 / (t * A x + (1 - t) * B x) ≤
        (1 - t) * (B x - A x * B x * (2 / (t0 * A x + (1 - t0) * B x) -
            B x / (t0 * A x + (1 - t0) * B x) ^ 2)) +
          t * (A x - A x * B x * (2 / (t0 * A x + (1 - t0) * B x) -
            A x / (t0 * A x + (1 - t0) * B x) ^ 2)) - (2 * t - 1) * (A x - B x) := by
      intro x
      have hAx := hA x
      have hBx := hB x
      set D := t * A x + (1 - t) * B x with hD
      set D0 := t0 * A x + (1 - t0) * B x with hD0
      have hDpos : 0 < D := by
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · rw [hD, ← h0]
          linarith
        · have : 0 ≤ (1 - t) * B x := mul_nonneg (by linarith) hBx.le
          have : 0 < t * A x := mul_pos h0 hAx
          linarith
      have hD0pos : 0 < D0 := by
        have : 0 < (1 - t0) * B x := mul_pos (by linarith) hBx
        have : 0 < t0 * A x := mul_pos hs0 hAx
        linarith
      have hid : t * (1 - t) * (A x - B x) ^ 2 / D =
          D - A x * B x / D - (2 * t - 1) * (A x - B x) := by
        have hDne := hDpos.ne'
        field_simp
        rw [hD]
        ring
      have hcvx : A x * B x * (2 / D0 - D / D0 ^ 2) ≤ A x * B x / D := by
        have hsq : 0 ≤ A x * B x * (D - D0) ^ 2 / (D * D0 ^ 2) := by positivity
        have he : A x * B x * (2 / D0 - D / D0 ^ 2) =
            A x * B x / D - A x * B x * (D - D0) ^ 2 / (D * D0 ^ 2) := by
          field_simp
          ring
        linarith
      have hsplit : A x * B x * (2 / D0 - D / D0 ^ 2) =
          (1 - t) * (A x * B x * (2 / D0 - B x / D0 ^ 2)) +
            t * (A x * B x * (2 / D0 - A x / D0 ^ 2)) := by
        rw [hD]
        ring
      rw [hid]
      nlinarith [hsplit, hcvx]
    calc ∑ x, t * (1 - t) * (A x - B x) ^ 2 / (t * A x + (1 - t) * B x)
        ≤ ∑ x, ((1 - t) * (B x - A x * B x * (2 / (t0 * A x + (1 - t0) * B x) -
            B x / (t0 * A x + (1 - t0) * B x) ^ 2)) +
          t * (A x - A x * B x * (2 / (t0 * A x + (1 - t0) * B x) -
            A x / (t0 * A x + (1 - t0) * B x) ^ 2)) - (2 * t - 1) * (A x - B x)) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hA1, hB1]
        ring
  have hmpos : ∀ xs u, 0 < m xs u := fun xs u => Finset.prod_pos fun l _ => hP _ _
  have hsum1 : ∀ u, ∑ xs, m xs u = 1 := by
    intro u
    simp only [hm]
    rw [← Fintype.prod_sum (fun l x => detector x (u l))]
    simp [hcol]
  have hsum9 : ∀ f : (Fin 2 → Fin 3) → ℝ, ∑ xs, f xs = ∑ a : Fin 3, ∑ b : Fin 3, f ![a, b] := by
    intro f
    rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp, Fintype.sum_prod_type]
    rfl
  have hbp : ∀ (i : Fin 3) (s : Fin 2 → Fin 3),
      basisPower (N := 2) i s = if s = (fun _ => i) then 1 else 0 := by
    intro i s
    simp only [basisPower, Fin.prod_univ_two, Pi.single_apply]
    by_cases h0 : s 0 = i
    · by_cases h1 : s 1 = i
      · have hs : s = fun _ => i := by
          funext l
          fin_cases l
          · exact h0
          · exact h1
        simp [hs]
      · have hs : s ≠ fun _ => i := fun e => h1 (by rw [e])
        simp [h1, hs]
    · have hs : s ≠ fun _ => i := fun e => h0 (by rw [e])
      simp [h0, hs]
  have huv : (fun _ => j : Fin 2 → Fin 3) ≠ fun _ => k := fun e => hjk (congrFun e 0)
  have hcs : catState (N := 2) j k θ = fun s => ((if s = (fun _ => j) then Real.cos θ
      else if s = (fun _ => k) then Real.sin θ else 0 : ℝ) : ℂ) := by
    funext s
    simp only [catState, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbp]
    by_cases h1 : s = fun _ => j
    · simp [h1, huv]
    · by_cases h2 : s = fun _ => k
      · simp [h2, huv.symm]
      · simp [h1, h2]
  have hcp : catPerp (N := 2) j k θ = fun s => ((if s = (fun _ => j) then -Real.sin θ
      else if s = (fun _ => k) then Real.cos θ else 0 : ℝ) : ℂ) := by
    funext s
    simp only [catPerp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hbp]
    by_cases h1 : s = fun _ => j
    · simp [h1, huv]
    · by_cases h2 : s = fun _ => k
      · simp [h2, huv.symm]
      · simp [h1, h2]
  have hpair : ∀ j k : Fin 3, j ≠ k → ∃ t0 : ℝ, 0 < t0 ∧ t0 < 1 ∧
      1 - ∑ xs, m xs (fun _ => j) * m xs (fun _ => k) *
          (2 / (t0 * m xs (fun _ => j) + (1 - t0) * m xs (fun _ => k)) -
            m xs (fun _ => k) / (t0 * m xs (fun _ => j) + (1 - t0) * m xs (fun _ => k)) ^ 2) <
        73 / 100 ∧
      1 - ∑ xs, m xs (fun _ => j) * m xs (fun _ => k) *
          (2 / (t0 * m xs (fun _ => j) + (1 - t0) * m xs (fun _ => k)) -
            m xs (fun _ => j) / (t0 * m xs (fun _ => j) + (1 - t0) * m xs (fun _ => k)) ^ 2) <
        73 / 100 := by
    intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · refine ⟨2061 / 4000, by norm_num, by norm_num, ?_, ?_⟩ <;>
        simp only [hsum9, Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> norm_num [detector, Matrix.cons_val_two]
    · refine ⟨191 / 500, by norm_num, by norm_num, ?_, ?_⟩ <;>
        simp only [hsum9, Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> norm_num [detector, Matrix.cons_val_two]
    · refine ⟨1939 / 4000, by norm_num, by norm_num, ?_, ?_⟩ <;>
        simp only [hsum9, Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> norm_num [detector, Matrix.cons_val_two]
    · exact absurd rfl hjk
    · refine ⟨363 / 800, by norm_num, by norm_num, ?_, ?_⟩ <;>
        simp only [hsum9, Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> norm_num [detector, Matrix.cons_val_two]
    · refine ⟨309 / 500, by norm_num, by norm_num, ?_, ?_⟩ <;>
        simp only [hsum9, Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> norm_num [detector, Matrix.cons_val_two]
    · refine ⟨437 / 800, by norm_num, by norm_num, ?_, ?_⟩ <;>
        simp only [hsum9, Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> norm_num [detector, Matrix.cons_val_two]
    · exact absurd rfl hjk
  obtain ⟨t0, ht0a, ht0b, hL0, hL1⟩ := hpair j k hjk
  have hcat : gamma detector (catState (N := 2) j k θ) (catPerp j k θ) ≤ 73 / 100 := by
    rw [hcs, hcp, htwo _ _ huv]
    have hsc := Real.sin_sq_add_cos_sq θ
    set t : ℝ := (Real.cos θ - Real.sin θ) ^ 2 / 2 with ht
    have h1t : 1 - t = (Real.sin θ + Real.cos θ) ^ 2 / 2 := by
      rw [ht]
      linear_combination (-1 : ℝ) * hsc
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by nlinarith [sq_nonneg (Real.sin θ + Real.cos θ)]
    calc _ = ∑ xs, t * (1 - t) * (m xs (fun _ => j) - m xs (fun _ => k)) ^ 2 /
          (t * m xs (fun _ => j) + (1 - t) * m xs (fun _ => k)) :=
          Finset.sum_congr rfl fun xs _ => by
            rw [h1t, ht]
            ring
      _ ≤ _ := htan _ _ t t0 (fun xs => hmpos xs _) (fun xs => hmpos xs _) (hsum1 _) (hsum1 _)
          ht0 ht1 ht0a ht0b
      _ ≤ (1 - t) * (73 / 100) + t * (73 / 100) := by
          have e0 := mul_le_mul_of_nonneg_left hL0.le (sub_nonneg.2 ht1)
          have e1 := mul_le_mul_of_nonneg_left hL1.le ht0
          linarith
      _ = 73 / 100 := by ring
  have hw' : (![1, 0] : Fin 2 → Fin 3) ≠ ![2, 1] := by decide
  have hw1 : witness = fun s => ((if s = ![1, 0] then (1 : ℝ)
      else if s = ![2, 1] then 0 else 0 : ℝ) : ℂ) := by
    funext s
    simp only [witness]
    split_ifs <;> simp
  have hw2 : witnessPerp = fun s => ((if s = ![1, 0] then (0 : ℝ)
      else if s = ![2, 1] then 1 else 0 : ℝ) : ℂ) := by
    funext s
    simp only [witnessPerp]
    split_ifs <;> simp
  have hwval : 73 / 100 < gamma detector witness witnessPerp := by
    rw [hw1, hw2, htwo _ _ hw', hsum9]
    simp only [Fin.sum_univ_three, hm, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num [detector, Matrix.cons_val_two]
  have hn1 : star witness ⬝ᵥ witness = 1 := by
    simp only [dotProduct, Pi.star_apply]
    rw [Fintype.sum_eq_add _ _ hw' fun w hw => by simp [witness, hw.1, hw.2]]
    simp [witness, hw'.symm]
  have hn2 : star witnessPerp ⬝ᵥ witnessPerp = 1 := by
    simp only [dotProduct, Pi.star_apply]
    rw [Fintype.sum_eq_add _ _ hw' fun w hw => by simp [witnessPerp, hw.1, hw.2]]
    simp [witnessPerp, hw'.symm]
  have horth : star witnessPerp ⬝ᵥ witness = 0 := by
    simp only [dotProduct, Pi.star_apply]
    rw [Fintype.sum_eq_add _ _ hw' fun w hw => by simp [witness, witnessPerp, hw.1, hw.2]]
    simp [witness, witnessPerp, hw'.symm]
  have := hmax witness witnessPerp hn1 hn2 horth
  linarith

end D5.S3.Quantum.Measurement.NoisyMeasurementCatOptimalityRefutation
