/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmScores
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmScores
   mirror-E: none(waiver:universal-cfc-calculation)
   anchors: []
   utility: none
   digest: Exact actual PGM scores for symmetric and diagonal density ensembles. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-!
The symmetric score formulas and the qubit and commuting constructions are due
to Hyunho Cha, as acknowledged by Haobo Ma and Wenlin Zhang in their 4 November
2026 note. The anonymous mechanism manuscript also supplies the symmetric
calculation. CC BY 4.0 applies only to the new Ma–Zhang note.
The admission content is exact universal CFC/actual-score evaluation, including
zero spectral entries in the diagonal family; no sampled certificate is used.
The inherited I score owner does not restrict the universal parameter domains.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.EquiprobablePgmScores
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric (rho)
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)

private theorem diagonal_inverse_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    (s : n → ℝ) (hs : ∀ x, 0 ≤ s x) :
    (diagonal (fun x => (s x : ℂ))) ^ (-(1 / 2) : ℝ) =
      diagonal (fun x => ((Real.sqrt (s x))⁻¹ : ℂ)) := by
  have hS : (diagonal (fun x => (s x : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun x => by
      change (0 : ℂ) ≤ (s x : ℂ)
      exact_mod_cast hs x)
  rw [CFC.rpow_eq_cfc_real hS.nonneg, cfc_diagonal]
  congr 1
  funext x
  congr 1
  rw [Real.rpow_neg (hs x), ← Real.sqrt_eq_rpow]
  push_cast
  rfl

private theorem inverse_sqrt_two (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (diagonal ![(u : ℂ), (v : ℂ)]) ^ (-(1 / 2) : ℝ) =
      diagonal ![(((Real.sqrt u)⁻¹ : ℝ) : ℂ), (((Real.sqrt v)⁻¹ : ℝ) : ℂ)] := by
  have h := diagonal_inverse_sqrt (![u, v] : Fin 2 → ℝ) (by
    intro x; fin_cases x <;> assumption)
  have he : (fun x : Fin 2 => (![u, v] x : ℂ)) = ![(u : ℂ), (v : ℂ)] := by
    funext x; fin_cases x <;> rfl
  rw [he] at h
  convert h using 1 <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

private theorem quadratic_trace (a b c x y : ℝ) :
    (trace (!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] *
      (diagonal ![(x : ℂ), (y : ℂ)] * !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] *
        diagonal ![(x : ℂ), (y : ℂ)]))).re =
      a ^ 2 * x ^ 2 + 2 * b ^ 2 * (x * y) + c ^ 2 * y ^ 2 := by
  have hd : diagonal ![(x : ℂ), (y : ℂ)] = !![(x : ℂ), 0; 0, (y : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hd]
  simp [Matrix.trace_fin_two, Complex.add_re, Complex.mul_re]
  ring

/-- Every diagonal ensemble has this actual Moore–Penrose PGM score, including
singular joint support. Division by a zero spectral mass has the support value zero. -/
theorem diagonal_score {d N : ℕ} (hN : 0 < N) (p : Fin N → Fin d → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (B : Finset (Fin N)) :
    pgmScore (fun i => diagonal (fun x => (p i x : ℂ))) B =
      (1 / (N : ℝ)) * ∑ i ∈ B, ∑ x, (p i x) ^ 2 / (∑ j ∈ B, p j x) := by
  let s : Fin d → ℝ := fun x => (1 / (N : ℝ)) * ∑ j ∈ B, p j x
  have hs (x) : 0 ≤ s x := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => hp i x)
  have hsum : (∑ j ∈ B, (1 / (N : ℂ)) • diagonal (fun x => (p j x : ℂ))) =
      diagonal (fun x => (s x : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [s, Matrix.sum_apply, Finset.mul_sum]
    · simp [Matrix.sum_apply, Matrix.smul_apply, hxy]
  unfold pgmScore
  rw [hsum, diagonal_inverse_sqrt s hs]
  have hsingle (i : Fin N) :
      (trace ((1 / (N : ℂ)) • diagonal (fun x => (p i x : ℂ)) *
        (diagonal (fun x => ((Real.sqrt (s x))⁻¹ : ℂ)) *
          (1 / (N : ℂ)) • diagonal (fun x => (p i x : ℂ)) *
            diagonal (fun x => ((Real.sqrt (s x))⁻¹ : ℂ))))).re =
        (1 / (N : ℝ)) * ∑ x, (p i x) ^ 2 / (∑ j ∈ B, p j x) := by
    simp only [← Matrix.diagonal_smul, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_mul_diagonal,
      trace_diagonal, Complex.re_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hsqrt := Real.sq_sqrt (hs x)
    have hpow : ((Real.sqrt (s x))⁻¹) ^ 2 = (s x)⁻¹ := by
      rw [inv_pow, hsqrt]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div,
      ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.ofReal_re]
    calc
      _ = (1 / (N : ℝ)) ^ 2 * (p i x) ^ 2 * ((Real.sqrt (s x))⁻¹) ^ 2 := by ring
      _ = _ := by
        rw [hpow]
        dsimp [s]
        simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, one_mul]
        have hcancel : (N : ℝ) * (N : ℝ)⁻¹ ^ 2 = (N : ℝ)⁻¹ := by
          field_simp
        linear_combination (p i x) ^ 2 * (∑ j ∈ B, p j x)⁻¹ * hcancel
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hsingle i)

private theorem sqrt_inverse_square (u : ℝ) (hu : 0 ≤ u) :
    ((Real.sqrt u)⁻¹) ^ 2 = u⁻¹ := by rw [inv_pow, Real.sq_sqrt hu]

private theorem sqrt_inverse_product (u v : ℝ) (hu : 0 ≤ u) :
    (Real.sqrt u)⁻¹ * (Real.sqrt v)⁻¹ = (Real.sqrt (u * v))⁻¹ := by
  rw [← mul_inv, ← Real.sqrt_mul hu]

/-- The actual original-prior pair and full PGM scores for every physical
symmetric qubit ensemble. The pair determinant may vanish. -/
theorem symmetric_scores (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    pgmScore (rho a b c) {0, 1} - 1 / 3 =
        2 * b ^ 2 / (3 * Real.sqrt (a * (1 - a))) ∧
      pgmScore (rho a b c) Finset.univ - 1 / 3 =
        4 * b ^ 2 / (3 * Real.sqrt ((2 * a + c) * (3 - 2 * a - c))) +
          2 * (c - a) ^ 2 / (3 * ((2 * a + c) * (3 - 2 * a - c))) := by
  have hv : 0 < 1 - a := sub_pos.mpr ha1
  have hu : 0 < 2 * a + c := by positivity
  have hw : 0 < 3 - 2 * a - c := by linarith
  have hSA : (∑ j ∈ ({0, 1} : Finset (Fin 3)), (1 / (3 : ℂ)) • rho a b c j) =
      diagonal ![((2 * a / 3 : ℝ) : ℂ), ((2 * (1 - a) / 3 : ℝ) : ℂ)] := by
    rw [Finset.sum_pair (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho] <;> push_cast <;> ring
  have hS : (∑ j : Fin 3, (1 / (3 : ℂ)) • rho a b c j) =
      diagonal ![(((2 * a + c) / 3 : ℝ) : ℂ), (((3 - 2 * a - c) / 3 : ℝ) : ℂ)] := by
    rw [Fin.sum_univ_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho] <;> push_cast <;> ring
  have hσ (i : Fin 3) : (1 / (3 : ℂ)) • rho a b c i =
      ![!![((a / 3 : ℝ) : ℂ), ((b / 3 : ℝ) : ℂ);
          ((b / 3 : ℝ) : ℂ), (((1 - a) / 3 : ℝ) : ℂ)],
        !![((a / 3 : ℝ) : ℂ), ((-b / 3 : ℝ) : ℂ);
          ((-b / 3 : ℝ) : ℂ), (((1 - a) / 3 : ℝ) : ℂ)],
        !![((c / 3 : ℝ) : ℂ), 0; 0, (((1 - c) / 3 : ℝ) : ℂ)]] i := by
    fin_cases i <;> ext j k
    all_goals fin_cases j <;> fin_cases k <;> simp [rho] <;> push_cast <;> ring
  constructor
  · unfold pgmScore
    simp only [Nat.cast_ofNat]
    rw [hSA, inverse_sqrt_two _ _ (by positivity) (by positivity),
      Finset.sum_pair (by decide)]
    simp only [Nat.cast_ofNat, hσ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [quadratic_trace, quadratic_trace]
    rw [sqrt_inverse_square _ (by positivity), sqrt_inverse_square _ (by positivity),
      sqrt_inverse_product _ _ (by positivity)]
    have hprod : 2 * a / 3 * (2 * (1 - a) / 3) = (2 / 3 : ℝ) ^ 2 * (a * (1 - a)) := by ring
    rw [hprod, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    have hq : Real.sqrt (a * (1 - a)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos ha hv)).ne'
    field_simp
    ring
  · unfold pgmScore
    simp only [Nat.cast_ofNat]
    rw [hS, inverse_sqrt_two _ _ (by positivity) (by positivity),
      Fin.sum_univ_three]
    simp only [Nat.cast_ofNat, hσ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ← Complex.ofReal_zero]
    rw [quadratic_trace, quadratic_trace, quadratic_trace]
    rw [sqrt_inverse_square _ (by positivity), sqrt_inverse_square _ (by positivity),
      sqrt_inverse_product _ _ (by positivity)]
    have hprod : (2 * a + c) / 3 * ((3 - 2 * a - c) / 3) =
        (1 / 3 : ℝ) ^ 2 * ((2 * a + c) * (3 - 2 * a - c)) := by ring
    rw [hprod, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    have hD : Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hu hw)).ne'
    field_simp [hu.ne', hw.ne', hD]
    <;> ring_nf
    <;> field_simp [show 3 - a * 2 - c ≠ 0 by linarith]
    <;> ring

end D5.S3.Quantum.Measurement.EquiprobablePgmScores
