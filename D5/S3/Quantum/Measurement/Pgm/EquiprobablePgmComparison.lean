/- GID: D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Pgm/EquiprobablePgmComparison
   mirror-E: none(waiver:universal-actual-object-proof)
   anchors: []
   utility: none
   digest: Actual symmetric CFC scores and the complete active-set failure criterion. -/

import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric

/-!
The symmetric CFC score calculation is credited to Hyunho Cha. Mechanism
attribution remains anonymous. The new note is by Haobo Ma then Wenlin Zhang;
CC BY 4.0 applies only to that note. The old literal byline is Wenlin Zhang
and Haobo / trureturing. The original-prior score and nonzero-effect activity
conventions are retained, including singular support powers.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success pgmScore)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)

open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity (diagonal_inverse_sqrt)

/-- Diagonal inverse square-root helper consumed by actual score and effect calculations. -/
theorem inverse_sqrt_two (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
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

theorem sqrt_inverse_square (u : ℝ) (hu : 0 ≤ u) :
    ((Real.sqrt u)⁻¹) ^ 2 = u⁻¹ := by rw [inv_pow, Real.sq_sqrt hu]

theorem sqrt_inverse_product (u v : ℝ) (hu : 0 ≤ u) :
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



open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)

private theorem gap_criterion (q D b δ : ℝ) (hq : 0 < q) (hD : 0 < D) :
    2 * (4 * b ^ 2 / (3 * Real.sqrt D) + 2 * δ ^ 2 / (3 * D)) <
        2 * b ^ 2 / (3 * Real.sqrt q) ↔
      16 * q < D ∧
        2 * δ ^ 2 * Real.sqrt q /
          (Real.sqrt D * (Real.sqrt D - 4 * Real.sqrt q)) < b ^ 2 := by
  let Q := Real.sqrt q
  let T := Real.sqrt D
  have hQ : 0 < Q := Real.sqrt_pos.mpr hq
  have hT : 0 < T := Real.sqrt_pos.mpr hD
  have hQsq : Q ^ 2 = q := Real.sq_sqrt hq.le
  have hTsq : T ^ 2 = D := Real.sq_sqrt hD.le
  by_cases hbig : 16 * q < D
  · have hdiff : 0 < T - 4 * Q := by nlinarith [sq_nonneg (T - 4 * Q)]
    have hid : 2 * b ^ 2 / (3 * Q) -
        2 * (4 * b ^ 2 / (3 * T) + 2 * δ ^ 2 / (3 * D)) =
        (2 * (T - 4 * Q) / (3 * Q * T)) *
          (b ^ 2 - 2 * δ ^ 2 * Q / (T * (T - 4 * Q))) := by
      rw [← hTsq]
      field_simp
      ring_nf
      field_simp [show T - Q * 4 ≠ 0 by linarith]
      ring
    have hfac : 0 < 2 * (T - 4 * Q) / (3 * Q * T) := by positivity
    change _ ↔ 16 * q < D ∧ 2 * δ ^ 2 * Q / (T * (T - 4 * Q)) < b ^ 2
    rw [and_iff_right hbig, ← sub_pos, hid, mul_pos_iff_of_pos_left hfac, sub_pos]
  · have hle : T ≤ 4 * Q := by nlinarith [sq_nonneg (T - 4 * Q)]
    have hcoh : 2 * b ^ 2 / (3 * Q) ≤ 8 * b ^ 2 / (3 * T) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 3 * Q)
        (by positivity : 0 < 3 * T)).mpr
      nlinarith [sq_nonneg b]
    have hcoh' : 2 * b ^ 2 / (3 * Q) ≤ 2 * (4 * b ^ 2 / (3 * T)) := by
      convert hcoh using 1 <;> ring
    have hpop : 0 ≤ 2 * δ ^ 2 / (3 * D) := by positivity
    have hn : ¬ 2 * (4 * b ^ 2 / (3 * T) + 2 * δ ^ 2 / (3 * D)) <
        2 * b ^ 2 / (3 * Q) := by
      intro h
      linarith [hcoh']
    exact iff_of_false hn (not_and_of_not_left _ hbig)

/-- Exact failure in the closed two-active region; either threshold equality
is nonfailure. The formulas remain actual matrix/CFC scores. -/
theorem pair_failure_iff (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
        pgmScore (rho a b c) {0, 1} - 1 / 3 ↔
      16 * (a * (1 - a)) < (2 * a + c) * (3 - 2 * a - c) ∧
        2 * (c - a) ^ 2 * Real.sqrt (a * (1 - a)) /
          (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) *
            (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) -
              4 * Real.sqrt (a * (1 - a)))) < b ^ 2 := by
  rw [(symmetric_scores a b c ha ha1 hc hc1).1,
    (symmetric_scores a b c ha ha1 hc hc1).2]
  exact gap_criterion _ _ _ _ (mul_pos ha (sub_pos.mpr ha1))
    (mul_pos (by positivity) (by linarith))

/-- The full active-set failure iff. It includes the closed pair region as an
essential conjunct; with three active effects the original comparison is equality. -/
theorem active_failure_iff (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 < a * (1 - a) - b ^ 2) :
    (∀ i, (rho a b c i).PosDef ∧ trace (rho a b c i) = 1) ∧
      (let A := Finset.univ.filter (fun i => optimalPovm a b c i ≠ 0)
       2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
           ((A.card : ℝ) - 1) * (pgmScore (rho a b c) A - 1 / 3) ↔
        |c - a| ≤ b ∧
          16 * (a * (1 - a)) < (2 * a + c) * (3 - 2 * a - c) ∧
          2 * (c - a) ^ 2 * Real.sqrt (a * (1 - a)) /
            (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) *
              (Real.sqrt ((2 * a + c) * (3 - 2 * a - c)) -
                4 * Real.sqrt (a * (1 - a)))) < b ^ 2) := by
  refine ⟨states_posDef a b c ha hc hc1 hd, ?_⟩
  dsimp only
  rw [(complete_classification a b c hb).2.2]
  by_cases hpair : |c - a| ≤ b
  · rw [if_pos hpair, and_iff_right hpair]
    norm_num only [Finset.card_pair (show (0 : Fin 3) ≠ 1 by decide),
      Nat.cast_ofNat, sub_self, sub_zero, one_mul, show (2 : ℝ) - 1 = 1 by norm_num]
    exact pair_failure_iff a b c ha ha1 hc hc1
  · norm_num [hpair]

theorem inverse_sqrt_residual (u : ℝ) (hu : 0 < 1 - u) :
    1 / Real.sqrt (1 - u) - 1 =
      u / (Real.sqrt (1 - u) * (1 + Real.sqrt (1 - u))) := by
  have hs := Real.sqrt_pos.mpr hu
  have he := Real.sq_sqrt hu.le
  field_simp
  nlinarith



end D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison

/- The theorem-specific escape registrations in this score/comparison owner
remain unfinished under https://github.com/the-omega-institute/trureturing/issues/27499.
That disclosure is not proof, registration acceptance or independent approval. -/
