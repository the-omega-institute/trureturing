/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedCurrentDiagonal
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sum the radial current contraction and regularize its diagonal limit. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

/-!
The radial contraction places the positive mode of `a` at `z` and the
negative mode of `b` at `w`. For the signed cover indices `k = 3n + r`
and `-k` the two eigenspaces are `ζ⁻ʳ` and `ζʳ`, respectively.
The monomial of the two physical currents is
`z^(-k/3-1) w^(k/3-1) = w⁻² t^(k+3)` with `t = (w/z)^(1/3)`.
At the diagonal we use the binomial branch `t = (1+u)^(-1/3)` with
constant term one, where `u = (z-w)/w` and `w ≠ 0`.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

open P48qThirdTwistedField
  (Cartan State annihilatorDual creator fixedDualBases modeRoot annihilatorDual_action pair_modes)
open ThirdEigenspacePairing (p48qAction p48qForm)
open PowerSeries (C X coeff constantCoeff)
open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "ι" => (HahnSeries.ofPowerSeries ℤ ℂ)
local notation "B" => (PowerSeries.binomialSeries (R := ℂ) ℂ)

/-- The first slot is projected to the eigenspace for positive cover residue `r`. -/
def movingGram (r : ℕ) (a b : Cartan) : ℂ :=
  p48qForm (projectAt (r : ℤ) a) b

theorem movingGram_eq_pairing (r : ℕ) (hr : r = 1 ∨ r = 2) (a b : Cartan)
    (ha : p48qAction a = (ζ ^ r) ^ 2 • a) :
    movingGram r a b = p48qForm a b := by
  have hmod : (((r : ℤ) % 3).toNat) = r := by
    rcases hr with h | h <;> subst r <;> decide
  have hz : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hcube : (ζ ^ r) ^ 3 = 1 := by
    rw [pow_right_comm, hz.pow_eq_one, one_pow]
  rw [movingGram, projectAt_eq_fourier, hmod, project_of_action _ hcube a ha]

/-- The actual Gram-dual row has pairing one in each orientation. -/
theorem movingGram_dual (r : ℕ) (hr : r = 1 ∨ r = 2) (i : Fin 16) :
    movingGram r (annihilatorDual fixedDualBases (i, r - 1))
      (creator fixedDualBases (i, r - 1)) = 1 := by
  have hroot : modeRoot (i, r - 1) = ζ ^ r := by
    rcases hr with h | h <;> subst r <;> rfl
  rw [movingGram_eq_pairing r hr _ _ (by
    rw [← hroot]
    exact annihilatorDual_action fixedDualBases (i, r - 1))]
  rw [formSymmetric.eq]
  exact (pair_modes fixedDualBases i i (r - 1)).trans (ite_eq_left rfl)

/-- Positive frequencies `n + α`, with the fractional monomial factored out. -/
def positiveFrequencySeries (α g : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => ((n : ℂ) + α) * g

/-- The weighted series is a linear combination of the geometric series and its square. -/
theorem positiveFrequencySeries_geometric (α g : ℂ) :
    positiveFrequencySeries α g =
      C g * ((PowerSeries.mk 1 : PowerSeries ℂ) ^ 2 +
        C (α - 1) * PowerSeries.mk 1) := by
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add ℂ 1]
  apply PowerSeries.ext
  intro n
  simp only [positiveFrequencySeries, PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_mk,
    Pi.one_apply, mul_one, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  ring

/-- The geometric sum, with its denominator cleared in the power-series ring. -/
theorem positiveFrequencySeries_sum (α g : ℂ) :
    positiveFrequencySeries α g * (1 - X) ^ 2 = C g * (C α + C (1 - α) * X) := by
  let G : PowerSeries ℂ := PowerSeries.mk 1
  have hG : G * (1 - X) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one ℂ
  rw [positiveFrequencySeries_geometric]
  change C g * (G ^ 2 + C (α - 1) * G) * (1 - X) ^ 2 = _
  calc
    _ = C g * ((G * (1 - X)) ^ 2 + C (α - 1) * (G * (1 - X)) * (1 - X)) := by
      ring
    _ = C g * (C α + C (1 - α) * X) := by
      rw [hG, one_pow, mul_one, map_sub, map_sub, map_one]
      ring

/-- The radial contraction in the cover ratio `t`, with the scalar `w⁻²` pulled out. -/
def radialContractionSeries (r : ℕ) (a b : Cartan) : PowerSeries ℂ :=
  X ^ (r + 3) *
    PowerSeries.expand 3 (by decide) (positiveFrequencySeries ((r : ℂ) / 3) (movingGram r a b))

theorem radialContractionSeries_coeff (r n : ℕ) (a b : Cartan) :
    coeff (3 * n + (r + 3)) (radialContractionSeries r a b) =
      ((n : ℂ) + (r : ℂ) / 3) * movingGram r a b := by
  rw [radialContractionSeries, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_expand_mul,
    positiveFrequencySeries, PowerSeries.coeff_mk]

theorem radialContractionSeries_coeff_of_off_sector (r j : ℕ) (a b : Cartan)
    (h : ¬ (r + 3 ≤ j ∧ 3 ∣ j - (r + 3))) :
    coeff j (radialContractionSeries r a b) = 0 := by
  rw [radialContractionSeries, PowerSeries.coeff_X_pow_mul']
  split_ifs with hj
  · exact PowerSeries.coeff_expand_of_not_dvd 3 (by decide) _ (fun hd => h ⟨hj, hd⟩)
  · rfl

/-- The coefficients of the radial contraction are the checked central commutators on
the full state space. Opposite signed indices pair, while distinct frequencies commute. -/
theorem radialContractionSeries_commutator (r n m : ℕ) (a b : Cartan) :
    ⁅mode a (3 * (n : ℤ) + (r : ℤ)), mode b (-(3 * (m : ℤ) + (r : ℤ)))⁆ =
      if n = m then
        coeff (3 * n + (r + 3)) (radialContractionSeries r a b) • (1 : Module.End ℂ State)
      else 0 := by
  have hop : (3 * (n : ℤ) + (r : ℤ)) + -(3 * (m : ℤ) + (r : ℤ)) = 0 ↔ n = m := by
    omega
  have hmod : (3 * (n : ℤ) + (r : ℤ)) % 3 = (r : ℤ) % 3 := by omega
  have hproj : projectAt (3 * (n : ℤ) + (r : ℤ)) a = projectAt (r : ℤ) a := by
    rw [projectAt_eq_fourier, projectAt_eq_fourier, hmod]
  rw [mode_commutator]
  refine (ite_cond_congr (propext hop)).trans ?_
  rw [hproj, radialContractionSeries_coeff]
  have hfreq : (((3 * (n : ℤ) + (r : ℤ) : ℤ) : ℂ) / 3) =
      (n : ℂ) + (r : ℂ) / 3 := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  rw [hfreq, movingGram]

/-- The summed contraction, as a rational expression in the cover ratio `t`. -/
def contractionAtRatio (r : ℕ) (g : ℂ) (t : PowerSeries ℂ) : LaurentSeries ℂ :=
  ι (C g * t ^ (r + 3) * (C ((r : ℂ) / 3) + C (1 - (r : ℂ) / 3) * t ^ 3)) /
    ι ((1 - t ^ 3) ^ 2)

private theorem ofPowerSeries_ne_zero {p : PowerSeries ℂ} (hp : p ≠ 0) : ι p ≠ 0 := by
  intro h
  apply hp
  exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero ι).symm)

/-- Expanding the rational sum at `t = 0` gives the actual radial series. -/
theorem radialContractionSeries_sum (r : ℕ) (a b : Cartan) :
    ι (radialContractionSeries r a b) = contractionAtRatio r (movingGram r a b) X := by
  have hbase : (1 : PowerSeries ℂ) - X ^ 3 ≠ 0 := by
    intro h
    have h₀ := congrArg (constantCoeff (R := ℂ)) h
    simpa using h₀
  unfold contractionAtRatio
  apply (eq_div_iff (ofPowerSeries_ne_zero (pow_ne_zero 2 hbase))).2
  rw [← map_mul]
  have h := congrArg (PowerSeries.expand 3 (by decide : (3 : ℕ) ≠ 0) (R := ℂ))
    (positiveFrequencySeries_sum ((r : ℂ) / 3) (movingGram r a b))
  simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.expand_C,
    PowerSeries.expand_X] at h
  apply congrArg ι
  unfold radialContractionSeries
  rw [mul_assoc, h, map_sub, map_one]
  ring

/-- The cover ratio in the coordinate `u = (z-w)/w`, with constant term one. -/
def diagonalCoverRatio : PowerSeries ℂ :=
  B (-(1 / 3))

private theorem binomial_pow (s : ℂ) (n : ℕ) : B s ^ n = B ((n : ℂ) * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, PowerSeries.binomialSeries_add]

private theorem diagonalCoverRatio_cube : diagonalCoverRatio ^ 3 = B (-1) := by
  rw [diagonalCoverRatio, binomial_pow, show ((3 : ℕ) : ℂ) * (-(1 / 3)) = -1 by norm_num]

theorem diagonalCoverRatio_branch :
    constantCoeff diagonalCoverRatio = 1 ∧ diagonalCoverRatio ^ 3 * (1 + X) = 1 := by
  have h₁ : B (1 : ℂ) = 1 + X := by
    simpa only [Nat.cast_one, pow_one] using
      (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)
  refine ⟨by simp [diagonalCoverRatio], ?_⟩
  rw [diagonalCoverRatio_cube, ← h₁, ← PowerSeries.binomialSeries_add,
    neg_add_cancel, PowerSeries.binomialSeries_zero]

/-- The numerator of the normalized diagonal Laurent series. -/
def diagonalNumerator (α : ℂ) : PowerSeries ℂ :=
  B (-α) * (1 + C α * X)

/-- Re-expand the same rational sum at the diagonal branch. The two factors
of `(1+u)⁻¹` cancel against the factors in `(1-t³)²`. -/
theorem contractionAtRatio_diagonal (r : ℕ) (g : ℂ) :
    contractionAtRatio r g diagonalCoverRatio =
      ι (C g * diagonalNumerator ((r : ℂ) / 3)) / ι ((X : PowerSeries ℂ) ^ 2) := by
  let q : PowerSeries ℂ := B (-1)
  let α : ℂ := (r : ℂ) / 3
  have hc : diagonalCoverRatio ^ 3 = q := diagonalCoverRatio_cube
  have hq : q * (1 + X) = 1 := by
    rw [← hc]
    exact diagonalCoverRatio_branch.2
  have hq₀ : q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hq
    exact zero_ne_one hq
  have hr : diagonalCoverRatio ^ r = B (-α) := by
    rw [diagonalCoverRatio, binomial_pow]
    exact congrArg B (by dsimp [α]; ring)
  have hden : 1 - q = X * q := by
    calc
      1 - q = q * (1 + X) - q := by rw [hq]
      _ = X * q := by ring
  have hnum : C α + C (1 - α) * q = q * (1 + C α * X) := by
    calc
      _ = C α * (q * (1 + X)) + (1 - C α) * q := by rw [hq, mul_one, map_sub, map_one]
      _ = _ := by ring
  unfold contractionAtRatio diagonalNumerator
  change ι (C g * diagonalCoverRatio ^ (r + 3) * (C α + C (1 - α) * diagonalCoverRatio ^ 3)) /
      ι ((1 - diagonalCoverRatio ^ 3) ^ 2) =
    ι (C g * (B (-α) * (1 + C α * X))) / ι ((X : PowerSeries ℂ) ^ 2)
  rw [pow_add diagonalCoverRatio r 3, hr, hc, hden, hnum]
  apply (div_eq_div_iff
    (ofPowerSeries_ne_zero (pow_ne_zero 2 (mul_ne_zero PowerSeries.X_ne_zero hq₀)))
    (ofPowerSeries_ne_zero (pow_ne_zero 2 PowerSeries.X_ne_zero))).2
  simp only [map_mul, map_pow]
  ring

private theorem coeff_succ_diagonalNumerator (α : ℂ) (n : ℕ) :
    coeff (n + 1) (diagonalNumerator α) =
      Ring.choose (-α) (n + 1) + Ring.choose (-α) n * α := by
  rw [diagonalNumerator, mul_add, mul_one, ← mul_assoc, map_add, PowerSeries.coeff_succ_mul_X,
    PowerSeries.coeff_mul_C]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- The entire numerator minus one is divisible by `u²`. Its quotient has
constant term `α(1-α)/2`. -/
theorem diagonalNumerator_factor (α : ℂ) :
    ∃ R : PowerSeries ℂ, diagonalNumerator α - 1 = X ^ 2 * R ∧
      constantCoeff R = α * (1 - α) / 2 := by
  have h₀ : coeff 0 (diagonalNumerator α - 1) = 0 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, diagonalNumerator]
  have h₁ : coeff 1 (diagonalNumerator α - 1) = 0 := by
    rw [map_sub, PowerSeries.coeff_one, if_neg (by decide : (1 : ℕ) ≠ 0), sub_zero]
    change coeff (0 + 1) (diagonalNumerator α) = 0
    rw [coeff_succ_diagonalNumerator, Ring.choose_one_right, Ring.choose_zero_right, one_mul,
      neg_add_cancel]
  have hchoose : Ring.choose (-α) 2 = (-α) * (-α - 1) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    rw [mul_comm (Ring.choose (-α) 2) 2]
    simpa only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one,
      show (2 : ℕ) - 1 = 1 by decide, Ring.choose_one_right] using
      (Ring.choose_smul_choose (-α) (n := 2) (k := 1) (by decide))
  have h₂ : coeff 2 (diagonalNumerator α - 1) = α * (1 - α) / 2 := by
    rw [map_sub, PowerSeries.coeff_one, if_neg (by decide : (2 : ℕ) ≠ 0), sub_zero]
    change coeff (1 + 1) (diagonalNumerator α) = _
    rw [coeff_succ_diagonalNumerator, show (1 : ℕ) + 1 = 2 by decide, hchoose,
      Ring.choose_one_right]
    ring
  have hd : (X : PowerSeries ℂ) ^ 2 ∣ diagonalNumerator α - 1 := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro n hn
    interval_cases n
    · exact h₀
    · exact h₁
  obtain ⟨R, hR⟩ := hd
  refine ⟨R, hR, ?_⟩
  have h := congrArg (coeff (R := ℂ) 2) hR
  change coeff 2 (diagonalNumerator α - 1) = coeff (0 + 2) (X ^ 2 * R) at h
  rw [h₂, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  exact h.symm

/-- Remove the full principal part from the moving contraction at the diagonal.
The remaining Laurent series comes from a power series with constant term
`w⁻² · Gram(a,b) / 9` in either orientation. -/
theorem movingContraction_diagonal_regularization (r : ℕ) (hr : r = 1 ∨ r = 2)
    (a b : Cartan) (w : ℂ) :
    ∃ R : PowerSeries ℂ,
      contractionAtRatio r ((w ^ 2)⁻¹ * movingGram r a b) diagonalCoverRatio -
          ι (C ((w ^ 2)⁻¹ * movingGram r a b)) / ι ((X : PowerSeries ℂ) ^ 2) = ι R ∧
      constantCoeff R = (w ^ 2)⁻¹ * movingGram r a b / 9 := by
  let g : ℂ := (w ^ 2)⁻¹ * movingGram r a b
  let α : ℂ := (r : ℂ) / 3
  obtain ⟨S, hS, hS₀⟩ := diagonalNumerator_factor α
  have hα : α * (1 - α) / 2 = (1 : ℂ) / 9 := by
    rcases hr with h | h <;> simp [α, h] <;> norm_num
  refine ⟨C g * S, ?_, ?_⟩
  · change contractionAtRatio r g diagonalCoverRatio -
        ι (C g) / ι ((X : PowerSeries ℂ) ^ 2) = ι (C g * S)
    rw [contractionAtRatio_diagonal, ← sub_div, ← map_sub]
    apply (div_eq_iff (ofPowerSeries_ne_zero (pow_ne_zero 2 PowerSeries.X_ne_zero))).2
    rw [← map_mul]
    apply congrArg ι
    calc
      C g * diagonalNumerator α - C g = C g * (diagonalNumerator α - 1) := by
        rw [mul_sub, mul_one]
      _ = (C g * S) * X ^ 2 := by
        rw [hS]
        ring
  · change constantCoeff (C g * S) = g / 9
    rw [map_mul, PowerSeries.constantCoeff_C, hS₀, hα]
    ring

/-- For an actual dual row in either moving orientation, the scalar diagonal correction
is `w⁻² / 9`. -/
theorem gramDualContraction_diagonal_regularization (r : ℕ) (hr : r = 1 ∨ r = 2)
    (i : Fin 16) (w : ℂ) :
    ∃ R : PowerSeries ℂ,
      contractionAtRatio r (w ^ 2)⁻¹ diagonalCoverRatio -
          ι (C (w ^ 2)⁻¹) / ι ((X : PowerSeries ℂ) ^ 2) = ι R ∧
      constantCoeff R = (w ^ 2)⁻¹ / 9 := by
  simpa only [movingGram_dual r hr i, mul_one] using
    movingContraction_diagonal_regularization r hr
      (annihilatorDual fixedDualBases (i, r - 1)) (creator fixedDualBases (i, r - 1)) w

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
