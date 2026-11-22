/- GID: D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/ThermalOperationDegeneracyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation.claim; result=D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation.result; claim=D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation.claim
   digest: A qutrit thermal operation exceeds the population bound of every finite bath capped at degeneracy three. -/

import D5.S3.Quantum.Decoherence.GibbsBathBandwidth
import D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A finite Gibbs qutrit channel can exceed the population bound of every cap-three bath. -/

set_option autoImplicit false

namespace D5.S3.QuantumChannels.ThermalDegeneracyCertificate

open scoped BigOperators

private def potential : Fin 4 → Fin 4 → ℕ :=
  ![![0, 11, 18, 24],
    ![14, 20, 24, 24],
    ![20, 24, 24, 24],
    ![24, 24, 24, 24]]

private theorem potential_step : ∀ a b c : Fin 4,
    8 * c.val + potential c a ≤ 22 * (c.val - (a.val + b.val)) + 2 * potential a b := by
  decide +kernel

noncomputable section

/-- The unnormalized Gibbs weight at inverse temperature `log 2`. -/
def boltzmann (t : ℝ) : ℝ := Real.exp (-(Real.log 2) * t)

/-- The number of ground rows left unmatched by the two lower bath fibers. -/
def deficit (g : ℝ → ℕ) (t : ℝ) : ℕ := g t - (g (t - 1) + g (t - 2))

private theorem boltzmann_add_one (t : ℝ) : boltzmann (t + 1) = boltzmann t / 2 := by
  simp only [boltzmann, mul_add, Real.exp_add, mul_one, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv]

/-- A degeneracy cap of three forces the weighted deficit to be at least four elevenths
of the weighted multiplicity for every finite real energy distribution. -/
private theorem weighted_sum_le_eleven_fourths_deficit
    (s : Finset ℝ) (g : ℝ → ℕ) (hs : ∀ t ∉ s, g t = 0) (hcap : ∀ t, g t ≤ 3) :
    (∑ t ∈ s, boltzmann t * (g t : ℝ)) ≤
      (11 / 4 : ℝ) * ∑ t ∈ s, boltzmann t * (deficit g t : ℝ) := by
  classical
  let shift : ℝ → ℝ := fun t => t + 1
  let A : Finset ℝ := s ∪ s.image shift
  let F : Finset ℝ := A ∪ A.image shift
  let count : ℝ → Fin 4 := fun t => ⟨g t, Nat.lt_succ_of_le (hcap t)⟩
  let q : ℝ → ℝ := fun t => (potential (count t) (count (t - 1)) : ℝ)
  have hpoint (t : ℝ) :
      8 * (g t : ℝ) + q t ≤ 22 * (deficit g t : ℝ) + 2 * q (t - 1) := by
    have h := potential_step (count (t - 1)) (count (t - 2)) (count t)
    change 8 * g t + potential (count t) (count (t - 1)) ≤
      22 * deficit g t + 2 * potential (count (t - 1)) (count (t - 2)) at h
    have hsub : t - 1 - 1 = t - 2 := by ring
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, q, hsub] using
      (Nat.cast_le (α := ℝ)).mpr h

  have hsA : s ⊆ A := Finset.subset_union_left
  have hAF : A ⊆ F := Finset.subset_union_left
  have hshift_mem {B : Finset ℝ} {t : ℝ} (ht : t - 1 ∈ B) : t ∈ B.image shift := by
    simpa only [shift, sub_add_cancel] using Finset.mem_image_of_mem shift ht
  have hq_zero {t : ℝ} (ht : t ∉ A) : q t = 0 := by
    have hnow : t ∉ s := fun h => ht (hsA h)
    have hprev : t - 1 ∉ s := fun h => ht (Finset.mem_union.mpr (Or.inr (hshift_mem h)))
    have hcount_zero (u : ℝ) (hu : g u = 0) : count u = 0 := Fin.ext hu
    have h00 : potential 0 0 = 0 := by decide +kernel
    simp only [q, hcount_zero t (hs t hnow), hcount_zero (t - 1) (hs (t - 1) hprev),
      h00, Nat.cast_zero]

  -- Enlarge the sums to a support containing both potential terms.
  have hg_sum : (∑ t ∈ s, boltzmann t * (g t : ℝ)) =
      ∑ t ∈ F, boltzmann t * (g t : ℝ) := by
    apply Finset.sum_subset (hsA.trans hAF)
    intro t _ ht
    simp only [hs t ht, Nat.cast_zero, mul_zero]
  have hd_sum : (∑ t ∈ s, boltzmann t * (deficit g t : ℝ)) =
      ∑ t ∈ F, boltzmann t * (deficit g t : ℝ) := by
    apply Finset.sum_subset (hsA.trans hAF)
    intro t _ ht
    simp only [deficit, hs t ht, Nat.zero_sub, Nat.cast_zero, mul_zero]
  have hq_sum : (∑ t ∈ A, boltzmann t * q t) = ∑ t ∈ F, boltzmann t * q t := by
    apply Finset.sum_subset hAF
    intro t _ ht
    rw [hq_zero ht, mul_zero]

  have hshiftAF : A.image shift ⊆ F := Finset.subset_union_right
  have hshift_injective : Function.Injective shift := fun _ _ h => add_right_cancel h
  have hcancel : (∑ t ∈ F, boltzmann t * q (t - 1)) =
      (∑ t ∈ F, boltzmann t * q t) / 2 := by
    calc
      _ = ∑ t ∈ A.image shift, boltzmann t * q (t - 1) := by
        symm
        apply Finset.sum_subset hshiftAF
        intro t _ ht
        have hprev : t - 1 ∉ A := fun h => ht (hshift_mem h)
        rw [hq_zero hprev, mul_zero]
      _ = ∑ t ∈ A, boltzmann (shift t) * q (shift t - 1) :=
        Finset.sum_image hshift_injective.injOn
      _ = ∑ t ∈ A, (boltzmann t * q t) / 2 := by
        apply Finset.sum_congr rfl
        intro t _
        simp only [shift, boltzmann_add_one, add_sub_cancel_right]
        ring
      _ = (∑ t ∈ A, boltzmann t * q t) / 2 :=
        (Finset.sum_div A (fun t => boltzmann t * q t) 2).symm
      _ = _ := by rw [hq_sum]

  have hsum :
      (∑ t ∈ F, (8 * (boltzmann t * (g t : ℝ)) + boltzmann t * q t)) ≤
        ∑ t ∈ F, (22 * (boltzmann t * (deficit g t : ℝ)) + 2 * (boltzmann t * q (t - 1))) := by
    apply Finset.sum_le_sum
    intro t _
    calc
      _ = boltzmann t * (8 * (g t : ℝ) + q t) := by ring
      _ ≤ boltzmann t * (22 * (deficit g t : ℝ) + 2 * q (t - 1)) :=
        mul_le_mul_of_nonneg_left (hpoint t) (Real.exp_nonneg _)
      _ = _ := by ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← hg_sum, ← hd_sum, hcancel] at hsum
  linarith only [hsum]

end

end D5.S3.QuantumChannels.ThermalDegeneracyCertificate

namespace D5.S3.QuantumChannels.ThermalDegeneracyShellBound

noncomputable section

open scoped BigOperators Classical Kronecker Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)
open GibbsBathBandwidth (diagonalReal gibbsWeight)

/-- The qutrit energies in units of the level spacing. -/
def levels (j : Fin 3) : ℝ := (j.val : ℝ)

private theorem levels_zero : levels 0 = 0 := by norm_num [levels]
private theorem levels_one : levels 1 = 1 := by norm_num [levels]
private theorem levels_two : levels 2 = 2 := by norm_num [levels]

/-- The initial populations in the energy basis. -/
def populations : Fin 3 → ℝ := ![0, 2 / 3, 1 / 3]

def inputState : Matrix (Fin 3) (Fin 3) ℂ := diagonalReal populations

/-- The unnormalized Gibbs weight at inverse temperature `log 2`. -/
def boltzmann (t : ℝ) : ℝ := Real.exp (-(Real.log 2) * t)

def partition {m : ℕ} (e : Fin m → ℝ) : ℝ := ∑ a, boltzmann (e a)

def bathState {m : ℕ} (e : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonalReal (gibbsWeight (Real.log 2) e)

/-- The finite thermal output in the given energy bases. -/
def thermalOutput {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ)
    (ρ : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceRight (U * (ρ ⊗ₖ bathState e) * Uᴴ)

def bathEnergies {m : ℕ} (e : Fin m → ℝ) : Finset ℝ := Finset.univ.image e

def bathFiber {m : ℕ} (e : Fin m → ℝ) (t : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun a => e a = t)

def multiplicity {m : ℕ} (e : Fin m → ℝ) (t : ℝ) : ℕ := (bathFiber e t).card

/-- Input basis indices in shell `t` whose qutrit coordinate is excited. -/
def excitedColumns {m : ℕ} (e : Fin m → ℝ) (t : ℝ) : Finset (Fin 3 × Fin m) :=
  Finset.univ.filter (fun a => a.1 ≠ 0 ∧ levels a.1 + e a.2 = t)

/-- Sum of squared entries from excited columns to ground rows in shell `t`. -/
def shellTransfer {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ) (t : ℝ) : ℝ :=
  ∑ b ∈ bathFiber e t, ∑ a ∈ excitedColumns e t, Complex.normSq (U (0, b) a)

private theorem boltzmann_add (s t : ℝ) : boltzmann (s + t) = boltzmann s * boltzmann t := by
  simp only [boltzmann, mul_add, Real.exp_add]

private theorem boltzmann_nat (n : ℕ) : boltzmann (n : ℝ) = (1 / 2 : ℝ) ^ n := by
  unfold boltzmann
  rw [mul_comm (-(Real.log 2)) (n : ℝ), Real.exp_nat_mul, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]

private theorem partition_pos {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ) : 0 < partition e := by
  unfold partition
  exact Finset.sum_pos (fun a _ => Real.exp_pos (-(Real.log 2) * e a))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- The Gibbs denominator expressed as a sum over distinct bath energies. -/
private theorem partition_eq_sum_multiplicity {m : ℕ} (e : Fin m → ℝ) :
    partition e = ∑ t ∈ bathEnergies e, boltzmann t * (multiplicity e t : ℝ) := by
  calc
    partition e = ∑ t ∈ bathEnergies e, ∑ a ∈ bathFiber e t, boltzmann t :=
      (Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := bathEnergies e) (g := e)
        (fun a ha => Finset.mem_image_of_mem e ha) boltzmann).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp [multiplicity, nsmul_eq_mul, mul_comm]

/-- The excited columns come from the two lower bath fibers. -/
private theorem excitedColumns_card {m : ℕ} (e : Fin m → ℝ) (t : ℝ) :
    (excitedColumns e t).card = multiplicity e (t - 1) + multiplicity e (t - 2) := by
  have h1 (a : Fin m) : levels 1 + e a = t ↔ e a = t - 1 := by
    rw [levels_one]
    constructor <;> intro h <;> linarith
  have h2 (a : Fin m) : levels 2 + e a = t ↔ e a = t - 2 := by
    rw [levels_two]
    constructor <;> intro h <;> linarith
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  simp only [excitedColumns, multiplicity, bathFiber, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [h1, h2, h10, h20]

/-- The two dimensions of the excited-to-ground block each bound its transfer sum. -/
private theorem shellTransfer_le {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ) (t : ℝ) :
    shellTransfer e U t ≤
      min (multiplicity e t : ℝ)
        ((multiplicity e (t - 1) : ℝ) + (multiplicity e (t - 2) : ℝ)) := by
  have hU := RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary U.property
  have hrow (r : Fin 3 × Fin m) :
      (∑ a : Fin 3 × Fin m, Complex.normSq (U r a)) = 1 := by
    simpa only [RHLinalg.normSqMatrix, Matrix.of_apply, Complex.sq_norm] using
      (sum_row_of_mem_doublyStochastic hU r)
  have hcol (a : Fin 3 × Fin m) :
      (∑ r : Fin 3 × Fin m, Complex.normSq (U r a)) = 1 := by
    simpa only [RHLinalg.normSqMatrix, Matrix.of_apply, Complex.sq_norm] using
      (sum_col_of_mem_doublyStochastic hU a)
  apply le_min
  · calc
      shellTransfer e U t ≤ ∑ _b ∈ bathFiber e t, (1 : ℝ) := by
        unfold shellTransfer
        apply Finset.sum_le_sum
        intro b _
        rw [← hrow (0, b)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Complex.normSq_nonneg _)
      _ = (multiplicity e t : ℝ) := by simp [multiplicity]
  · calc
      shellTransfer e U t =
          ∑ a ∈ excitedColumns e t, ∑ b ∈ bathFiber e t, Complex.normSq (U (0, b) a) :=
        Finset.sum_comm
      _ ≤ ∑ _a ∈ excitedColumns e t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        calc
          (∑ b ∈ bathFiber e t, Complex.normSq (U (0, b) a)) ≤
              ∑ b : Fin m, Complex.normSq (U (0, b) a) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => Complex.normSq_nonneg _)
          _ ≤ ∑ j : Fin 3, ∑ b : Fin m, Complex.normSq (U (j, b) a) :=
            Finset.single_le_sum
              (f := fun j : Fin 3 => ∑ b : Fin m, Complex.normSq (U (j, b) a))
              (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
              (Finset.mem_univ 0)
          _ = 1 := by simpa only [Fintype.sum_prod_type] using hcol a
      _ = ((excitedColumns e t).card : ℝ) := by simp
      _ = _ := by rw [excitedColumns_card, Nat.cast_add]

/-- A diagonal qutrit input gives the Gibbs-weighted squared-entry population formula. -/
private theorem output_population_eq_sum {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ) (p : Fin 3 → ℝ) (j : Fin 3) :
    (thermalOutput e U (diagonalReal p) j j).re =
      ∑ b : Fin m, ∑ a : Fin 3 × Fin m,
        (p a.1 * gibbsWeight (Real.log 2) e a.2) * Complex.normSq (U (j, b) a) := by
  let q : Fin 3 × Fin m → ℝ := fun a => p a.1 * gibbsWeight (Real.log 2) e a.2
  have htensor : diagonalReal p ⊗ₖ bathState e = diagonalReal q := by
    simp only [bathState, diagonalReal, Matrix.diagonal_kronecker_diagonal, q,
      Complex.ofReal_mul]
  have hdiag (r : Fin 3 × Fin m) :
      (U * diagonalReal q * Uᴴ) r r =
        ∑ a : Fin 3 × Fin m, ((q a * Complex.normSq (U r a) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [diagonalReal, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro a _
    calc
      U r a * (q a : ℂ) * star (U r a) = (q a : ℂ) * (U r a * star (U r a)) := by ring
      _ = _ := by
        rw [Complex.star_def, Complex.mul_conj]
        simp only [q, Complex.ofReal_mul]
  rw [thermalOutput, htensor]
  change (∑ b : Fin m, (U * diagonalReal q * Uᴴ) (j, b) (j, b)).re =
    ∑ b : Fin m, ∑ a : Fin 3 × Fin m, q a * Complex.normSq (U (j, b) a)
  simp only [hdiag, Complex.re_sum, Complex.ofReal_re]

private theorem energy_entry_zero {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ)
    (hU : IsEnergyConserving levels e U) (r a : Fin 3 × Fin m)
    (hne : levels r.1 + e r.2 ≠ levels a.1 + e a.2) : U r a = 0 := by
  have h := congrArg (fun M : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ => M r a) hU
  change (U * Matrix.diagonal (fun i : Fin 3 × Fin m => ((levels i.1 + e i.2 : ℝ) : ℂ))) r a =
    (Matrix.diagonal (fun i : Fin 3 × Fin m => ((levels i.1 + e i.2 : ℝ) : ℂ)) * U) r a at h
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  by_contra hzero
  apply hne
  apply Complex.ofReal_injective
  exact (mul_left_cancel₀ hzero (h.trans (mul_comm _ _))).symm

private theorem excited_population {j : Fin 3} (hj : j ≠ 0) :
    populations j = (4 / 3 : ℝ) * boltzmann (levels j) := by
  have h1 : boltzmann 1 = (1 / 2 : ℝ) := by
    simpa only [Nat.cast_one, pow_one] using boltzmann_nat 1
  have h2 : boltzmann 2 = (1 / 2 : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat] using boltzmann_nat 2
  fin_cases j
  · exact (hj rfl).elim
  · norm_num [populations, levels, h1]
  · norm_num [populations, levels, h2]

private theorem ground_row_eq {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ)
    (hU : IsEnergyConserving levels e U) (b : Fin m) :
    (∑ a : Fin 3 × Fin m,
      (populations a.1 * gibbsWeight (Real.log 2) e a.2) * Complex.normSq (U (0, b) a)) =
    ((4 / 3 : ℝ) / partition e * boltzmann (e b)) *
      ∑ a ∈ excitedColumns e (e b), Complex.normSq (U (0, b) a) := by
  calc
    _ = ∑ a ∈ excitedColumns e (e b),
          (populations a.1 * gibbsWeight (Real.log 2) e a.2) * Complex.normSq (U (0, b) a) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      by_cases hzero : a.1 = 0
      · have hp : populations a.1 = 0 := by rw [hzero] <;> rfl
        rw [hp, zero_mul, zero_mul]
      · have hne : levels a.1 + e a.2 ≠ e b := by
          intro he
          exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero, he⟩)
        have hu : U (0, b) a = 0 := by
          apply energy_entry_zero e U hU
          simpa only [levels_zero, zero_add] using Ne.symm hne
        rw [hu, Complex.normSq_zero, mul_zero]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have hmem : a.1 ≠ 0 ∧ levels a.1 + e a.2 = e b := (Finset.mem_filter.mp ha).2
      rw [excited_population hmem.1]
      change ((4 / 3 : ℝ) * boltzmann (levels a.1) *
        (boltzmann (e a.2) / partition e)) * _ = _
      rw [← hmem.2, boltzmann_add]
      ring

/-- Ground output is a sum of the Gibbs-weighted transfers over the distinct bath energies. -/
private theorem ground_population_eq_shell_sum {m : ℕ} (e : Fin m → ℝ)
    (U : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ)
    (hU : IsEnergyConserving levels e U) :
    (thermalOutput e U inputState 0 0).re =
      ((4 / 3 : ℝ) / partition e) *
        ∑ t ∈ bathEnergies e, boltzmann t * shellTransfer e U t := by
  rw [inputState, output_population_eq_sum]
  let row : Fin m → ℝ :=
    fun b => ∑ a ∈ excitedColumns e (e b), Complex.normSq (U (0, b) a)
  calc
    _ = ∑ b, ((4 / 3 : ℝ) / partition e * boltzmann (e b)) * row b :=
      Finset.sum_congr rfl (fun b _ => ground_row_eq e U hU b)
    _ = ∑ t ∈ bathEnergies e, ∑ b ∈ bathFiber e t,
          ((4 / 3 : ℝ) / partition e * boltzmann (e b)) * row b :=
      (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := bathEnergies e) (g := e)
        (fun b hb => Finset.mem_image_of_mem e hb) _).symm
    _ = ∑ t ∈ bathEnergies e, ((4 / 3 : ℝ) / partition e * boltzmann t) * shellTransfer e U t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [shellTransfer, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hbt : e b = t := (Finset.mem_filter.mp hb).2
      dsimp only [row]
      rw [hbt]
    _ = _ := by simp only [mul_assoc, Finset.mul_sum]

/-- The shell bound for every finite bath spectrum and every exactly
energy-preserving joint unitary, with the Gibbs partition in the denominator. -/
private theorem ground_population_le_shell_sum {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ) (hU : IsEnergyConserving levels e U) :
    (thermalOutput e U inputState 0 0).re ≤
      ((4 / 3 : ℝ) / partition e) *
        ∑ t ∈ bathEnergies e, boltzmann t *
          min (multiplicity e t : ℝ)
            ((multiplicity e (t - 1) : ℝ) + (multiplicity e (t - 2) : ℝ)) := by
  rw [ground_population_eq_shell_sum e U hU]
  have hcoeff : 0 ≤ (4 / 3 : ℝ) / partition e := div_nonneg (by norm_num) (partition_pos hm e).le
  apply mul_le_mul_of_nonneg_left _ hcoeff
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (shellTransfer_le e U t) (Real.exp_nonneg _)

end

end D5.S3.QuantumChannels.ThermalDegeneracyShellBound

namespace D5.S3.QuantumChannels.ThermalDegeneracyWitness

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open GibbsBathBandwidth (diagonalReal gibbsWeight gibbsWeight_pos sum_gibbsWeight)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)

/-- The 20 bath basis states, with energy multiplicities `1, 1, 2, 3, 5, 8`. -/
def bathLevel (b : Fin 20) : ℕ :=
  (#v[0, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5] :
    Vector ℕ 20).get b

private abbrev Joint := Fin 3 × Fin 20

private abbrev flatten : Joint ≃ Fin 60 := finProdFinEquiv

/-- The joint basis table, in the order `20 * s + b`. -/
private def flatImage (x : Fin 60) : Fin 60 :=
  (#v[0, 20, 21, 40, 22, 23, 41, 24, 25, 26, 42, 43, 27, 28, 29, 30, 31, 44, 45, 46,
      1, 2, 4, 5, 7, 8, 9, 12, 13, 14, 15, 16, 32, 33, 34, 35, 36, 37, 38, 39,
      3, 6, 10, 11, 17, 18, 19, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59] :
    Vector (Fin 60) 60).get x

private theorem flatImage_involutive : ∀ x : Fin 60, flatImage (flatImage x) = x := by
  decide +kernel

private def flatPermutation : Equiv.Perm (Fin 60) where
  toFun := flatImage
  invFun := flatImage
  left_inv := flatImage_involutive
  right_inv := flatImage_involutive

private def jointPermutation : Equiv.Perm Joint :=
  (flatten.trans flatPermutation).trans flatten.symm

private def totalLevel (x : Joint) : ℕ := x.1.val + bathLevel x.2

private theorem flatImage_preserves_totalLevel : ∀ x : Fin 60,
    totalLevel (flatten.symm (flatImage x)) = totalLevel (flatten.symm x) := by
  decide +kernel

private theorem jointPermutation_preserves_totalLevel (x : Joint) :
    totalLevel (jointPermutation x) = totalLevel x := by
  change totalLevel (flatten.symm (flatImage (flatten x))) = totalLevel x
  simpa only [Equiv.symm_apply_apply] using flatImage_preserves_totalLevel (flatten x)

private def energyWeight (b : Fin 20) : ℚ := (1 / 2 : ℚ) ^ bathLevel b

private def partitionWeight : ℚ := ∑ b : Fin 20, energyWeight b

private theorem partitionWeight_eq : partitionWeight = 47 / 16 := by
  decide +kernel

private def rationalGibbsWeight (b : Fin 20) : ℚ := energyWeight b / partitionWeight

def inputPopulation (s : Fin 3) : ℚ :=
  (![0, 2 / 3, 1 / 3] : Fin 3 → ℚ) s

private theorem rational_ground_entry :
    (∑ b : Fin 20, inputPopulation (jointPermutation (0, b)).1 *
      rationalGibbsWeight (jointPermutation (0, b)).2) = 124 / 141 := by
  simp only [rationalGibbsWeight, partitionWeight_eq]
  decide +kernel

noncomputable section

/-- The evenly spaced qutrit Hamiltonian's diagonal. -/
def systemEnergy (s : Fin 3) : ℝ := (s.val : ℝ)

/-- The bath Hamiltonian's diagonal in the chosen basis. -/
def bathEnergy (b : Fin 20) : ℝ := (bathLevel b : ℝ)

/-- Inverse temperature for a Boltzmann factor of `1 / 2` across one gap. -/
def inverseTemperature : ℝ := Real.log 2

private theorem inverseTemperature_pos : 0 < inverseTemperature :=
  Real.log_pos (by norm_num)

/-- The normalized Gibbs state in the bath energy basis. -/
def bathState : Matrix (Fin 20) (Fin 20) ℂ :=
  diagonalReal (gibbsWeight inverseTemperature bathEnergy)

/-- The qutrit input with populations `0, 2 / 3, 1 / 3`. -/
def inputState : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonalReal (fun s => (inputPopulation s : ℝ))

private theorem exp_energy_eq (b : Fin 20) :
    Real.exp (-inverseTemperature * bathEnergy b) = (energyWeight b : ℝ) := by
  have hbase : Real.exp (-inverseTemperature) = 1 / 2 := by
    rw [inverseTemperature, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    Real.exp (-inverseTemperature * bathEnergy b) =
        Real.exp ((bathLevel b : ℝ) * -inverseTemperature) := by
      rw [bathEnergy, mul_comm]
    _ = Real.exp (-inverseTemperature) ^ bathLevel b := Real.exp_nat_mul _ _
    _ = (energyWeight b : ℝ) := by
      simp only [hbase, energyWeight, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

private theorem gibbsWeight_eq_rat (b : Fin 20) :
    gibbsWeight inverseTemperature bathEnergy b = (rationalGibbsWeight b : ℝ) := by
  simp only [gibbsWeight, exp_energy_eq, rationalGibbsWeight, partitionWeight,
    Rat.cast_div, Rat.cast_sum]

/-- The joint unitary on the system-first product basis. -/
def jointUnitary : Matrix (Fin 3 × Fin 20) (Fin 3 × Fin 20) ℂ :=
  jointPermutation.permMatrix ℂ

private theorem jointUnitary_mem_unitaryGroup : jointUnitary ∈ Matrix.unitaryGroup (Fin 3 × Fin 20) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change jointPermutation.permMatrix ℂ * (jointPermutation.permMatrix ℂ)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

private theorem jointPermutation_preserves_energy (x : Joint) :
    systemEnergy (jointPermutation x).1 + bathEnergy (jointPermutation x).2 =
      systemEnergy x.1 + bathEnergy x.2 := by
  simpa only [totalLevel, Nat.cast_add, systemEnergy, bathEnergy] using
    congrArg (fun n : ℕ => (n : ℝ)) (jointPermutation_preserves_totalLevel x)

private theorem jointUnitary_energyConserving : IsEnergyConserving systemEnergy bathEnergy jointUnitary := by
  unfold IsEnergyConserving
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : j = jointPermutation i
  · subst j
    rw [jointPermutation_preserves_energy, mul_comm]
  · have hzero : jointUnitary i j = 0 := by
      change jointPermutation.toPEquiv.toMatrix i j = (0 : ℂ)
      simp only [PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, h, ite_false]
    simp only [hzero, zero_mul, mul_zero]

/-- The finite thermal operation on arbitrary qutrit matrices. -/
def channel (Q : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceRight (jointUnitary * (Q ⊗ₖ bathState) * jointUnitaryᴴ)

private theorem jointUnitary_conj_diagonal (d : Joint → ℂ) :
    jointUnitary * diagonal d * jointUnitaryᴴ = diagonal (fun x => d (jointPermutation x)) := by
  unfold jointUnitary
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  apply Matrix.ext
  intro i j
  simp [Matrix.submatrix_apply, Matrix.diagonal, Equiv.Perm.inv_def]

private theorem channel_ground_entry : channel inputState 0 0 = (124 / 141 : ℂ) := by
  unfold channel inputState bathState diagonalReal
  rw [Matrix.diagonal_kronecker_diagonal, jointUnitary_conj_diagonal]
  simp only [partialTraceRight, Matrix.diagonal_apply_eq, gibbsWeight_eq_rat,
    Complex.ofReal_ratCast, ← Rat.cast_mul]
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using
    congrArg (fun q : ℚ => (q : ℂ)) rational_ground_entry

end

end D5.S3.QuantumChannels.ThermalDegeneracyWitness

noncomputable section

open Matrix
open scoped BigOperators Kronecker
open GibbsBathBandwidth (diagonalReal gibbsWeight)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)

namespace D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation

open ThermalDegeneracyShellBound (bathEnergies bathFiber boltzmann partition levels)

local notation "bathMultiplicity" => ThermalDegeneracyShellBound.multiplicity

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- A finite positive-temperature thermal operation in the bath energy basis. -/
def operation {d m : ℕ} (β : ℝ) (e : Fin m → ℝ)
    (U : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) (Q : Mat d) : Mat d :=
  partialTraceRight (U * (Q ⊗ₖ diagonalReal (gibbsWeight β e)) * Uᴴ)

/-- Eigenspace multiplicity never exceeds the given cap. -/
def HasCap {m : ℕ} (e : Fin m → ℝ) (M : ℕ) : Prop :=
  ∀ t : ℝ, bathMultiplicity e t ≤ M

/-- The system-dimension degeneracy conjecture in §V of arXiv:2207.11189v4. -/
def claim : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (β : ℝ), 0 < β → ∀ (E : Fin d → ℝ)
    (m : ℕ), 0 < m → ∀ (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin d × Fin m) ℂ),
    IsEnergyConserving E e U →
    ∃ (n : ℕ) (e' : Fin n → ℝ) (V : Matrix.unitaryGroup (Fin d × Fin n) ℂ),
      0 < n ∧ HasCap e' d ∧ IsEnergyConserving E e' V ∧
        operation (d := d) β e' V = operation (d := d) β e U

private theorem multiplicity_zero {m : ℕ} (e : Fin m → ℝ) {t : ℝ}
    (ht : t ∉ bathEnergies e) : bathMultiplicity e t = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hau, hat⟩ := Finset.mem_filter.mp ha
  exact ht (Finset.mem_image.mpr ⟨a, hau, hat⟩)

private def capacityMass {m : ℕ} (e : Fin m → ℝ) : ℝ :=
  ∑ t ∈ bathEnergies e, boltzmann t *
    min (bathMultiplicity e t : ℝ) ((bathMultiplicity e (t - 1) : ℝ) + (bathMultiplicity e (t - 2) : ℝ))

private theorem capacityMass_le {m : ℕ} (e : Fin m → ℝ) (hc : HasCap e 3) :
    (4 / 3 : ℝ) * capacityMass e ≤ (28 / 33 : ℝ) * partition e := by
  let d := ThermalDegeneracyCertificate.deficit (bathMultiplicity e)
  have hd := ThermalDegeneracyCertificate.weighted_sum_le_eleven_fourths_deficit
    (bathEnergies e) (bathMultiplicity e) (fun _ ht => multiplicity_zero e ht) hc
  change (∑ t ∈ bathEnergies e, boltzmann t * (bathMultiplicity e t : ℝ)) ≤
    (11 / 4 : ℝ) * ∑ t ∈ bathEnergies e, boltzmann t * (d t : ℝ) at hd
  rw [← ThermalDegeneracyShellBound.partition_eq_sum_multiplicity] at hd
  have hs : capacityMass e + (∑ t ∈ bathEnergies e, boltzmann t * (d t : ℝ)) =
      partition e := by
    rw [capacityMass, ← Finset.sum_add_distrib,
      ThermalDegeneracyShellBound.partition_eq_sum_multiplicity]
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_add]
    congr 1
    change min (bathMultiplicity e t : ℝ) ((bathMultiplicity e (t - 1) : ℝ) +
      (bathMultiplicity e (t - 2) : ℝ)) + (d t : ℝ) = (bathMultiplicity e t : ℝ)
    have h : min (bathMultiplicity e t) (bathMultiplicity e (t - 1) + bathMultiplicity e (t - 2)) + d t =
        bathMultiplicity e t := by
      change _ + (bathMultiplicity e t - (bathMultiplicity e (t - 1) + bathMultiplicity e (t - 2))) = _
      exact (add_comm _ _).trans tsub_add_min
    exact_mod_cast h
  linarith only [hd, hs]

set_option maxHeartbeats 1000000 in
private theorem ground_le_of_cap {m : ℕ} (hm : 0 < m) (e : Fin m → ℝ)
    (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ)
    (hu : IsEnergyConserving levels e U) (hc : HasCap e 3) :
    (operation (Real.log 2) e U ThermalDegeneracyShellBound.inputState 0 0).re ≤ 28 / 33 := by
  calc
    _ ≤ ((4 / 3 : ℝ) / partition e) * capacityMass e := by
      simpa only [operation, ThermalDegeneracyShellBound.thermalOutput,
        ThermalDegeneracyShellBound.bathState, capacityMass] using
        ThermalDegeneracyShellBound.ground_population_le_shell_sum hm e U hu
    _ ≤ _ := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ (ThermalDegeneracyShellBound.partition_pos hm e)).2 (capacityMass_le e hc)

private theorem witness_input_eq :
    ThermalDegeneracyWitness.inputState = ThermalDegeneracyShellBound.inputState := by
  unfold ThermalDegeneracyWitness.inputState ThermalDegeneracyShellBound.inputState
  congr 1
  funext i
  fin_cases i <;> norm_num [ThermalDegeneracyWitness.inputPopulation,
    ThermalDegeneracyShellBound.populations]

/-- Cap-three operations on the chosen qutrit at inverse temperature log 2. -/
def cappedOperations : Set (Mat 3 → Mat 3) :=
  {F | ∃ (m : ℕ) (e : Fin m → ℝ) (U : Matrix.unitaryGroup (Fin 3 × Fin m) ℂ),
    0 < m ∧ HasCap e 3 ∧ IsEnergyConserving levels e U ∧ F = operation (Real.log 2) e U}

private theorem closure_ground_le {F : Mat 3 → Mat 3} (hF : F ∈ closure cappedOperations) :
    (F ThermalDegeneracyShellBound.inputState 0 0).re ≤ 28 / 33 := by
  let observe (G : Mat 3 → Mat 3) :=
    (G ThermalDegeneracyShellBound.inputState 0 0).re
  have hc : Continuous observe :=
    Complex.continuous_re.comp ((continuous_apply 0).comp
      ((continuous_apply 0).comp (continuous_apply ThermalDegeneracyShellBound.inputState)))
  have hset : IsClosed {G : Mat 3 → Mat 3 | observe G ≤ (28 / 33 : ℝ)} :=
    isClosed_le hc continuous_const
  apply (closure_minimal (s := cappedOperations) (t := {G | observe G ≤ (28 / 33 : ℝ)})
    ?_ hset) hF
  rintro G ⟨m, e, U, hm, hcap, hU, rfl⟩
  exact ground_le_of_cap hm e U hU hcap

private theorem witness_outside_closure :
    ThermalDegeneracyWitness.channel ∉ closure cappedOperations := by
  intro h
  have hcap := closure_ground_le h
  rw [← witness_input_eq, ThermalDegeneracyWitness.channel_ground_entry] at hcap
  norm_num at hcap

/-- The actual finite thermal channel is separated from all cap-three channels. -/
theorem result : ¬ claim := by
  intro h
  let U : Matrix.unitaryGroup (Fin 3 × Fin 20) ℂ :=
    ⟨ThermalDegeneracyWitness.jointUnitary, ThermalDegeneracyWitness.jointUnitary_mem_unitaryGroup⟩
  obtain ⟨m, e, V, hm, hcap, hV, hsame⟩ := h 3 (by decide)
    (Real.log 2) ThermalDegeneracyWitness.inverseTemperature_pos levels 20 (by decide)
    ThermalDegeneracyWitness.bathEnergy U ThermalDegeneracyWitness.jointUnitary_energyConserving
  apply witness_outside_closure
  apply subset_closure
  exact ⟨m, e, V, hm, hcap, hV, hsame.symm⟩

end D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation
