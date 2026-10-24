/- GID: D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/TemporalBellContractionIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Temporal Bell endpoint contractions equal one-particle propagator entries for every N. -/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-! Endpoint vacuum contractions for the open XX chain in the Heisenberg picture. -/

open Matrix
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier (numberParity majorana_clifford_and_parity)
open PredictiveThermodynamic.Physical (Assignment)

noncomputable section
namespace D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity

def hopping (N : ℕ) (J μ : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then -(μ : ℂ)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -(J : ℂ) else 0

def hamiltonian (N : ℕ) (J μ : ℝ) : FullOperator N :=
  ∑ i : Fin N, ∑ j : Fin N, hopping N J μ i j • ((fullC i)ᴴ * fullC j)

def propagator (N : ℕ) (J μ t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • hopping N J μ)

def evolve {N : ℕ} (J μ t : ℝ) (A : FullOperator N) : FullOperator N :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • hamiltonian N J μ) * A *
    NormedSpace.exp (-(((t : ℂ) * Complex.I) • hamiltonian N J μ))

def sigmaXLast (N : ℕ) (hN : 0 < N) : FullOperator N :=
  (((List.finRange N).filter (fun j => j.val < N - 1)).map
    (fun j => (1 : FullOperator N) - (2 : ℂ) • ((fullC j)ᴴ * fullC j))).prod *
      ((fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩)ᴴ +
        fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩)

def vacuumIndex (N : ℕ) : Assignment N := fun _ => false

def claim : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N) (J μ t : ℝ),
    let first : Fin N := ⟨0, by omega⟩
    let last : Fin N := ⟨N - 1, by omega⟩
    let X := evolve J μ t (sigmaXLast N (by omega))
    ((fullC last * fullC first * X * (fullC first)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC last * fullC first * X * (fullC last)ᴴ)
        (vacuumIndex N) (vacuumIndex N)).re =
      (propagator N J μ t last last - propagator N J μ t first last).re

private lemma mixed_CAR {N : ℕ} (i j : Fin N) :
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i =
      if i = j then (1 : FullOperator N) else 0 := by
  by_cases h : i = j
  · subst j
    simpa using fullC_CAR i
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with h | h
    · exact fullC_mixed_anticomm_of_lt i j h
    · have ht := congrArg Matrix.conjTranspose (fullC_mixed_anticomm_of_lt j i h)
      simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, add_comm] using ht

private lemma creation_anticomm {N : ℕ} (i j : Fin N) :
    (fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ = 0 := by
  let g := D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana (N := N)
  have hc := (majorana_clifford_and_parity N).2.2.2.1
  have h00 := hc (i, false) (j, false)
  have h11 := hc (i, true) (j, true)
  have h01 := hc (i, false) (j, true)
  have h10 := hc (i, true) (j, false)
  have hz : (4 : ℂ) • ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) = 0 := by
    calc
      _ = (g i false * g j false + g j false * g i false) -
          (g i true * g j true + g j true * g i true) +
          Complex.I • ((g i false * g j true + g j true * g i false) +
            (g i true * g j false + g j false * g i true)) := by
        dsimp [g, D5.S3.Quantum.Fermionic.FockMajoranaCarrier.majorana]
        simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul,
          smul_add, smul_sub, smul_smul, Complex.I_mul_I]
        ext s t
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by
        change (_ - _ + Complex.I • (_ + _)) = 0
        rw [h00, h11, h01, h10]
        simp
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private lemma quadratic_commutator {N : ℕ} (J μ : ℝ) (j : Fin N) :
    hamiltonian N J μ * (fullC j)ᴴ - (fullC j)ᴴ * hamiltonian N J μ =
      ∑ i : Fin N, hopping N J μ i j • (fullC i)ᴴ := by
  have hterm (i k : Fin N) :
      ((fullC i)ᴴ * fullC k) * (fullC j)ᴴ -
          (fullC j)ᴴ * ((fullC i)ᴴ * fullC k) =
        if k = j then (fullC i)ᴴ else 0 := by
    calc
      _ = (fullC i)ᴴ * (fullC k * (fullC j)ᴴ + (fullC j)ᴴ * fullC k) -
          ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) * fullC k := by
        noncomm_ring
      _ = _ := by rw [mixed_CAR, creation_anticomm]; split_ifs <;> simp
  unfold hamiltonian
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hterm]
  simp

private lemma creation_evolution {N : ℕ} (J μ t : ℝ) (j : Fin N) :
    evolve J μ t (fullC j)ᴴ =
      ∑ i : Fin N, propagator N J μ t i j • (fullC i)ᴴ := by
  let H := hamiltonian N J μ
  let h := hopping N J μ
  let L : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] FullOperator N :=
    { toFun := fun M => ∑ i : Fin N, M i j • (fullC i)ᴴ
      map_add' := by intro M Q; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c M; simp [Finset.smul_sum, smul_smul] }
  have hL (M : Matrix (Fin N) (Fin N) ℂ) : H * L M - L M * H = L (h * M) := by
    change H * (∑ i, M i j • (fullC i)ᴴ) -
      (∑ i, M i j • (fullC i)ᴴ) * H = ∑ i, (h * M) i j • (fullC i)ᴴ
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
    simp only [H, quadratic_commutator, Finset.smul_sum, smul_smul,
      Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm]
  let F (z : ℂ) := NormedSpace.exp (z • (-H)) *
    L (NormedSpace.exp (z • h)) * NormedSpace.exp (z • H)
  have hd (z : ℂ) : HasDerivAt F 0 z := by
    have hC := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt z
      (hasDerivAt_exp_smul_const' h z)
    have hraw := ((hasDerivAt_exp_smul_const (-H) z).mul hC).mul
      (hasDerivAt_exp_smul_const' H z)
    apply hraw.congr_deriv
    change ((NormedSpace.exp (z • (-H)) * (-H)) * L (NormedSpace.exp (z • h)) +
      NormedSpace.exp (z • (-H)) * L (h * NormedSpace.exp (z • h))) *
        NormedSpace.exp (z • H) +
      (NormedSpace.exp (z • (-H)) * L (NormedSpace.exp (z • h))) *
        (H * NormedSpace.exp (z • H)) = 0
    rw [← hL]
    noncomm_ring
  let z := (t : ℂ) * Complex.I
  have hc := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  have hzero : L (1 : Matrix (Fin N) (Fin N) ℂ) = (fullC j)ᴴ := by
    change (∑ i, (1 : Matrix (Fin N) (Fin N) ℂ) i j • (fullC i)ᴴ) = _
    simp [Matrix.one_apply]
  have hc' : NormedSpace.exp (z • (-H)) * L (NormedSpace.exp (z • h)) *
      NormedSpace.exp (z • H) = (fullC j)ᴴ := by
    simpa only [F, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, hzero] using hc
  have hinv : NormedSpace.exp (z • H) * NormedSpace.exp (z • (-H)) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (z • H)).neg_right]
    simp
  change NormedSpace.exp (z • H) * (fullC j)ᴴ * NormedSpace.exp (-(z • H)) =
    L (NormedSpace.exp (z • h))
  rw [← hc']
  calc
    _ = (NormedSpace.exp (z • H) * NormedSpace.exp (z • (-H))) *
        L (NormedSpace.exp (z • h)) *
        (NormedSpace.exp (z • H) * NormedSpace.exp (z • (-H))) := by
      simp only [smul_neg, mul_assoc]
    _ = _ := by rw [hinv]; simp only [one_mul, mul_one]

private lemma hamiltonian_hermitian (N : ℕ) (J μ : ℝ) :
    (hamiltonian N J μ).IsHermitian := by
  have hh (i j : Fin N) : star (hopping N J μ i j) = hopping N J μ j i := by
    by_cases hij : i = j
    · subst j
      simp [hopping]
    · simp only [hopping, if_neg hij, if_neg (Ne.symm hij)]
      split_ifs <;> simp_all
  change (hamiltonian N J μ)ᴴ = _
  unfold hamiltonian
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh]
  rw [Finset.sum_comm]

private lemma evolve_adjoint {N : ℕ} (J μ t : ℝ) (A : FullOperator N) :
    evolve J μ t Aᴴ = (evolve J μ t A)ᴴ := by
  have hK : ((((t : ℂ) * Complex.I) • hamiltonian N J μ) : FullOperator N)ᴴ =
      -(((t : ℂ) * Complex.I) • hamiltonian N J μ) := by
    rw [Matrix.conjTranspose_smul, (hamiltonian_hermitian N J μ).eq]
    simp [Complex.star_def]
  unfold evolve
  simp only [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose,
    Matrix.conjTranspose_neg, hK, neg_neg, mul_assoc]

private lemma annihilation_evolution {N : ℕ} (J μ t : ℝ) (j : Fin N) :
    evolve J μ t (fullC j) =
      ∑ i : Fin N, star (propagator N J μ t i j) • fullC i := by
  have hcreate := congrArg Matrix.conjTranspose (creation_evolution J μ t j)
  rw [← evolve_adjoint] at hcreate
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul] using hcreate

private lemma parity_odd {N : ℕ} (j : Fin N) :
    numberParity N * fullC j + fullC j * numberParity N = 0 ∧
      numberParity N * (fullC j)ᴴ + (fullC j)ᴴ * numberParity N = 0 := by
  let P := numberParity N
  have hc := majorana_clifford_and_parity N
  have hsum := hc.2.2.2.2 (j, false)
  change P * (fullC j + (fullC j)ᴴ) + (fullC j + (fullC j)ᴴ) * P = 0 at hsum
  have hdiff : P * (fullC j - (fullC j)ᴴ) + (fullC j - (fullC j)ᴴ) * P = 0 := by
    have ht := hc.2.2.2.2 (j, true)
    change P * (Complex.I • (fullC j - (fullC j)ᴴ)) +
      (Complex.I • (fullC j - (fullC j)ᴴ)) * P = 0 at ht
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at ht
    exact (smul_eq_zero.mp ht).resolve_left Complex.I_ne_zero
  have hz : (2 : ℂ) • (P * fullC j + fullC j * P) = 0 := by
    calc
      _ = (P * (fullC j + (fullC j)ᴴ) + (fullC j + (fullC j)ᴴ) * P) +
          (P * (fullC j - (fullC j)ᴴ) + (fullC j - (fullC j)ᴴ) * P) := by
        simp only [two_smul]
        noncomm_ring
      _ = 0 := by rw [hsum, hdiff]; simp
  have ha := (smul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  refine ⟨ha, ?_⟩
  have ht := congrArg Matrix.conjTranspose ha
  simpa only [P, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hc.1.eq,
    Matrix.conjTranspose_zero, add_comm] using ht

private lemma sigmaXLast_parity (N : ℕ) (hN : 0 < N) :
    sigmaXLast N hN = numberParity N *
      (fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩ -
        (fullC ⟨N - 1, Nat.sub_lt hN (by decide)⟩)ᴴ) := by
  sorry

private lemma parity_stationary (N : ℕ) (J μ t : ℝ) :
    evolve J μ t (numberParity N) = numberParity N := by
  let P := numberParity N
  let H := hamiltonian N J μ
  let z := (t : ℂ) * Complex.I
  have hterm (i j : Fin N) : P * ((fullC i)ᴴ * fullC j) = ((fullC i)ᴴ * fullC j) * P := by
    have hi := eq_neg_of_add_eq_zero_left (parity_odd i).2
    have hj := eq_neg_of_add_eq_zero_left (parity_odd j).1
    calc
      _ = (P * (fullC i)ᴴ) * fullC j := by simp only [mul_assoc]
      _ = -((fullC i)ᴴ * (P * fullC j)) := by rw [hi]; noncomm_ring
      _ = _ := by rw [hj]; noncomm_ring
  have hPH : Commute P H := by
    change P * (∑ i : Fin N, ∑ j : Fin N,
        hopping N J μ i j • ((fullC i)ᴴ * fullC j)) =
      (∑ i : Fin N, ∑ j : Fin N, hopping N J μ i j • ((fullC i)ᴴ * fullC j)) * P
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hterm]
  have hc := (hPH.smul_right z).exp_right
  unfold evolve
  change NormedSpace.exp (z • H) * P * NormedSpace.exp (-(z • H)) = P
  rw [← hc.eq, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (z • H)).neg_right]
  simp

private lemma evolve_mul {N : ℕ} (J μ t : ℝ) (A B : FullOperator N) :
    evolve J μ t (A * B) = evolve J μ t A * evolve J μ t B := by
  let K := ((t : ℂ) * Complex.I) • hamiltonian N J μ
  have hinv : NormedSpace.exp (-K) * NormedSpace.exp K = 1 := by
    rw [← Matrix.exp_add_of_commute (-K) K (Commute.refl K).neg_left]
    simp
  unfold evolve
  change NormedSpace.exp K * (A * B) * NormedSpace.exp (-K) = _
  calc
    _ = NormedSpace.exp K * A * (NormedSpace.exp (-K) * NormedSpace.exp K) * B *
        NormedSpace.exp (-K) := by rw [hinv]; simp only [mul_one, mul_assoc]
    _ = _ := by simp only [K, mul_assoc]

private lemma evolve_sub {N : ℕ} (J μ t : ℝ) (A B : FullOperator N) :
    evolve J μ t (A - B) = evolve J μ t A - evolve J μ t B := by
  unfold evolve
  noncomm_ring

private lemma evolved_endpoint (N : ℕ) (hN : 0 < N) (J μ t : ℝ) :
    evolve J μ t (sigmaXLast N hN) = numberParity N *
      ((∑ i : Fin N, star (propagator N J μ t i ⟨N - 1, by omega⟩) • fullC i) -
        ∑ i : Fin N, propagator N J μ t i ⟨N - 1, by omega⟩ • (fullC i)ᴴ) := by
  rw [sigmaXLast_parity, evolve_mul, parity_stationary, evolve_sub,
    annihilation_evolution, creation_evolution]

private lemma vacuum_annihilator {N : ℕ} (j : Fin N) (s : Assignment N) :
    fullC j s (vacuumIndex N) = 0 := by
  rw [fullC_entry]
  simp [vacuumIndex]

private lemma vacuum_right_annihilator {N : ℕ} (j : Fin N) (M : FullOperator N)
    (s : Assignment N) : (M * fullC j) s (vacuumIndex N) = 0 := by
  simp only [Matrix.mul_apply, vacuum_annihilator, mul_zero, Finset.sum_const_zero]

private lemma vacuum_left_creation {N : ℕ} (j : Fin N) (M : FullOperator N)
    (s : Assignment N) : ((fullC j)ᴴ * M) (vacuumIndex N) s = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, vacuum_annihilator,
    star_zero, zero_mul, Finset.sum_const_zero]

private lemma vacuum_pair {N : ℕ} (i j : Fin N) :
    (fullC i * (fullC j)ᴴ) (vacuumIndex N) (vacuumIndex N) =
      if i = j then (1 : ℂ) else 0 := by
  have hc := congrArg (fun M : FullOperator N => M (vacuumIndex N) (vacuumIndex N))
    (mixed_CAR i j)
  simp only [Matrix.add_apply, vacuum_left_creation, add_zero] at hc
  by_cases hij : i = j <;> simpa [hij, Matrix.one_apply] using hc

private lemma vacuum_four {N : ℕ} (a b k r : Fin N) :
    (fullC b * fullC a * (fullC k)ᴴ * (fullC r)ᴴ) (vacuumIndex N) (vacuumIndex N) =
      (if a = k then (if b = r then (1 : ℂ) else 0) else 0) -
        (if b = k then (if a = r then (1 : ℂ) else 0) else 0) := by
  have he : fullC b * fullC a * (fullC k)ᴴ * (fullC r)ᴴ =
      fullC b * (fullC a * (fullC k)ᴴ + (fullC k)ᴴ * fullC a) * (fullC r)ᴴ -
        (fullC b * (fullC k)ᴴ + (fullC k)ᴴ * fullC b) * fullC a * (fullC r)ᴴ +
        (fullC k)ᴴ * fullC b * fullC a * (fullC r)ᴴ := by noncomm_ring
  rw [he, mixed_CAR, mixed_CAR]
  by_cases hak : a = k <;> by_cases hbk : b = k <;>
    simp [hak, hbk, mul_assoc, vacuum_left_creation, vacuum_pair]

private lemma vacuum_annihilation_contraction {N : ℕ} (a b k r : Fin N) :
    (fullC b * fullC a * fullC k * (fullC r)ᴴ) (vacuumIndex N) (vacuumIndex N) = 0 := by
  have he : fullC b * fullC a * fullC k * (fullC r)ᴴ =
      fullC b * fullC a * (fullC k * (fullC r)ᴴ + (fullC r)ᴴ * fullC k) -
        (fullC b * fullC a * (fullC r)ᴴ) * fullC k := by noncomm_ring
  rw [he, mixed_CAR]
  by_cases hkr : k = r <;>
    simp [hkr, Matrix.sub_apply, vacuum_right_annihilator]

private lemma vacuum_contractions {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (u v : Fin N → ℂ) :
    (fullC b * fullC a *
        (numberParity N * ((∑ i : Fin N, u i • fullC i) -
          ∑ i : Fin N, v i • (fullC i)ᴴ)) * (fullC a)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC b * fullC a *
        (numberParity N * ((∑ i : Fin N, u i • fullC i) -
          ∑ i : Fin N, v i • (fullC i)ᴴ)) * (fullC b)ᴴ)
        (vacuumIndex N) (vacuumIndex N) = v b - v a := by
  let P := numberParity N
  have ha := eq_neg_of_add_eq_zero_right (parity_odd a).1
  have hb := eq_neg_of_add_eq_zero_right (parity_odd b).1
  have hp : fullC b * fullC a * P = P * (fullC b * fullC a) := by
    calc
      _ = fullC b * (fullC a * P) := by simp only [mul_assoc]
      _ = fullC b * (-(P * fullC a)) := by rw [ha]
      _ = -(fullC b * P) * fullC a := by noncomm_ring
      _ = _ := by rw [hb]; noncomm_ring
  have hclean (M R : FullOperator N) :
      (fullC b * fullC a * (P * M) * R) (vacuumIndex N) (vacuumIndex N) =
        (fullC b * fullC a * M * R) (vacuumIndex N) (vacuumIndex N) := by
    have he : fullC b * fullC a * (P * M) * R = P * (fullC b * fullC a * M * R) := by
      calc
        _ = (fullC b * fullC a * P) * M * R := by noncomm_ring
        _ = _ := by rw [hp]; noncomm_ring
    rw [he]
    dsimp only [P]
    rw [D5.S3.Quantum.Fermionic.FockMajoranaCarrier.numberParity_eq_diagonal,
      Matrix.diagonal_mul]
    simp [D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.occupationCount, vacuumIndex]
  rw [hclean, hclean]
  simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    vacuum_annihilation_contraction, vacuum_four]
  simp [hab, Ne.symm hab, eq_comm, sub_eq_add_neg]

private lemma complex_identity (N : ℕ) (hN : 2 ≤ N) (J μ t : ℝ) :
    let first : Fin N := ⟨0, by omega⟩
    let last : Fin N := ⟨N - 1, by omega⟩
    let X := evolve J μ t (sigmaXLast N (by omega))
    (fullC last * fullC first * X * (fullC first)ᴴ)
        (vacuumIndex N) (vacuumIndex N) +
      (fullC last * fullC first * X * (fullC last)ᴴ)
        (vacuumIndex N) (vacuumIndex N) =
      propagator N J μ t last last - propagator N J μ t first last := by
  dsimp only
  rw [evolved_endpoint]
  apply vacuum_contractions
  intro h
  have := congrArg Fin.val h
  dsimp at this
  omega

theorem result : claim := by
  intro N hN J μ t
  exact congrArg Complex.re (complex_identity N hN J μ t)

end D5.S3.Quantum.SpinChains.TemporalBellContractionIdentity
