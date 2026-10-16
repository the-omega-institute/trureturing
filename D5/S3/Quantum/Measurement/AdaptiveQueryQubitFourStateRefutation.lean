/- GID: D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.claim; result=D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result; claim=D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.claim
   digest: Four qubit states admit adaptive query value 99/100 above pre-query bound 483/500. -/

import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

set_option linter.style.longLine false

namespace D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation

open Matrix
open scoped BigOperators ComplexOrder

abbrev Q2 := D5.S3.Quantum.FiniteDimensional.QubitMatrix

/-- Nonnegative normalized priors and qubit density matrices. -/
def IsEnsemble {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2) : Prop :=
  (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1 ∧
    ∀ x, (ρ x).PosSemidef ∧ trace (ρ x) = 1

/-- A finite positive operator-valued measure. -/
def IsPOVM {ι : Type} [Fintype ι] (M : ι → Q2) : Prop :=
  D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM M

private def cell {n : ℕ} (X : Finset (Fin n)) (ℓ : Fin 2) : Finset (Fin n) :=
  if ℓ = 0 then X else Xᶜ

/-- Each nonempty cell has its own normalized POVM; an empty cell contributes nothing. -/
def IsPreStrategy {n : ℕ} (X : Finset (Fin n)) (M : Fin 2 → Fin n → Q2) : Prop :=
  ∀ ℓ, (∀ x ∈ cell X ℓ, (M ℓ x).PosSemidef) ∧
    ((cell X ℓ).Nonempty → ∑ x ∈ cell X ℓ, M ℓ x = 1)

/-- The success value of a pre-measurement query, including its prior weights. -/
noncomputable def preValue {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2)
    (X : Finset (Fin n)) (M : Fin 2 → Fin n → Q2) : ℝ :=
  ∑ ℓ, ∑ x ∈ cell X ℓ, q x * (trace (ρ x * M ℓ x)).re

/-- The supremum over all binary partitions and their cell measurements. -/
noncomputable def Ppre {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2) : ℝ :=
  sSup {v | ∃ X M, IsPreStrategy X M ∧ v = preValue q ρ X M}

/-- The query and the two guesses can depend on the observed POVM outcome. -/
def IsAdaptiveStrategy {n m : ℕ} (M : Fin m → Q2)
    (P : Fin m → Finset (Fin n)) (f : Fin m → Fin 2 → Fin n) : Prop :=
  IsPOVM M ∧ ∀ z ℓ, f z ℓ ∈ cell (P z) ℓ

/-- The success value of an adaptive post-measurement query. -/
noncomputable def adaptiveValue {n m : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2)
    (M : Fin m → Q2) (f : Fin m → Fin 2 → Fin n) : ℝ :=
  ∑ z, ∑ ℓ, q (f z ℓ) * (trace (ρ (f z ℓ) * M z)).re

/-- The proposed absence of adaptive advantage for every qubit ensemble of size at least four. -/
def claim : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (q : Fin n → ℝ) (ρ : Fin n → Q2), IsEnsemble q ρ →
    ∀ (m : ℕ) (M : Fin m → Q2) (P : Fin m → Finset (Fin n))
      (f : Fin m → Fin 2 → Fin n), IsAdaptiveStrategy M P f →
        adaptiveValue q ρ M f ≤ Ppre q ρ

private noncomputable def q : Fin 4 → ℝ := ![33/100, 33/100, 33/100, 1/100]

private noncomputable def ket : Fin 4 → Fin 2 → ℂ :=
  ![![1, 0], ![1, 2], ![1, -2], ![1, 1]]

private noncomputable def weight : Fin 4 → ℝ := ![1, 1/5, 1/5, 1/2]

private noncomputable def rho (x : Fin 4) : Q2 :=
  weight x • vecMulVec (ket x) (star (ket x))

private theorem ensemble_valid : IsEnsemble q rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [q.eq_1]
    fin_cases x <;> norm_num [q.eq_1]
  · norm_num [q.eq_1, Fin.sum_univ_succ]
  · intro x
    constructor
    · exact (posSemidef_vecMulVec_self_star (ket x)).smul
        (by rw [weight.eq_1]; fin_cases x <;> norm_num)
    · rw [rho, trace_smul, trace_vecMulVec, ket.eq_1]
      fin_cases x <;>
        norm_num [weight.eq_1, ket.eq_1, dotProduct, Fin.sum_univ_two, map_ofNat]

private noncomputable def effectKet : Fin 3 → Fin 2 → ℂ :=
  ![![0, 1], ![2, -1], ![2, 1]]

private noncomputable def effectWeight : Fin 3 → ℝ := ![3/4, 1/8, 1/8]

private noncomputable def effect (z : Fin 3) : Q2 :=
  effectWeight z • vecMulVec (effectKet z) (star (effectKet z))

private def partition : Fin 3 → Finset (Fin 4) := ![{1}, {0}, {0}]

private def guess : Fin 3 → Fin 2 → Fin 4 := ![![1, 2], ![0, 2], ![0, 1]]

private theorem adaptive_valid : IsAdaptiveStrategy effect partition guess := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z
    exact (posSemidef_vecMulVec_self_star (effectKet z)).smul
      (by rw [effectWeight.eq_1]; fin_cases z <;> norm_num)
  · rw [Fin.sum_univ_three, effect.eq_1, effectKet.eq_1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [effect.eq_1, effectWeight.eq_1, effectKet.eq_1, vecMulVec, Fin.sum_univ_succ,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.cons_val_two, map_ofNat]
  · intro z ℓ
    fin_cases z <;> fin_cases ℓ <;> decide

private theorem adaptive_value : adaptiveValue q rho effect guess = 99/100 := by
  rw [adaptiveValue.eq_1, guess.eq_1]
  norm_num [adaptiveValue.eq_1, q.eq_1, rho, weight.eq_1, ket.eq_1, effect.eq_1, effectWeight.eq_1, effectKet.eq_1,
    guess.eq_1, trace, Matrix.mul_apply, vecMulVec, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.smul_apply, Complex.mul_re, Complex.mul_im, Matrix.cons_val_two,
    Matrix.cons_val_three, map_ofNat]

private noncomputable def realMat (a b c : ℝ) : Q2 :=
  (!![a, b; b, c]).map (↑)

private def parts : Fin 8 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 1, 2}, {0, 3}, {0, 1, 3}, {0, 2, 3}, Finset.univ]

private noncomputable def dual : Fin 8 → Fin 2 → Q2 :=
  ![![realMat (33/100) 0 0, realMat (99/500) 0 (99/250)],
    ![realMat (173/500) (33/500) (7/25), realMat (147/2000) (-16/125) (533/2000)],
    ![realMat (173/500) (-33/500) (7/25), realMat (27/400) (33/250) (529/2000)],
    ![realMat (33/100) 0 (33/100), realMat (1/200) (1/200) (1/200)],
    ![realMat (661/2000) 0 (11/2000), realMat (99/500) 0 (99/250)],
    ![realMat (173/500) (33/500) (7/25), realMat (33/500) (-33/250) (33/125)],
    ![realMat (173/500) (-33/500) (7/25), realMat (33/500) (33/250) (33/125)],
    ![realMat (33/100) 0 (33/100), 0]]

private theorem real_psd (A : Q2)
    (hr : A = realMat (A 0 0).re (A 0 1).re (A 1 1).re)
    (hn : A = 0 ∨ (0 < (A 0 0).re + (A 1 1).re ∧
      0 ≤ (A 0 0).re * (A 1 1).re - (A 0 1).re ^ 2)) : A.PosSemidef := by
  rcases hn with hz | hn
  · rw [hz]
    exact PosSemidef.zero
  · rw [hr, realMat.eq_1]
    exact FreeSpectrahedronFeasibilityWitness.posSemidef_of_trace_det
      _ _ _ hn.1 hn.2

set_option maxHeartbeats 2000000 in
-- The finite case proof checks all 32 rational slack matrices.
private theorem certificate_slack (k : Fin 8) (ℓ : Fin 2) (x : Fin 4)
    (hx : x ∈ cell (parts k) ℓ) :
    (dual k ℓ - (q x : ℂ) • rho x).PosSemidef := by
  rw [cell.eq_1, parts.eq_1] at hx
  rw [dual.eq_1]
  fin_cases k <;> fin_cases ℓ <;> fin_cases x <;>
    norm_num [cell.eq_1, parts.eq_1, Fin.ext_iff] at hx
  all_goals apply real_psd
  all_goals first
    | solve
      | ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [dual.eq_1, realMat.eq_1, q.eq_1, rho, weight.eq_1, ket.eq_1, vecMulVec,
            Matrix.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three, map_ofNat]
    | solve
      | right
        norm_num [dual.eq_1, realMat.eq_1, q.eq_1, rho, weight.eq_1, ket.eq_1, vecMulVec,
          Matrix.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three, map_ofNat]
    | left
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [dual.eq_1, realMat.eq_1, q.eq_1, rho, weight.eq_1, ket.eq_1, vecMulVec,
          Matrix.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three, map_ofNat]

private theorem certificate_traces (k : Fin 8) :
    (∀ ℓ, 0 ≤ (trace (dual k ℓ)).re) ∧
    (trace (dual k 0)).re + (trace (dual k 1)).re ≤ 483/500 := by
  fin_cases k <;> constructor
  all_goals first
    | solve
      | intro ℓ
        fin_cases ℓ <;> norm_num [dual.eq_1, realMat.eq_1, trace, Fin.sum_univ_two]
    | norm_num [dual.eq_1, realMat.eq_1, trace, Fin.sum_univ_two]

private theorem cell_bound {n : ℕ} (q : Fin n → ℝ) (ρ : Fin n → Q2)
    (C : Finset (Fin n)) (M : Fin n → Q2) (Y : Q2)
    (hp : ∀ x ∈ C, (M x).PosSemidef)
    (hs : C.Nonempty → ∑ x ∈ C, M x = 1)
    (hd : ∀ x ∈ C, (Y - (q x : ℂ) • ρ x).PosSemidef)
    (ht : 0 ≤ (trace Y).re) :
    ∑ x ∈ C, q x * (trace (ρ x * M x)).re ≤ (trace Y).re := by
  by_cases hc : C.Nonempty
  · have hpoint (x : Fin n) (hx : x ∈ C) :
        q x * (trace (ρ x * M x)).re ≤ (trace (Y * M x)).re := by
      have hpos := (Complex.nonneg_iff.mp ((hd x hx).trace_mul_nonneg (hp x hx))).1
      simp only [sub_mul, smul_mul, trace_sub, trace_smul, Complex.sub_re,
        smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at hpos
      linarith
    calc
      ∑ x ∈ C, q x * (trace (ρ x * M x)).re ≤
          ∑ x ∈ C, (trace (Y * M x)).re := Finset.sum_le_sum hpoint
      _ = (trace Y).re := by
        rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum, hs hc, mul_one]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hc]
    simpa using ht

private theorem pre_bound_parts (k : Fin 8) (M : Fin 2 → Fin 4 → Q2)
    (hM : IsPreStrategy (parts k) M) : preValue q rho (parts k) M ≤ 483/500 := by
  rw [preValue.eq_1, Fin.sum_univ_two]
  have hzero := cell_bound q rho (cell (parts k) 0) (M 0) (dual k 0)
    (hM 0).1 (hM 0).2 (certificate_slack k 0) ((certificate_traces k).1 0)
  have hone := cell_bound q rho (cell (parts k) 1) (M 1) (dual k 1)
    (hM 1).1 (hM 1).2 (certificate_slack k 1) ((certificate_traces k).1 1)
  exact (add_le_add hzero hone).trans (certificate_traces k).2

private theorem partitions_complete :
    ∀ X : Finset (Fin 4), ∃ k : Fin 8, X = parts k ∨ Xᶜ = parts k := by
  decide

private theorem pre_bound (X : Finset (Fin 4)) (M : Fin 2 → Fin 4 → Q2)
    (hM : IsPreStrategy X M) : preValue q rho X M ≤ 483/500 := by
  obtain ⟨k, hk | hk⟩ := partitions_complete X
  · subst X
    exact pre_bound_parts k M hM
  · let N : Fin 2 → Fin 4 → Q2 := ![M 1, M 0]
    have hN : IsPreStrategy (parts k) N := by
      intro ℓ
      fin_cases ℓ
      · simpa [← hk, cell.eq_1, N] using hM 1
      · simpa [← hk, cell.eq_1, N] using hM 0
    have hv : preValue q rho X M = preValue q rho (parts k) N := by
      simp [preValue.eq_1, Fin.sum_univ_two, ← hk, cell.eq_1, N, add_comm]
    rw [hv]
    exact pre_bound_parts k N hN

private theorem pre_nonempty :
    {v | ∃ X M, IsPreStrategy X M ∧ v = preValue q rho X M}.Nonempty := by
  let M : Fin 2 → Fin 4 → Q2 := fun _ x => if x = 0 then 1 else 0
  refine ⟨preValue q rho Finset.univ M, Finset.univ, M, ?_, rfl⟩
  intro ℓ
  fin_cases ℓ
  · constructor
    · intro x _
      dsimp [M]
      split_ifs
      · exact PosSemidef.one
      · exact PosSemidef.zero
    · intro _
      norm_num [cell.eq_1, M, Fin.sum_univ_succ]
  · simp [cell.eq_1]

private theorem pre_upper : Ppre q rho ≤ 483/500 := by
  apply csSup_le pre_nonempty
  rintro v ⟨X, M, hM, rfl⟩
  exact pre_bound X M hM

theorem result : ¬ claim := by
  intro hc
  have h := hc 4 (by decide) q rho ensemble_valid 3 effect partition guess adaptive_valid
  rw [adaptive_value] at h
  linarith [pre_upper]

end D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation
