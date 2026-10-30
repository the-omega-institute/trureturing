/- GID: D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim; result=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result; claim=D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.claim
   digest: A spin-four covariant channel lowers order-seven trace-distance anticoherence. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-!
The mixed-state reading of axiom (T4) in Denis–Lacaille–Martin–Serrano-Ensástiga,
arXiv:2605.29436v1, with the witness specified in preregistration #24441.
Reduced states are expressed in the normalized Dicke basis. Their splitting
isometry implements the ordinary qubit partial trace in these coordinates.
-/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)

/-- The tensor power in the computational basis of `n` qubits. -/
def qubitPower (n : ℕ) (u : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => ∏ k, u (x k) (y k)

/-- The normalized Dicke embedding; the spin index counts qubits in state one. -/
def dickeIsometry (n : ℕ) : Matrix (Fin n → Fin 2) (Fin (n + 1)) ℂ :=
  fun x r => if (∑ k, (x k).val) = r.val then
    (Real.sqrt (n.choose r.val : ℝ) : ℂ)⁻¹ else 0

/-- The spin-`n/2` representation obtained by restricting the qubit tensor power. -/
def spinAction (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (dickeIsometry n)ᴴ * qubitPower n u.val * dickeIsometry n

/-- The Dicke splitting coefficients for the first `t` and last `n-t` qubits. -/
def dickeSplit (n t : ℕ) :
    Matrix (Fin (t + 1) × Fin (n - t + 1)) (Fin (n + 1)) ℂ :=
  fun kl r => if kl.1.val + kl.2.val = r.val then
    ((Real.sqrt ((t.choose kl.1.val : ℝ) * ((n - t).choose kl.2.val : ℝ)) /
      Real.sqrt (n.choose r.val : ℝ) : ℝ) : ℂ) else 0

/-- The qubit partial trace, expressed in the normalized `t`-qubit Dicke basis. -/
def reducedState {n : ℕ} (t : ℕ) (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  partialTraceRight (dickeSplit n t * ρ * (dickeSplit n t)ᴴ)

/-- The maximally mixed state on the symmetric `t`-qubit subspace. -/
def mixedState (t : ℕ) : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ :=
  (1 / ((t : ℂ) + 1)) • 1

/-- The source's maximum trace distance over all states of spin `t/2`. -/
def normalizer (t : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ σ : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ,
    σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - mixedState t)}

/-- The distance-based total anticoherence measure for Schatten exponent one. -/
def anticoherence {n : ℕ} (t : ℕ)
    (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  1 - traceNorm (reducedState t ρ - mixedState t) / normalizer t

/-- Complete positivity, trace preservation, and covariance under every single-qubit SU(2). -/
def IsCovariantChannel {n : ℕ} (φ : MatrixMap (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  φ.IsCompletelyPositive ∧ φ.IsTracePreserving ∧
    ∀ (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      φ (spinAction n u * x * (spinAction n u)ᴴ) =
        spinAction n u * φ x * (spinAction n u)ᴴ

/-- Axiom (T4), including the source's full mixed-state range `1 ≤ t ≤ n`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℕ, 1 ≤ t → t ≤ n →
    ∀ φ : MatrixMap (Fin (n + 1)) (Fin (n + 1)) ℂ, IsCovariantChannel φ →
    ∀ ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → anticoherence t ρ ≤ anticoherence t (φ ρ)

private def witnessState : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r => (![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℂ) / 1764)

private def witnessKraus : Fin 5 → Matrix (Fin 9) (Fin 9) ℂ :=
  ![(1 / (Real.sqrt 1540 : ℂ)) • ((3 : ℂ) • (Jz 8 * Jz 8) - (20 : ℂ) • 1),
    (-(Real.sqrt (3 / 3080) : ℂ)) • (Jz 8 * Jplus 8 + Jplus 8 * Jz 8),
    (Real.sqrt (3 / 3080) : ℂ) • (Jz 8 * (Jplus 8)ᴴ + (Jplus 8)ᴴ * Jz 8),
    (Real.sqrt (3 / 3080) : ℂ) • (Jplus 8 * Jplus 8),
    (Real.sqrt (3 / 3080) : ℂ) • ((Jplus 8)ᴴ * (Jplus 8)ᴴ)]

private def witnessChannel : MatrixMap (Fin 9) (Fin 9) ℂ :=
  MatrixMap.of_kraus witnessKraus witnessKraus

private def quadrupole (a b : Fin 3) : Matrix (Fin 9) (Fin 9) ℂ :=
  let j : Fin 3 → Matrix (Fin 9) (Fin 9) ℂ := ![Jx 8, Jy 8, Jz 8]
  (1 / 2 : ℂ) • (j a * j b + j b * j a) -
    (if a = b then (20 / 3 : ℂ) else 0) • 1

private def witnessOutput : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r =>
    (![22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584] r : ℂ) / 194040)

private lemma dicke_isometry (n : ℕ) : (dickeIsometry n)ᴴ * dickeIsometry n = 1 := by
  sorry

private lemma tensor_preserves_symmetric (n : ℕ)
    (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    qubitPower n u.val * dickeIsometry n = dickeIsometry n * spinAction n u := by
  sorry

private lemma dicke_split_partialTrace (t s : ℕ)
    (ρ : Matrix (Fin (t + s + 1)) (Fin (t + s + 1)) ℂ) :
    let v := dickeIsometry (t + s)
    let w := fun xy : (Fin t → Fin 2) × (Fin s → Fin 2) =>
      Fin.append xy.1 xy.2
    partialTraceRight ((v * ρ * vᴴ).submatrix w w) =
      dickeIsometry t * reducedState t ρ * (dickeIsometry t)ᴴ := by
  sorry

private def krausShift : Fin 5 → ℤ := ![0, -1, 1, -2, 2]

private def krausAmplitude (q : Fin 5) (r : Fin 9) : ℝ :=
  let z : ℝ := 4 - r.val
  let c := Real.sqrt (3 / 3080)
  ![(3 * z ^ 2 - 20) / Real.sqrt 1540,
    -c * (2 * z + 1) * Real.sqrt (20 - z * (z + 1)),
    c * (2 * z - 1) * Real.sqrt (20 - (z - 1) * z),
    c * Real.sqrt (20 - z * (z + 1)) * Real.sqrt (20 - (z + 1) * (z + 2)),
    c * Real.sqrt (20 - (z - 1) * z) * Real.sqrt (20 - (z - 2) * (z - 1))] q

private def krausWeight (q : Fin 5) (r : Fin 9) : ℝ :=
  let z : ℝ := 4 - r.val
  ![(3 * z ^ 2 - 20) ^ 2 / 1540,
    3 / 3080 * (2 * z + 1) ^ 2 * (20 - z * (z + 1)),
    3 / 3080 * (2 * z - 1) ^ 2 * (20 - (z - 1) * z),
    3 / 3080 * (20 - z * (z + 1)) * (20 - (z + 1) * (z + 2)),
    3 / 3080 * (20 - (z - 1) * z) * (20 - (z - 2) * (z - 1))] q

private lemma kraus_entry (q : Fin 5) (i r : Fin 9) :
    witnessKraus q i r =
      if (i.val : ℤ) = (r.val : ℤ) + krausShift q then (krausAmplitude q r : ℂ)
      else 0 := by
  fin_cases q <;> fin_cases i <;> fin_cases r <;>
    norm_num [witnessKraus, krausShift, krausAmplitude, Jplus, Jz, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_ofReal] <;> ring

private lemma kraus_amplitude_sq (q : Fin 5) (r : Fin 9) :
    krausAmplitude q r ^ 2 = krausWeight q r := by
  fin_cases q <;> fin_cases r <;>
    norm_num [krausAmplitude, krausWeight, mul_pow, div_pow, Real.sq_sqrt]

private lemma kraus_column_product (q : Fin 5) (i : Fin 9) (r s : Fin 9) :
    star (witnessKraus q i r) * witnessKraus q i s =
      if r = s ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q then
        (krausWeight q r : ℂ) else 0 := by
  rw [kraus_entry, kraus_entry]
  by_cases hr : (i.val : ℤ) = (r.val : ℤ) + krausShift q
  · by_cases hs : (i.val : ℤ) = (s.val : ℤ) + krausShift q
    · have hrs : r = s := Fin.ext (by omega)
      subst s
      simp only [hr, ite_true, true_and, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← sq, kraus_amplitude_sq]
    · have hrs : r ≠ s := by intro he; subst s; exact hs hr
      simp [hr, hs, hrs]
  · simp [hr]

private lemma kraus_complete : ∑ q, (witnessKraus q)ᴴ * witnessKraus q = 1 := by
  ext r s
  simp only [Finset.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [kraus_column_product]
  fin_cases r <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ, krausShift, krausWeight, Matrix.one_apply]

private lemma cartesian_channel (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel x = (3 / 770 : ℂ) •
      ∑ a : Fin 3, ∑ b : Fin 3, quadrupole a b * x * quadrupole a b := by
  sorry

private lemma collective_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3,
        spinAction 8 u * (![Jx 8, Jy 8, Jz 8] a) * (spinAction 8 u)ᴴ =
          ∑ c : Fin 3, (r a c : ℂ) • (![Jx 8, Jy 8, Jz 8] c) := by
  sorry

private lemma channel_covariant (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (x : Matrix (Fin 9) (Fin 9) ℂ) :
    witnessChannel (spinAction 8 u * x * (spinAction 8 u)ᴴ) =
      spinAction 8 u * witnessChannel x * (spinAction 8 u)ᴴ := by
  sorry

private lemma witness_channel : IsCovariantChannel (n := 8) witnessChannel := by
  exact ⟨MatrixMap.of_kraus_isCompletelyPositive witnessKraus,
    MatrixMap.IsTracePreserving.of_kraus_isTracePreserving
      witnessKraus witnessKraus kraus_complete, channel_covariant⟩

private lemma witness_state : witnessState.PosSemidef ∧ witnessState.trace = 1 := by
  constructor
  · apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
  · norm_num [witnessState, trace_diagonal, Fin.sum_univ_succ]

private lemma witness_output : witnessChannel witnessState = witnessOutput := by
  sorry

private lemma split_product (n t : ℕ) (k m : Fin (t + 1))
    (l : Fin (n - t + 1)) (r : Fin (n + 1)) :
    dickeSplit n t (k, l) r * star (dickeSplit n t (m, l) r) =
      if k = m ∧ k.val + l.val = r.val then
        (((t.choose k.val : ℝ) * ((n - t).choose l.val : ℝ) /
          (n.choose r.val : ℝ) : ℝ) : ℂ) else 0 := by
  by_cases hk : k.val + l.val = r.val
  · by_cases hm : m.val + l.val = r.val
    · have hkm : k = m := Fin.ext (by omega)
      subst m
      simp only [dickeSplit, hk, and_self, ite_true, Complex.star_def,
        Complex.conj_ofReal]
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← sq, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    · have hkm : k ≠ m := by intro h; subst m; exact hm hk
      simp [dickeSplit, hk, hm, hkm]
  · simp [dickeSplit, hk]

private lemma split_weight_sum (n t : ℕ) (k : Fin (t + 1)) (r : Fin (n + 1)) :
    (∑ l : Fin (n - t + 1), if k.val + l.val = r.val then
      (t.choose k.val : ℝ) * ((n - t).choose l.val : ℝ) / (n.choose r.val : ℝ)
      else 0) =
      (t.choose k.val : ℝ) * ((n - t).choose (r.val - k.val) : ℝ) /
        (n.choose r.val : ℝ) * (if k.val ≤ r.val then 1 else 0) := by
  by_cases hk : k.val ≤ r.val
  · by_cases hl : r.val - k.val ≤ n - t
    · let l : Fin (n - t + 1) := ⟨r.val - k.val, by omega⟩
      rw [Finset.sum_eq_single l]
      · simp [l, hk, Nat.add_sub_of_le hk]
      · intro b _ hbl
        have hne : k.val + b.val ≠ r.val := by
          intro he
          apply hbl
          apply Fin.ext
          dsimp [l]
          omega
        simp [hne]
      · simp
    · have hc : (n - t).choose (r.val - k.val) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [hc, Nat.cast_zero, mul_zero, zero_div, zero_mul]
      apply Finset.sum_eq_zero
      intro l _
      have hne : k.val + l.val ≠ r.val := by omega
      simp [hne]
  · simp only [hk, ite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro l _
    have hne : k.val + l.val ≠ r.val := by omega
    simp [hne]

private lemma diagonal_reduction (n t : ℕ) (ht : t ≤ n) (p : Fin (n + 1) → ℝ) :
    reducedState t (diagonal (fun r => (p r : ℂ))) =
      diagonal (fun k => ((∑ r : Fin (n + 1), p r *
        (t.choose k.val : ℝ) * ((n - t).choose (r.val - k.val) : ℝ) /
        (n.choose r.val : ℝ) * (if k.val ≤ r.val then 1 else 0) : ℝ) : ℂ)) := by
  have he (k m : Fin (t + 1)) :
      reducedState t (diagonal (fun r => (p r : ℂ))) k m =
        ∑ l : Fin (n - t + 1), ∑ r : Fin (n + 1),
          (p r : ℂ) * (dickeSplit n t (k, l) r * star (dickeSplit n t (m, l) r)) := by
    change (∑ l : Fin (n - t + 1),
      (dickeSplit n t * diagonal (fun r => (p r : ℂ)) * (dickeSplit n t)ᴴ)
        (k, l) (m, l)) = _
    apply Finset.sum_congr rfl
    intro l _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro r _
    ring
  ext k m
  rw [he]
  simp_rw [split_product]
  by_cases hkm : k = m
  · subst m
    simp only [true_and, diagonal_apply_eq]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [← Complex.ofReal_sum, split_weight_sum]
    push_cast
    ring
  · simp [hkm, diagonal_apply_ne _ hkm]

private lemma input_reduction : reducedState 7 witnessState =
    diagonal (fun k => (![21, 21, 40, 21, 21, 21, 21, 2] k : ℂ) / 168) := by
  have hp : witnessState = diagonal (fun r : Fin 9 =>
      (((![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℝ) / 1764 : ℝ) : ℂ)) := by
    congr 1
    funext r
    fin_cases r <;> norm_num
  rw [hp, diagonal_reduction 8 7 (by norm_num)]
  congr 1
  funext k
  fin_cases k <;> norm_num [Fin.sum_univ_succ, Nat.choose]

private lemma output_reduction : reducedState 7 witnessOutput =
    diagonal (fun k =>
      (![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℂ) / 517440) := by
  have hp : witnessOutput = diagonal (fun r : Fin 9 =>
      (((![22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584] r : ℝ) /
        194040 : ℝ) : ℂ)) := by
    congr 1
    funext r
    fin_cases r <;> norm_num
  rw [hp, diagonal_reduction 8 7 (by norm_num)]
  congr 1
  funext k
  fin_cases k <;> norm_num [Fin.sum_univ_succ, Nat.choose]

private lemma input_distance :
    traceNorm (reducedState 7 witnessState - mixedState 7) = 19 / 84 := by
  rw [input_reduction]
  have he : diagonal (fun k => (![21, 21, 40, 21, 21, 21, 21, 2] k : ℂ) / 168) -
      mixedState 7 = diagonal (fun k : Fin 8 =>
        (((![21, 21, 40, 21, 21, 21, 21, 2] k : ℝ) / 168 - 1 / 8 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> norm_num [mixedState]
    · simp [mixedState, diagonal_apply, hij]
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_succ]

private lemma output_distance :
    traceNorm (reducedState 7 (witnessChannel witnessState) - mixedState 7) =
      3933 / 17248 := by
  rw [witness_output, output_reduction]
  have he : diagonal (fun k =>
      (![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℂ) / 517440) -
      mixedState 7 = diagonal (fun k : Fin 8 =>
        (((![69468, 87252, 64205, 82635, 78360, 59892, 43533, 32095] k : ℝ) /
          517440 - 1 / 8 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> norm_num [mixedState]
    · simp [mixedState, diagonal_apply, hij]
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_succ]

private lemma normalizer_positive : 0 < normalizer 7 := by
  have hm : (mixedState 7).PosSemidef ∧ (mixedState 7).trace = 1 := by
    have he : mixedState 7 = diagonal (fun _ : Fin 8 => (1 / 8 : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> norm_num [mixedState, diagonal_apply, hij]
    rw [he]
    exact ⟨posSemidef_diagonal_iff.mpr (by
      intro i; norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]), by norm_num⟩
  have hnorm (σ : Matrix (Fin 8) (Fin 8) ℂ) (hσ : σ.PosSemidef) (ht : σ.trace = 1) :
      traceNorm σ = 1 := by
    have h := congrArg Complex.re
      (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef hσ)
    simpa [ht] using h
  have hb : BddAbove {d : ℝ | ∃ σ : Matrix (Fin 8) (Fin 8) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧ d = traceNorm (σ - mixedState 7)} := by
    refine ⟨2, ?_⟩
    rintro d ⟨σ, hσ, ht, rfl⟩
    have h := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le
      σ (-(mixedState 7))
    rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg,
      hnorm σ hσ ht, hnorm _ hm.1 hm.2, ← sub_eq_add_neg] at h
    norm_num at h ⊢
    exact h
  let σ : Matrix (Fin 8) (Fin 8) ℂ := diagonal (fun i => if i = 0 then 1 else 0)
  have hσ : σ.PosSemidef ∧ σ.trace = 1 := by
    constructor
    · apply posSemidef_diagonal_iff.mpr
      intro i
      split_ifs <;> norm_num
    · simp [σ]
  have hd : traceNorm (σ - mixedState 7) = 7 / 4 := by
    have he : σ - mixedState 7 = diagonal (fun i : Fin 8 =>
        (((if i = 0 then 1 else 0) - 1 / 8 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        fin_cases i <;> norm_num [σ, mixedState]
      · simp [σ, mixedState, diagonal_apply, hij]
    rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
    norm_num [Fin.sum_univ_succ]
  have hle : 7 / 4 ≤ normalizer 7 :=
    le_csSup hb ⟨σ, hσ.1, hσ.2, hd.symm⟩
  linarith

theorem result : ¬ claim := by
  intro h
  have hm := h 8 (by norm_num) 7 (by norm_num) (by norm_num)
    witnessChannel witness_channel witnessState witness_state.1 witness_state.2
  change 1 - traceNorm (reducedState 7 witnessState - mixedState 7) / normalizer 7 ≤
    1 - traceNorm (reducedState 7 (witnessChannel witnessState) - mixedState 7) /
      normalizer 7 at hm
  rw [input_distance, output_distance] at hm
  have hlt : (19 / 84 : ℝ) / normalizer 7 < (3933 / 17248 : ℝ) / normalizer 7 :=
    (div_lt_div_iff_of_pos_right normalizer_positive).2 (by norm_num)
  linarith

end D5.S3.Quantum.Measurement.AnticoherenceTraceDistanceRefutation
