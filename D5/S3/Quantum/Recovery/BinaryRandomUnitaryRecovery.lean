/- GID: D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A unitary decoder maximizes binary random-unitary recovery fidelity. -/

import D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian

/-! Unitary diagonalization and the resulting optimal recovery for arbitrary
    pairs of finite-dimensional unitaries. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Matrix
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)

noncomputable section

open D5.S3.Quantum.Recovery.BinaryUnitaryOptimization
open D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel

namespace D5.S3.Quantum.Recovery.BinaryRandomUnitaryRecovery

/-- A unitary has a unitary eigenbasis and all its diagonal entries in that basis
    have modulus one. -/
theorem unitary_diagonalize {d : ℕ} (W : unitaryGroup (Fin d) ℂ) :
    ∃ S : unitaryGroup (Fin d) ℂ, ∃ z : Fin d → ℂ, ∃ hz : ∀ j, ‖z j‖ = 1,
      star S * W * S = diagonalUnitary z hz := by
  obtain ⟨M, hM, z, heq⟩ :=
    Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (W : CodeMatrix d)
  let S : unitaryGroup (Fin d) ℂ := ⟨M, hM⟩
  have hc : ((star S * W * S : unitaryGroup (Fin d) ℂ) : CodeMatrix d) = diagonal z := heq
  have hgram := Unitary.coe_star_mul_self (star S * W * S)
  rw [hc, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at hgram
  have hz (j : Fin d) : ‖z j‖ = 1 := by
    have h := congrArg (fun A : CodeMatrix d => (A j j).re) hgram
    rw [Matrix.diagonal_apply_eq] at h
    change (conj (z j) * z j).re = _ at h
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Matrix.one_apply_eq,
      Complex.one_re, Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (z j)]
  exact ⟨S, z, hz, Subtype.ext hc⟩

private def inBasis {d : ℕ} (L R : unitaryGroup (Fin d) ℂ) (K : CodeMatrix d) :
    CodeMatrix d := (R : CodeMatrix d)ᴴ * K * (L : CodeMatrix d)

private theorem trace_inBasis {d : ℕ} (L R T : unitaryGroup (Fin d) ℂ) (K : CodeMatrix d) :
    trace (K * ((L * T * star R : unitaryGroup (Fin d) ℂ) : CodeMatrix d)) =
      trace (inBasis L R K * (T : CodeMatrix d)) := by
  simp only [Submonoid.coe_mul, Unitary.coe_star, Matrix.star_eq_conjTranspose, inBasis]
  rw [← Matrix.mul_assoc K, Matrix.trace_mul_comm _ ((R : CodeMatrix d)ᴴ)]
  simp only [Matrix.mul_assoc]

private theorem inBasis_complete {d : ℕ} {k : Type*} [Fintype k]
    (L R : unitaryGroup (Fin d) ℂ) (K : k → CodeMatrix d)
    (hK : ∑ a, (K a)ᴴ * K a = 1) :
    ∑ a, (inBasis L R (K a))ᴴ * inBasis L R (K a) = 1 := by
  have hR : (R : CodeMatrix d) * (R : CodeMatrix d)ᴴ = 1 := Unitary.coe_mul_star_self R
  have hL : (L : CodeMatrix d)ᴴ * (L : CodeMatrix d) = 1 := Unitary.coe_star_mul_self L
  calc
    _ = ∑ a, (L : CodeMatrix d)ᴴ * ((K a)ᴴ * K a) * (L : CodeMatrix d) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [inBasis, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        _ = (L : CodeMatrix d)ᴴ * (K a)ᴴ *
            ((R : CodeMatrix d) * (R : CodeMatrix d)ᴴ) * K a * (L : CodeMatrix d) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by simp only [hR, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.sum_mul, ← Matrix.mul_sum, hK, Matrix.mul_one, hL]

private theorem score_inBasis {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (L R T : unitaryGroup (Fin d) ℂ) (D E : CodeChannel d)
    {k : Type*} [Fintype k] (K : k → CodeMatrix d)
    (hD : ∀ X, channelAction D X = ∑ a, K a * X * (K a)ᴴ)
    (hE : ∀ X, channelAction E X =
      ∑ a, inBasis L R (K a) * X * (inBasis L R (K a))ᴴ) :
    recoveryScore (binaryChannel hp hq hpq (L * star R) (L * T * star R)) D =
      recoveryScore (binaryChannel hp hq hpq 1 T) E := by
  rw [binary_score_kraus hd hp hq hpq _ _ D K hD,
    binary_score_kraus hd hp hq hpq _ _ E (inBasis L R ∘ K) hE]
  have h1 (A : CodeMatrix d) :
      trace (A * ((L * star R : unitaryGroup (Fin d) ℂ) : CodeMatrix d)) =
        trace (inBasis L R A) := by
    simpa only [mul_one, Submonoid.coe_one] using trace_inBasis L R 1 A
  simp only [Function.comp_apply, h1, trace_inBasis, Submonoid.coe_one, Matrix.mul_one]

private theorem unitary_score_inBasis {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (L R T Z : unitaryGroup (Fin d) ℂ) :
    recoveryScore (binaryChannel hp hq hpq (L * star R) (L * T * star R))
      (unitaryChannel (R * Z * star L)) =
        recoveryScore (binaryChannel hp hq hpq 1 T) (unitaryChannel Z) := by
  have h : inBasis L R ((R * Z * star L : unitaryGroup (Fin d) ℂ) : CodeMatrix d) = Z := by
    have hg : star R * (R * Z * star L) * L = Z := by
      simp only [Unitary.star_eq_inv]
      group
    exact congrArg Subtype.val hg
  apply score_inBasis hd hp hq hpq L R T _ _
    (fun _ : Unit => ((R * Z * star L : unitaryGroup (Fin d) ℂ) : CodeMatrix d))
  · intro X
    simp only [unitaryChannel_action, Fintype.sum_unique]
  · intro X
    simp only [unitaryChannel_action, Fintype.sum_unique, h]

private theorem binary_unitary_optimal_inBasis {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (L R : unitaryGroup (Fin d) ℂ)
    (z : Fin d → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    ∃ Z : unitaryGroup (Fin d) ℂ, ∀ D : CodeChannel d,
      recoveryScore (binaryChannel hp hq hpq (L * star R)
        (L * diagonalUnitary z hz * star R)) D ≤
      recoveryScore (binaryChannel hp hq hpq (L * star R)
        (L * diagonalUnitary z hz * star R)) (unitaryChannel Z) := by
  obtain ⟨w, hw, hmax⟩ := diagonal_binary_unitary_optimal hd hp hq hpq z hz
  refine ⟨R * diagonalUnitary w hw * star L, fun D => ?_⟩
  let K := actual_kraus_representation D
  obtain ⟨E, hE⟩ := finite_kraus_quantum_channel (inBasis L R ∘ K.kraus)
    (inBasis_complete L R K.kraus K.hkraus)
  rw [score_inBasis hd hp hq hpq L R (diagonalUnitary z hz) D E K.kraus K.haction hE,
    unitary_score_inBasis hd hp hq hpq]
  exact hmax E

/-- A binary random-unitary channel on a nonzero finite code admits a unitary
    decoder maximizing entanglement fidelity at the maximally mixed input
    among all canonical CPTP decoders. Either branch probability may be zero. -/
theorem binary_unitary_optimal {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (U V : unitaryGroup (Fin d) ℂ) :
    ∃ Z : unitaryGroup (Fin d) ℂ, ∀ D : CodeChannel d,
      recoveryScore (binaryChannel hp hq hpq U V) D ≤
      recoveryScore (binaryChannel hp hq hpq U V) (unitaryChannel Z) := by
  obtain ⟨S, z, hz, hdiag⟩ := unitary_diagonalize (star U * V)
  have hU : U * S * star S = U := by simp [mul_assoc]
  have hV : U * S * diagonalUnitary z hz * star S = V := by
    rw [← hdiag]
    simp only [Unitary.star_eq_inv]
    group
  simpa only [hU, hV] using binary_unitary_optimal_inBasis hd hp hq hpq (U * S) S z hz

#print axioms unitary_diagonalize
#print axioms binary_unitary_optimal

end D5.S3.Quantum.Recovery.BinaryRandomUnitaryRecovery
