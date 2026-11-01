/- GID: D5/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/SpeziaSerpentineHigherExteriorTrace
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All exterior traces above order two of the serpentine matrix vanish. -/

/-
admission_basis: open-problem-resolution (#21796; Proved).
Direct same-delivery dependency: D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.charpoly_factor (statement_id sha256:27bcfca35148cd99f4e71acd632b6cce1f15b6b108be600f29a60c293b98ee97), applied in result; its proof uses the re-pinned alternating_sum owner above.
escape_witness: none (the admission uses the external named settlement).
claim: proof_shape: not-applicable(definition); escape_witness: none; consumers: external settlement.
result: proof_shape: bind-only; escape_witness: none; consumers: external settlement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21995.
The characteristic-coefficient exterior trace includes the zero-space case k > n.
The source’s one-based row and column numbers are i.val + 1 and j.val + 1.
-/
import D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.SpeziaSerpentineHigherExteriorTrace

/-- A322844, second conjecture line. M and traceExt are reused from the first
family member; k > n uses the zero exterior-space convention. -/
def claim : Prop :=
  ∀ (n : ℕ) (k : ℕ), 2 < k → D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.traceExt k (D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.M n) = 0

open Polynomial

theorem result : claim := by
  intro n k hk
  unfold D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.traceExt
  split_ifs with hkn
  · have hn : 2 ≤ n := by omega
    have hlow : ¬ n - 2 ≤ n - k := by omega
    have hc : (((D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.M n).charpoly.coeff (n - k) : ℤ) : ℚ) = 0 := by
      change (Int.castRingHom ℚ) ((D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.M n).charpoly.coeff (n - k)) = 0
      rw [← Polynomial.coeff_map (Int.castRingHom ℚ), ← Matrix.charpoly_map,
        D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.charpoly_factor n hn, Polynomial.coeff_X_pow_mul']
      simp [hlow]
    have hz : (D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.M n).charpoly.coeff (n - k) = 0 := by
      exact Rat.intCast_eq_zero_iff.mp hc
    rw [hz, mul_zero]
  · rfl

end D5.S3.Quantum.Matrix.SpeziaSerpentineHigherExteriorTrace
