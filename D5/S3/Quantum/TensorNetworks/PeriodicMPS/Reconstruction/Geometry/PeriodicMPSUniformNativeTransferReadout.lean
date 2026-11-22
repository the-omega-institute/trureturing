/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformNativeTransferReadout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformNativeTransferReadout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Native transfer readout of the periodic two-site marginal. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformAntisymmetricTransfer
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness

/-!
# Native transfer readout of the periodic two-site marginal

The partial trace sums over the words on the residual sites. The corresponding
ordered products of the two transfer symbols sum to the residual transfer power.
We use the bra-first tensor order of the transfer spectrum and the ket-row,
bra-column order of the physical marginal.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformNativeTransferReadout

open PeriodicMPSParentIntersection (Bond Word wordMatrix wordMatrix_append)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSUniformHardCoreMarginalWitness (pairGram pairGram_traceWord)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryTransfer binaryInsertion)
open PeriodicMPSUniformAntisymmetricTransfer
  (mixedTransfer mixedRaw mixedRaw_trace conjugateCore)
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped BigOperators Kronecker

noncomputable section

/-- Every ordered binary tail contributes the Kronecker product of its two
word matrices. The empty tail contributes the identity. -/
theorem mixedTransfer_pow_eq_sum_wordProducts {R : Type*} [CommRing R]
    (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) R) (m : ℕ) :
    mixedTransfer ket bra ^ m =
      ∑ w : Word m,
        (List.ofFn fun i => bra (w i)).prod ⊗ₖ (List.ofFn fun i => ket (w i)).prod := by
  induction m with
  | zero => simp [Finset.univ_unique]
  | succ m ih =>
    rw [pow_succ', ih, ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.prod_cons, Fin.sum_univ_two]
    unfold mixedTransfer binaryTransfer
    simp_rw [Matrix.mul_kronecker_mul, ← Finset.mul_sum, ← add_mul]

private lemma traceWord_prefix (A : Fin 2 → Bond) (p : TwoBits) {m : ℕ} (w : Word m) :
    traceWord 2 2 (2 + m) A (Fin.append ![p.1, p.2] w) =
      (A p.1 * A p.2 * wordMatrix A w).trace := by
  change (wordMatrix A (Fin.append ![p.1, p.2] w)).trace = _
  rw [wordMatrix_append]
  simp [wordMatrix, List.ofFn_succ]

/-- The literal adjacent two-site Gram matrix at period `2 + m` is the
physical specialization of the mixed transfer readout with exponent `m`. -/
theorem pairGram_traceWord_eq_mixedRaw (A : Fin 2 → Bond) (m : ℕ) :
    pairGram (traceWord 2 2 (2 + m) A) = mixedRaw A (conjugateCore A) m := by
  classical
  ext p q
  change (∑ w : Word m, traceWord 2 2 (2 + m) A (Fin.append ![p.1, p.2] w) *
      star (traceWord 2 2 (2 + m) A (Fin.append ![q.1, q.2] w))) =
    (binaryInsertion (conjugateCore A) A q p * mixedTransfer A (conjugateCore A) ^ m).trace
  rw [mixedTransfer_pow_eq_sum_wordProducts, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [traceWord_prefix A p w, traceWord_prefix A q w]
  simp only [binaryInsertion, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  rw [mul_comm ((A p.1 * A p.2 * wordMatrix A w).trace)]
  congr 1
  let f : Bond →+* Bond := RingHom.mapMatrix (starRingEnd ℂ)
  change starRingEnd ℂ (A q.1 * A q.2 * wordMatrix A w).trace =
    (f (A q.1) * f (A q.2) * (List.ofFn fun i => f (A (w i))).prod).trace
  have hword : (List.ofFn fun i => f (A (w i))) =
      (List.ofFn fun i => A (w i)).map f := List.map_ofFn.symm
  rw [hword, ← map_list_prod, ← map_mul, ← map_mul]
  exact AddMonoidHom.map_trace (starRingEnd ℂ) _

/-- The tracked `rawTwo A r` has `r + 2` residual sites. Its entries use
the literal bra-first tensor sum of the transfer spectrum. -/
theorem rawTwo_entry_eq_transfer_power (A : Fin 2 → Bond) (r : ℕ) (p q : TwoBits) :
    rawTwo A r p q =
      (((conjugateCore A q.1 * conjugateCore A q.2) ⊗ₖ (A p.1 * A p.2)) *
        (conjugateCore A 0 ⊗ₖ A 0 + conjugateCore A 1 ⊗ₖ A 1) ^ (r + 2)).trace := by
  change rawTwo A r p q = mixedRaw A (conjugateCore A) (r + 2) p q
  rw [← pairGram_traceWord A r, pairGram_traceWord_eq_mixedRaw]

/-- The raw trace for normalization is the trace of the full-period transfer power. -/
theorem pairGram_traceWord_trace_eq_transfer_power (A : Fin 2 → Bond) (m : ℕ) :
    (pairGram (traceWord 2 2 (2 + m) A)).trace =
      ((conjugateCore A 0 ⊗ₖ A 0 + conjugateCore A 1 ⊗ₖ A 1) ^ (2 + m)).trace := by
  change (pairGram (traceWord 2 2 (2 + m) A)).trace =
    (mixedTransfer A (conjugateCore A) ^ (2 + m)).trace
  rw [pairGram_traceWord_eq_mixedRaw, mixedRaw_trace, Nat.add_comm m 2]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformNativeTransferReadout
