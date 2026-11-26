/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformAntisymmetricTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformAntisymmetricTransfer
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreTransferRecurrence, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization]
   utility: none
   digest: The singlet contraction of uniform periodic trace tensors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreTransferRecurrence
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Antisymmetric marginal of a periodic bond-two MPS

The mixed transfer is bra-first, with no relation between the two families
until the specialization to the actual raw two-site marginal.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformAntisymmetricTransfer

open PeriodicMPSUniformHardCoreTransferRecurrence
  (TwoBits binaryTransfer binaryInsertion binaryRawTransfer conjugateJet eval_binaryRawTransfer)
open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open scoped Matrix Kronecker BigOperators

noncomputable section

variable {R : Type*}

abbrev BondMatrix (R : Type*) := Matrix (Fin 2) (Fin 2) R
abbrev TransferMatrix (R : Type*) := Matrix TwoBits TwoBits R

section Ring

variable [CommRing R]

/-- The commutator of the zero and one matrices in a binary core. -/
def coreCommutator (A : Fin 2 → BondMatrix R) : BondMatrix R :=
  A 0 * A 1 - A 1 * A 0

/-- The determinant of the core commutator. -/
def commutatorDet (A : Fin 2 → BondMatrix R) : R :=
  (coreCommutator A).det

/-- The bra-first mixed transfer, C ⊗ A + D ⊗ B. -/
def mixedTransfer (ket bra : Fin 2 → BondMatrix R) : TransferMatrix R :=
  binaryTransfer bra ket

/-- The characteristic recurrence, with coefficients in ascending order. -/
def characteristicRecurrence (T : TransferMatrix R) : LinearRecurrence R :=
  ⟨4, fun i => -T.charpoly.coeff i⟩

private lemma charpoly_natDegree [Nontrivial R] (T : TransferMatrix R) :
    T.charpoly.natDegree = 4 := by
  rw [Matrix.charpoly_natDegree_eq_dim]
  decide

private lemma trace_eq_neg_coeff_three (T : TransferMatrix R) :
    T.trace = -T.charpoly.coeff 3 := by
  simpa only [show Fintype.card TwoBits - 1 = 3 by decide] using
    Matrix.trace_eq_neg_charpoly_coeff T

/-- Cayley–Hamilton gives the order-four recurrence for any linear transfer readout. -/
theorem transferReadout_isSolution (T : TransferMatrix R)
    (readout : TransferMatrix R →ₗ[R] R) :
    (characteristicRecurrence T).IsSolution (fun m => readout (T ^ m)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro m
    exact Subsingleton.elim _ _
  intro m
  have heval : readout (T ^ m * Polynomial.aeval T T.charpoly) = 0 := by
    rw [Matrix.aeval_self_charpoly, mul_zero, map_zero]
  rw [Polynomial.aeval_eq_sum_range, charpoly_natDegree T, Finset.sum_range_succ] at heval
  simp only [mul_add, Finset.mul_sum, Algebra.mul_smul_comm, ← pow_add, map_add,
    map_sum, map_smul, smul_eq_mul] at heval
  have hmonic : T.charpoly.coeff 4 = 1 :=
    charpoly_natDegree T ▸ (Matrix.charpoly_monic T).coeff_natDegree
  rw [hmonic, one_mul] at heval
  change readout (T ^ (m + 4)) = ∑ i : Fin 4, -T.charpoly.coeff i * readout (T ^ (m + i))
  rw [Fin.sum_univ_eq_sum_range (fun i => -T.charpoly.coeff i * readout (T ^ (m + i))) 4]
  simpa only [neg_mul, ← Finset.sum_neg_distrib] using eq_neg_of_add_eq_zero_right heval

private lemma trace_commutator (A : Fin 2 → BondMatrix R) :
    (coreCommutator A).trace = 0 := by
  rw [coreCommutator, Matrix.trace_sub, Matrix.trace_mul_comm (A 0) (A 1), sub_self]

private lemma trace_commutator_symbol (A : Fin 2 → BondMatrix R) (i : Fin 2) :
    (coreCommutator A * A i).trace = 0 := by
  fin_cases i <;>
    simp [coreCommutator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.sub_apply, Fin.sum_univ_two] <;> ring

private lemma trace_commutator_word2 (A : Fin 2 → BondMatrix R) (i j : Fin 2) :
    (coreCommutator A * (A i * A j)).trace =
      if i = j then 0 else if i = 0 then -commutatorDet A else commutatorDet A := by
  fin_cases i <;> fin_cases j <;>
    simp [commutatorDet, coreCommutator, Matrix.det_fin_two, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two] <;> ring

private lemma trace_commutator_word3 (A : Fin 2 → BondMatrix R) (i j k : Fin 2) :
    (coreCommutator A * (A i * A j * A k)).trace =
      if i = j then (A i).trace * (coreCommutator A * (A i * A k)).trace
      else if j = k then (A k).trace * (coreCommutator A * (A i * A k)).trace else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [coreCommutator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.sub_apply, Fin.sum_univ_two] <;> ring

end Ring

section GeneratingFunction

variable [CommRing R] [Nontrivial R]

private lemma charpolyRev_coeff (T : TransferMatrix R) (j : ℕ) (hj : j ≤ 4) :
    T.charpolyRev.coeff j = T.charpoly.coeff (4 - j) := by
  rw [← T.reverse_charpoly, Polynomial.coeff_reverse, charpoly_natDegree T,
    Polynomial.revAt_le hj]

private lemma charpolyRev_coeff_zero_of_gt (T : TransferMatrix R) (j : ℕ) (hj : 4 < j) :
    T.charpolyRev.coeff j = 0 := by
  rw [← T.reverse_charpoly, Polynomial.coeff_reverse, charpoly_natDegree T,
    Polynomial.revAt_eq_self_of_lt hj]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [charpoly_natDegree T])

end GeneratingFunction

section CompleteHomogeneous

variable [CommRing R]

/-- Formal reciprocal of det(I - zT), whose coefficients are the complete
homogeneous transfer factors. The constant term of det(I - zT) is 1. -/
def transferSeries (T : TransferMatrix R) : PowerSeries R :=
  PowerSeries.invOfUnit (T.charpolyRev : PowerSeries R) 1

/-- The degree-m coefficient of 1 / det(I - zT). -/
def completeHomogeneous (T : TransferMatrix R) (m : ℕ) : R :=
  PowerSeries.coeff m (transferSeries T)

theorem charpolyRev_mul_transferSeries (T : TransferMatrix R) :
    (T.charpolyRev : PowerSeries R) * transferSeries T = 1 := by
  apply PowerSeries.mul_invOfUnit
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero]
  simp

@[simp] theorem completeHomogeneous_zero (T : TransferMatrix R) :
    completeHomogeneous T 0 = 1 := by
  simp [completeHomogeneous, PowerSeries.coeff_zero_eq_constantCoeff_apply, transferSeries]

@[simp] theorem completeHomogeneous_one (T : TransferMatrix R) :
    completeHomogeneous T 1 = T.trace := by
  have h := congrArg (PowerSeries.coeff 1) (charpolyRev_mul_transferSeries T)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (T.charpolyRev : PowerSeries R) *
      PowerSeries.coeff j (transferSeries T))] at h
  simpa [Finset.sum_range_succ, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    completeHomogeneous, transferSeries, sub_eq_add_neg, eq_comm (a := (0 : R)),
    add_neg_eq_zero] using h

private def paddedSeries (T : TransferMatrix R) : PowerSeries R :=
  PowerSeries.X ^ 2 * transferSeries T

private lemma paddedSeries_coeff (T : TransferMatrix R) (m : ℕ) :
    PowerSeries.coeff m (paddedSeries T) =
      if 2 ≤ m then completeHomogeneous T (m - 2) else 0 := by
  rw [paddedSeries, PowerSeries.coeff_X_pow_mul']
  rfl

private lemma charpolyRev_mul_paddedSeries (T : TransferMatrix R) :
    (T.charpolyRev : PowerSeries R) * paddedSeries T = PowerSeries.X ^ 2 := by
  unfold paddedSeries
  rw [mul_left_comm, charpolyRev_mul_transferSeries, mul_one]

private lemma paddedSeries_isSolution (T : TransferMatrix R) :
    (characteristicRecurrence T).IsSolution (fun m => PowerSeries.coeff m (paddedSeries T)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro m
    exact Subsingleton.elim _ _
  intro m
  let f := fun j => T.charpolyRev.coeff j * PowerSeries.coeff (m + 4 - j) (paddedSeries T)
  have hc := congrArg (PowerSeries.coeff (m + 4)) (charpolyRev_mul_paddedSeries T)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (T.charpolyRev : PowerSeries R) *
      PowerSeries.coeff j (paddedSeries T)), PowerSeries.coeff_X_pow, ite_eq_right (by omega)] at hc
  simp only [Polynomial.coeff_coe] at hc
  change ∑ j ∈ Finset.range (m + 4 + 1), f j = 0 at hc
  have hsum : ∑ j ∈ Finset.range 5, f j = ∑ j ∈ Finset.range (m + 4 + 1), f j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hgt : 4 < j := Nat.not_lt.mp (fun h => hj (Finset.mem_range.mpr h))
    simp [f, charpolyRev_coeff_zero_of_gt T j hgt]
  rw [← hsum] at hc
  have hmonic : T.charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  change PowerSeries.coeff (m + 4) (paddedSeries T) =
    ∑ i : Fin 4, -T.charpoly.coeff i * PowerSeries.coeff (m + i) (paddedSeries T)
  rw [Fin.sum_univ_eq_sum_range
    (fun i => -T.charpoly.coeff i * PowerSeries.coeff (m + i) (paddedSeries T)) 4]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hc ⊢
  dsimp only [f] at hc
  rw [hmonic, Nat.sub_zero, one_mul, charpolyRev_coeff T 1 (by decide),
    charpolyRev_coeff T 2 (by decide), charpolyRev_coeff T 3 (by decide),
    charpolyRev_coeff T 4 (by decide)] at hc
  simp only [Nat.reduceSub, show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, Nat.add_sub_cancel,
    Nat.add_zero] at hc ⊢
  linear_combination hc

end CompleteHomogeneous

section Field

variable [Field R]

/-- Antisymmetric raw readout at transfer exponent m. The factor 1/2 comes
from contracting with (|01⟩ - |10⟩) / √2 on both sides. The unnormalized difference vector
gives twice this readout. -/
def antisymmetricTransfer (ket bra : Fin 2 → BondMatrix R) (m : ℕ) : R :=
  (1 / 2 : R) *
    ((coreCommutator bra ⊗ₖ coreCommutator ket) * mixedTransfer ket bra ^ m).trace

theorem antisymmetricTransfer_isSolution (ket bra : Fin 2 → BondMatrix R) :
    (characteristicRecurrence (mixedTransfer ket bra)).IsSolution
      (antisymmetricTransfer ket bra) := by
  let readout : TransferMatrix R →ₗ[R] R :=
    (1 / 2 : R) •
      ((Matrix.traceLinearMap TwoBits R R).comp
        (LinearMap.mulLeft R (coreCommutator bra ⊗ₖ coreCommutator ket)))
  exact transferReadout_isSolution (mixedTransfer ket bra) readout

@[simp] theorem antisymmetricTransfer_zero (ket bra : Fin 2 → BondMatrix R) :
    antisymmetricTransfer ket bra 0 = 0 := by
  simp [antisymmetricTransfer, Matrix.trace_kronecker, trace_commutator]

@[simp] theorem antisymmetricTransfer_one (ket bra : Fin 2 → BondMatrix R) :
    antisymmetricTransfer ket bra 1 = 0 := by
  simp [antisymmetricTransfer, mixedTransfer, binaryTransfer, mul_add, Matrix.trace_add,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, trace_commutator_symbol]

variable [CharZero R]

@[simp] theorem antisymmetricTransfer_two (ket bra : Fin 2 → BondMatrix R) :
    antisymmetricTransfer ket bra 2 = commutatorDet ket * commutatorDet bra := by
  simp only [antisymmetricTransfer, mixedTransfer, binaryTransfer, pow_succ, pow_zero, one_mul,
    add_mul, mul_add, Matrix.trace_add, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    trace_commutator_word2]
  norm_num [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]
  ring

@[simp] theorem antisymmetricTransfer_three (ket bra : Fin 2 → BondMatrix R) :
    antisymmetricTransfer ket bra 3 =
      (mixedTransfer ket bra).trace * (commutatorDet ket * commutatorDet bra) := by
  simp only [antisymmetricTransfer, mixedTransfer, binaryTransfer, pow_succ, pow_zero, one_mul,
    add_mul, mul_add, Matrix.trace_add, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    trace_commutator_word3, trace_commutator_word2]
  norm_num [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]
  ring

omit [CharZero R] in
/-- The characteristic recurrence in descending lag order. -/
theorem antisymmetricTransfer_recurrence (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    let T := mixedTransfer ket bra
    let a := antisymmetricTransfer ket bra
    a (m + 4) = T.trace * a (m + 3) - T.charpoly.coeff 2 * a (m + 2) -
      T.charpoly.coeff 1 * a (m + 1) - T.charpoly.coeff 0 * a m := by
  dsimp only
  let T := mixedTransfer ket bra
  let a := antisymmetricTransfer ket bra
  have h := antisymmetricTransfer_isSolution ket bra m
  change a (m + 4) = ∑ i : Fin 4, -T.charpoly.coeff i * a (m + i) at h
  rw [Fin.sum_univ_eq_sum_range (fun i => -T.charpoly.coeff i * a (m + i)) 4] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero] at h
  change a (m + 4) = T.trace * a (m + 3) - T.charpoly.coeff 2 * a (m + 2) -
    T.charpoly.coeff 1 * a (m + 1) - T.charpoly.coeff 0 * a m
  rw [trace_eq_neg_coeff_three]
  linear_combination h

/-- The all-exponent factorization, with the chain-length shift made explicit. -/
theorem antisymmetricTransfer_factor (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    antisymmetricTransfer ket bra (m + 2) =
      commutatorDet ket * commutatorDet bra * completeHomogeneous (mixedTransfer ket bra) m := by
  let T := mixedTransfer ket bra
  let d := commutatorDet ket * commutatorDet bra
  let E := characteristicRecurrence T
  have hp : E.IsSolution (fun k => d * PowerSeries.coeff k (paddedSeries T)) := by
    apply (E.is_sol_iff_mem_solSpace _).mpr
    exact E.solSpace.smul_mem d ((E.is_sol_iff_mem_solSpace _).mp (paddedSeries_isSolution T))
  have hi : Set.EqOn (antisymmetricTransfer ket bra)
      (fun k => d * PowerSeries.coeff k (paddedSeries T)) (Finset.range E.order) := by
    intro k hk
    have hk' : k < 4 := Finset.mem_range.mp hk
    interval_cases k <;>
      simp [paddedSeries_coeff, d, T, mul_comm]
  have h := (E.eq_iff_eqOn_range_order _ _ (antisymmetricTransfer_isSolution ket bra) hp).mpr hi
  simpa [paddedSeries_coeff, T, d] using congrFun h (m + 2)

/-- The antisymmetric series has numerator Δket Δbra z² and denominator det(I - zT). -/
theorem antisymmetricTransfer_series (ket bra : Fin 2 → BondMatrix R) :
    PowerSeries.mk (antisymmetricTransfer ket bra) =
      PowerSeries.C (commutatorDet ket * commutatorDet bra) *
        (PowerSeries.X ^ 2 * transferSeries (mixedTransfer ket bra)) := by
  ext m
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hm : 2 ≤ m
  · rw [ite_eq_left hm, ← Nat.sub_add_cancel hm]
    simpa [completeHomogeneous] using antisymmetricTransfer_factor ket bra (m - 2)
  · interval_cases m <;> simp

end Field

/-- The singlet readout is the four-entry contraction with
(|01⟩ - |10⟩) / √2 on both sides. The unnormalized difference vector
gives twice this readout. -/
def singletReadout [Field R] (M : TransferMatrix R) : R :=
  (1 / 2 : R) * (M (0, 1) (0, 1) - M (0, 1) (1, 0) -
    M (1, 0) (0, 1) + M (1, 0) (1, 0))

/-- The unit singlet vector in the physical two-bit basis. -/
def singletVector (p : TwoBits) : ℂ :=
  (↑((Real.sqrt 2)⁻¹) : ℂ) *
    (if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0)

theorem singletReadout_eq_expectation (M : TransferMatrix ℂ) :
    singletReadout M = star singletVector ⬝ᵥ (M *ᵥ singletVector) := by
  have hscale : (↑((Real.sqrt 2)⁻¹) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold singletReadout
  rw [← hscale]
  norm_num [singletVector, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Mixed two-site entries in ket-row, bra-column order, with bra-first transfer. -/
def mixedRaw [CommRing R] (ket bra : Fin 2 → BondMatrix R) (m : ℕ) : TransferMatrix R :=
  fun p q => (binaryInsertion bra ket q p * mixedTransfer ket bra ^ m).trace

theorem singletReadout_mixedRaw [Field R] (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    singletReadout (mixedRaw ket bra m) = antisymmetricTransfer ket bra m := by
  have h :
      binaryInsertion bra ket (0, 1) (0, 1) - binaryInsertion bra ket (1, 0) (0, 1) -
        binaryInsertion bra ket (0, 1) (1, 0) + binaryInsertion bra ket (1, 0) (1, 0) =
        coreCommutator bra ⊗ₖ coreCommutator ket := by
    ext i j
    simp only [binaryInsertion, coreCommutator, Matrix.add_apply, Matrix.sub_apply,
      Matrix.kroneckerMap_apply]
    ring
  rw [singletReadout, antisymmetricTransfer, ← h, add_mul, sub_mul, sub_mul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  rfl

/-- At length m + 4, the independent-core mixed singlet factors for every m. -/
theorem singletReadout_mixedRaw_factor [Field R] [CharZero R]
    (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    singletReadout (mixedRaw ket bra (m + 2)) =
      commutatorDet ket * commutatorDet bra * completeHomogeneous (mixedTransfer ket bra) m := by
  rw [singletReadout_mixedRaw, antisymmetricTransfer_factor]

/-- The trace of the mixed raw marginal equals the length-(m + 2) partition function. -/
theorem mixedRaw_trace [CommRing R] (ket bra : Fin 2 → BondMatrix R) (m : ℕ) :
    (mixedRaw ket bra m).trace = (mixedTransfer ket bra ^ (m + 2)).trace := by
  rw [show m + 2 = 2 + m by omega, pow_add]
  have h : (∑ p : TwoBits, binaryInsertion bra ket p p) = mixedTransfer ket bra ^ 2 := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, binaryInsertion, mixedTransfer,
      binaryTransfer, pow_two, add_mul, mul_add, ← Matrix.mul_kronecker_mul]
    ac_rfl
  rw [← h, Finset.sum_mul, Matrix.trace_sum]
  rfl

/-- The physical bra uses entrywise conjugation of the ket matrices. -/
def conjugateCore (A : Fin 2 → Bond) : Fin 2 → Bond :=
  fun i => (A i).map (starRingEnd ℂ)

private lemma map_kronecker {S V : Type*} [CommSemiring S] [CommSemiring V]
    (f : S →+* V) (P Q : BondMatrix S) :
    f.mapMatrix (P ⊗ₖ Q) = f.mapMatrix P ⊗ₖ f.mapMatrix Q := by
  ext i j
  exact f.map_mul _ _

private lemma rawTwo_eq_ketFirst (A : Fin 2 → Bond) (s : ℕ) (p q : TwoBits) :
    rawTwo A s p q =
      (binaryInsertion A (conjugateCore A) p q *
        binaryTransfer A (conjugateCore A) ^ (s + 2)).trace := by
  let f := Polynomial.evalRingHom (0 : ℂ)
  let P : Fin 2 → BondMatrix (Polynomial ℂ) := fun i => Polynomial.C.mapMatrix (A i)
  have hA (i : Fin 2) : f.mapMatrix (P i) = A i := by
    ext j k
    exact Polynomial.eval_C
  have hB (i : Fin 2) : f.mapMatrix (conjugateJet P i) = conjugateCore A i := by
    ext j k
    change ((Polynomial.C (A i j k)).map (starRingEnd ℂ)).eval 0 = starRingEnd ℂ (A i j k)
    rw [Polynomial.map_C, Polynomial.eval_C]
  have h := eval_binaryRawTransfer P 0 s p q
  change f (binaryRawTransfer P p q (s + 4)) =
    rawTwo (fun i => f.mapMatrix (P i)) s p q at h
  rw [show (fun i => f.mapMatrix (P i)) = A from funext hA] at h
  rw [binaryRawTransfer, AddMonoidHom.map_trace f] at h
  change (f.mapMatrix (_ * _ ^ (s + 4 - 2))).trace = _ at h
  simpa only [show s + 4 - 2 = s + 2 by omega, map_mul, map_pow, map_add, binaryInsertion,
    binaryTransfer, map_kronecker, hA, hB] using h.symm

private def swapTransfer : TransferMatrix ℂ ≃ₐ[ℂ] TransferMatrix ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm (Fin 2) (Fin 2))

private lemma swapTransfer_kronecker (P Q : Bond) :
    swapTransfer (P ⊗ₖ Q) = Q ⊗ₖ P := by
  ext i j
  change P i.2 j.2 * Q i.1 j.1 = Q i.1 j.1 * P i.2 j.2
  exact mul_comm _ _

private lemma trace_swapTransfer (M : TransferMatrix ℂ) :
    (swapTransfer M).trace = M.trace := by
  unfold Matrix.trace
  exact Equiv.sum_comp (Equiv.prodComm (Fin 2) (Fin 2)) (fun i => M i i)

/-- The bra-first mixed transfer specializes to the actual rawTwo at length s + 4. -/
theorem rawTwo_eq_mixedRaw (A : Fin 2 → Bond) (s : ℕ) :
    rawTwo A s = mixedRaw A (conjugateCore A) (s + 2) := by
  ext p q
  rw [rawTwo_eq_ketFirst, ← trace_swapTransfer]
  simp only [mixedRaw, mixedTransfer, binaryInsertion, binaryTransfer, map_mul, map_pow,
    map_add, swapTransfer_kronecker]

/-- The numerator of the actual singlet probability, at every length s + 4. -/
theorem rawTwo_singlet_factor (A : Fin 2 → Bond) (s : ℕ) :
    singletReadout (rawTwo A s) =
      commutatorDet A * commutatorDet (conjugateCore A) *
        completeHomogeneous (mixedTransfer A (conjugateCore A)) s := by
  rw [rawTwo_eq_mixedRaw, singletReadout_mixedRaw_factor]

/-- At nonzero raw trace, this is the singlet probability for the trace-one marginal. -/
def singletProbability (A : Fin 2 → Bond) (s : ℕ) : ℂ :=
  singletReadout ((rawTwo A s).trace⁻¹ • rawTwo A s)

/-- The literal trace-normalized singlet probability for every length n ≥ 4. -/
theorem singletProbability_factor (A : Fin 2 → Bond) (n : ℕ) (hn : 4 ≤ n) :
    singletProbability A (n - 4) =
      (commutatorDet A * commutatorDet (conjugateCore A) *
        completeHomogeneous (mixedTransfer A (conjugateCore A)) (n - 4)) /
      (mixedTransfer A (conjugateCore A) ^ n).trace := by
  have hscale (a : ℂ) (M : TransferMatrix ℂ) : singletReadout (a • M) = a * singletReadout M := by
    simp only [singletReadout, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [singletProbability, hscale, rawTwo_singlet_factor, rawTwo_eq_mixedRaw, mixedRaw_trace,
    show n - 4 + 2 + 2 = n by omega, div_eq_mul_inv, mul_comm]

private lemma rawTwo_trace_ofReal (A : Fin 2 → Bond) (s : ℕ) :
    (↑(rawTwo A s).trace.re : ℂ) = (rawTwo A s).trace := by
  have hstar : star (rawTwo A s).trace = (rawTwo A s).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, star_sum,
      PeriodicMPSTwoSiteAmbiguity.rawTwo_star_swap]
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im, Complex.conj_eq_iff_im.mp hstar]

/-- The same formula for the singlet expectation of the repository's normalized marginal. -/
theorem normalizedMarginal_singlet_factor (A : Fin 2 → Bond) (n : ℕ) (hn : 4 ≤ n) :
    star singletVector ⬝ᵥ
        (PeriodicMPSUniformHardCoreLocalization.normalizedMarginal (n - 2) A *ᵥ singletVector) =
      (commutatorDet A * commutatorDet (conjugateCore A) *
        completeHomogeneous (mixedTransfer A (conjugateCore A)) (n - 4)) /
      (mixedTransfer A (conjugateCore A) ^ n).trace := by
  rw [← singletReadout_eq_expectation, show n - 2 = (n - 4) + 2 by omega,
    PeriodicMPSUniformHardCoreLocalization.normalizedMarginal_eq_rawTwo]
  change singletReadout
    ((↑((rawTwo A (n - 4)).trace.re)⁻¹ : ℂ) • rawTwo A (n - 4)) = _
  rw [Complex.ofReal_inv, rawTwo_trace_ofReal]
  exact singletProbability_factor A n hn

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformAntisymmetricTransfer
