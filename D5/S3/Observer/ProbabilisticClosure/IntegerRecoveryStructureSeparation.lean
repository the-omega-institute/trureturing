/- GID: D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: CRT and Newton layers compose, while a two-dimensional residual remains. -/

import D5.S3.Factorization.PrimePowers.BoundedIntegerCrtCompleteness
import D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation
import D5.S0.Observation.PowerTraceSimilarityCountermodel

/- Library-search audit trail (2026-08-27): Searched the three named repository
   declarations and all Lean sources for a Newton theorem in the forward direction.
   `bounded_integer_crt_complete_iff` is the exact CRT iff; the named power-trace
   theorem is saturation in the direction “equal charpolys plus initial traces imply
   all traces”, not a trace-to-charpoly theorem. The latter direction is therefore an
   explicit bridge premise below. The named countermodel is reused without reproving it.
   Pinned Mathlib searches found `Matrix.trace_eq_neg_charpoly_coeff`,
   `Matrix.charpoly_one`, and `Fin.sum_univ_one`; no stronger bridge was found.
   The selected S3 bucket had 10 Lean files before this module and has 11 after it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.IntegerRecoveryStructureSeparation

open Polynomial
open D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation
open D5.S0.Observation.PowerTraceSimilarityCountermodel
open D5.S3.Factorization.PrimePowers.BoundedIntegerCrtCompleteness
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin

/- The first layer's exact carrier is `Fin N`; these definitions keep that carrier
   visible instead of silently replacing it by an unbounded integer type. -/

def localResiduesAgree (N : Nat) (S : Finset Nat) (kappa : Nat -> Nat)
    (x y : boundedIntegerWindow N) : Prop :=
  primePowerResidueReading N S kappa x = primePowerResidueReading N S kappa y

def boundedIntegerTraceData (n N : Nat) : Type :=
  Fin n -> boundedIntegerWindow N

def initialPowerTracesAgree {K : Type*} [Field K] {n : Nat}
    (A B : Matrix (Fin n) (Fin n) K) : Prop :=
  forall k : Fin n, Matrix.trace (A ^ ((k : Nat) + 1)) =
    Matrix.trace (B ^ ((k : Nat) + 1))

def NewtonCharacteristicPolynomialBridge {K : Type*} [Field K] {n : Nat}
    (A B : Matrix (Fin n) (Fin n) K) : Prop :=
  initialPowerTracesAgree A B -> A.charpoly = B.charpoly

def positivePowerTracesAgree {K : Type*} [Field K] {n : Nat}
    (A B : Matrix (Fin n) (Fin n) K) : Prop :=
  forall r, Matrix.trace (A ^ (r + 1)) = Matrix.trace (B ^ (r + 1))

/-- CRT recovery is exact pointwise on the bounded integer-trace carrier. -/
theorem local_residue_recovery_is_exact
    (N : Nat) (S : Finset Nat) (kappa : Nat -> Nat)
    (hS : forall p, p ∈ S -> Nat.Prime p)
    (hheight : N ≤ primePowerProduct S kappa)
    (x y : boundedIntegerWindow N)
    (hresidues : localResiduesAgree N S kappa x y) :
    x = y := by
  exact (bounded_integer_crt_complete_iff N S kappa hS).2 hheight hresidues

#print axioms local_residue_recovery_is_exact

/- The chain exposes every layer's own premise. `hNewton` is intentionally a
   premise: the imported theorem has the reverse saturation direction, so this
   module does not claim to prove a Newton converse that is not present. The
   prime hypothesis is consumed only by the CRT layer; the saturation and
   similarity layers use a field and dimension, not primality. The `Nat.Prime 2`
   fact in the finite-field counterexample only constructs its `ZMod 2` field. -/
/-- Local residues recover bounded integer traces, then an explicit Newton bridge
    gives the characteristic polynomial; the existing saturation theorem supplies
    all later traces once that polynomial is equal. -/
theorem integer_recovery_structure_recovery_chain
    (N : Nat) (S : Finset Nat) (kappa : Nat -> Nat)
    (hS : forall p, p ∈ S -> Nat.Prime p)
    (hheight : N ≤ primePowerProduct S kappa)
    {K : Type*} [Field K] {n : Nat}
    (A B : Matrix (Fin n) (Fin n) K)
    (hNewton : NewtonCharacteristicPolynomialBridge A B)
    (traceCodesA traceCodesB : boundedIntegerTraceData n N)
    (hresidues : forall k : Fin n,
      localResiduesAgree N S kappa (traceCodesA k) (traceCodesB k))
    (halignment : forall k : Fin n,
      Matrix.trace (A ^ ((k : Nat) + 1)) = (traceCodesA k).val ∧
      Matrix.trace (B ^ ((k : Nat) + 1)) = (traceCodesB k).val) :
    traceCodesA = traceCodesB ∧
      A.charpoly = B.charpoly ∧
      positivePowerTracesAgree A B := by
  have hCodes : traceCodesA = traceCodesB := by
    funext k
    apply Fin.ext
    exact congrArg Fin.val
      ((bounded_integer_crt_complete_iff N S kappa hS).2 hheight (hresidues k))
  have hInitial : initialPowerTracesAgree A B := by
    intro k
    calc
      Matrix.trace (A ^ ((k : Nat) + 1)) = (traceCodesA k).val :=
        (halignment k).1
      _ = (traceCodesB k).val := by rw [hCodes]
      _ = Matrix.trace (B ^ ((k : Nat) + 1)) := (halignment k).2.symm
  have hCharpoly : A.charpoly = B.charpoly := hNewton hInitial
  have hAll :=
    (power_trace_characteristic_polynomial_saturation A).2.2 B hCharpoly.symm
      (fun k hk => hInitial ⟨k, hk⟩)
  exact ⟨hCodes, hCharpoly, hAll⟩

#print axioms integer_recovery_structure_recovery_chain

/-- In dimension one, equal characteristic polynomials force equal matrices and
    hence conjugacy; the residual witness therefore starts in dimension two. -/
theorem one_dimensional_charpoly_determines_similarity {K : Type*} [Field K]
    (A B : Matrix (Fin 1) (Fin 1) K) (hcharpoly : A.charpoly = B.charpoly) :
    exists P : (Matrix (Fin 1) (Fin 1) K)ˣ,
      (P : Matrix (Fin 1) (Fin 1) K) * A * (↑P⁻¹ : Matrix (Fin 1) (Fin 1) K) = B := by
  have htrace : Matrix.trace A = Matrix.trace B := by
    rw [Matrix.trace_eq_neg_charpoly_coeff A, Matrix.trace_eq_neg_charpoly_coeff B,
      hcharpoly]
  have hmatrix : A = B := by
    ext i j
    fin_cases i; fin_cases j
    simpa [Matrix.trace, Fin.sum_univ_one] using htrace
  refine ⟨1, ?_⟩
  simp [hmatrix]

#print axioms one_dimensional_charpoly_determines_similarity

/-- The named two-dimensional countermodel is the residual after the spectral layer. -/
theorem power_trace_similarity_residual_witness {K : Type*} [Field K] :
    exists A N : Matrix (Fin 2) (Fin 2) K,
      A.charpoly = N.charpoly ∧
        ¬ (exists P : (Matrix (Fin 2) (Fin 2) K)ˣ,
          (P : Matrix (Fin 2) (Fin 2) K) * A *
              (↑P⁻¹ : Matrix (Fin 2) (Fin 2) K) = N) := by
  have h := power_traces_do_not_determine_similarity (K := K)
  dsimp only at h
  rcases h with ⟨_, hA, hN, _, _, hNot, _⟩
  exact ⟨0, Matrix.single 0 1 1, hA.trans hN.symm, hNot⟩

#print axioms power_trace_similarity_residual_witness

/-- Dropping prime support permits overlapping moduli and breaks the CRT criterion. -/
theorem prime_support_is_necessary_for_chain :
    ¬ (Function.Injective
        (primePowerResidueReading 5 {2, 4} (fun _ => 1)) ↔
      5 ≤ primePowerProduct {2, 4} (fun _ => 1)) := by
  exact prime_support_condition_is_necessary

#print axioms prime_support_is_necessary_for_chain

/-- Without the height capacity, even an empty support collides on `Fin 2`. -/
theorem height_bound_is_necessary_for_chain :
    exists (kappa : Nat -> Nat) (x y : boundedIntegerWindow 2),
      localResiduesAgree 2 ∅ kappa x y ∧ x ≠ y := by
  refine ⟨fun _ => 0, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_, ?_⟩
  · unfold localResiduesAgree
    exact Subsingleton.elim _ _
  · intro h
    have hval := congrArg Fin.val h
    norm_num at hval

#print axioms height_bound_is_necessary_for_chain

/-- At height zero the bounded carrier is empty, so every readout is injective
    vacuously, including for nonempty supports. -/
theorem zero_height_bound_first_layer (S : Finset Nat) (kappa : Nat -> Nat) :
    Function.Injective (primePowerResidueReading 0 S kappa) := by
  intro x
  exact Fin.elim0 x

#print axioms zero_height_bound_first_layer

/-- A field alone does not supply the missing forward Newton bridge in every
    characteristic: over `ZMod 2`, zero and identity have the same first two
    positive traces but distinct characteristic polynomials. -/
theorem newton_bridge_is_necessary :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exists A B : Matrix (Fin 2) (Fin 2) (ZMod 2),
      (forall k : Fin 2,
        Matrix.trace (A ^ ((k : Nat) + 1)) =
          Matrix.trace (B ^ ((k : Nat) + 1))) ∧
        A.charpoly ≠ B.charpoly := by
  let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := 0
  let B : Matrix (Fin 2) (Fin 2) (ZMod 2) := 1
  have hInitial : forall k : Fin 2,
      Matrix.trace (A ^ ((k : Nat) + 1)) =
        Matrix.trace (B ^ ((k : Nat) + 1)) := by
    intro k
    simpa [A, B, Matrix.trace, Fin.sum_univ_two] using
      (ZMod.natCast_self 2).symm
  have hCharpoly : A.charpoly ≠ B.charpoly := by
    rw [show A.charpoly = X ^ 2 by simp [A],
      show B.charpoly = (X - 1) ^ 2 by
        simpa [B] using (Matrix.charpoly_one (n := Fin 2) (R := ZMod 2))]
    intro h
    have hEval := congrArg (fun p : Polynomial (ZMod 2) => p.eval 0) h
    norm_num at hEval
  exact ⟨A, B, hInitial, hCharpoly⟩

#print axioms newton_bridge_is_necessary

/-- Without alignment, unrelated recovered codes carry no information about matrices. -/
theorem trace_alignment_is_necessary :
    exists (A B : Matrix (Fin 2) (Fin 2) ℚ)
      (codesA codesB : boundedIntegerTraceData 2 1),
      codesA = codesB ∧
        (forall k : Fin 2,
          localResiduesAgree 1 ∅ (fun _ => 0) (codesA k) (codesB k)) ∧
        NewtonCharacteristicPolynomialBridge A B ∧ A.charpoly ≠ B.charpoly := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := 0
  let B : Matrix (Fin 2) (Fin 2) ℚ := 1
  let codesA : boundedIntegerTraceData 2 1 := fun _ => ⟨0, by decide⟩
  let codesB : boundedIntegerTraceData 2 1 := fun _ => ⟨0, by decide⟩
  have hBridge : NewtonCharacteristicPolynomialBridge A B := by
    intro hInitial
    have hzero := hInitial ⟨0, by omega⟩
    norm_num [A, B, initialPowerTracesAgree, Matrix.trace, Fin.sum_univ_two] at hzero
  have hCharpoly : A.charpoly ≠ B.charpoly := by
    rw [show A.charpoly = X ^ 2 by simp [A],
      show B.charpoly = (X - 1) ^ 2 by
        simpa [B] using (Matrix.charpoly_one (n := Fin 2) (R := ℚ))]
    intro h
    have hEval := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    norm_num at hEval
  have hResidues : forall k : Fin 2,
      localResiduesAgree 1 ∅ (fun _ => 0) (codesA k) (codesB k) := by
    intro k
    unfold localResiduesAgree
    exact Subsingleton.elim _ _
  exact ⟨A, B, codesA, codesB, rfl, hResidues, hBridge, hCharpoly⟩

#print axioms trace_alignment_is_necessary

/-- The zero-dimensional carrier is an empty trace family and the chain remains valid. -/
theorem zero_dimension_chain :
    (0 : Matrix (Fin 0) (Fin 0) ℚ).charpoly =
        (0 : Matrix (Fin 0) (Fin 0) ℚ).charpoly ∧
      positivePowerTracesAgree
        (0 : Matrix (Fin 0) (Fin 0) ℚ) (0 : Matrix (Fin 0) (Fin 0) ℚ) := by
  let A : Matrix (Fin 0) (Fin 0) ℚ := 0
  let B : Matrix (Fin 0) (Fin 0) ℚ := 0
  have hChain := integer_recovery_structure_recovery_chain
    (N := 0) (S := ∅) (kappa := fun _ => 0) (hS := by simp)
    (hheight := by omega) (A := A) (B := B)
    (hNewton := by intro _; simp [A, B])
    (traceCodesA := fun k => Fin.elim0 k) (traceCodesB := fun k => Fin.elim0 k)
    (hresidues := by intro k; exact Fin.elim0 k)
    (halignment := by intro k; exact Fin.elim0 k)
  exact ⟨hChain.2.1, hChain.2.2⟩

#print axioms zero_dimension_chain

/-- Zero and identity audit all layers: empty support is injective only on the
    singleton window, their characteristic polynomials differ, and they cannot
    be conjugate. The separate zero/nilpotent witness has the same charpoly. -/
theorem zero_and_identity_layer_audit {K : Type*} [Field K] :
    Function.Injective
        (primePowerResidueReading 1 ∅ (fun _ => 0)) ∧
      ¬ (Function.Injective
        (primePowerResidueReading 2 ∅ (fun _ => 0))) ∧
      (0 : Matrix (Fin 2) (Fin 2) K).charpoly = X ^ 2 ∧
      (1 : Matrix (Fin 2) (Fin 2) K).charpoly = (X - 1) ^ 2 ∧
      ¬ (exists P : (Matrix (Fin 2) (Fin 2) K)ˣ,
        (P : Matrix (Fin 2) (Fin 2) K) * (0 : Matrix (Fin 2) (Fin 2) K) *
            (↑P⁻¹ : Matrix (Fin 2) (Fin 2) K) = 1) := by
  refine ⟨(bounded_integer_crt_complete_iff 1 ∅ (fun _ => 0) (by simp)).2 (by
      simp [primePowerProduct]), ?_, by simp, ?_, ?_⟩
  · rw [bounded_integer_crt_complete_iff 2 ∅ (fun _ => 0) (by simp)]
    simp [primePowerProduct]
  · simpa using (Matrix.charpoly_one (n := Fin 2) (R := K))
  · rintro ⟨P, hP⟩
    have : (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by simpa using hP.symm
    exact zero_ne_one this

#print axioms zero_and_identity_layer_audit

end D5.S3.Observer.ProbabilisticClosure.IntegerRecoveryStructureSeparation
