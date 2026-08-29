/- GID: D5/S3/Quantum/Measurements/CompleteContextCollisionConservation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CompleteContextCollisionConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete complementary contexts satisfy operator and scalar collision conservation. -/

import D5.S3.Quantum.Measurements.CompleteContextPurityIdentities

/- Library-search audit trail (2026-08-29):
   * `CompleteContextPurityIdentities.complete_context_purity_identities` is an exact hit for the
     scalar collision clause and is applied directly below, but it does not state the operator
     identity.
   * `CompleteContextTomography.complete_context_tomography` supplies the public trace-separation
     clause used to identify the frame operator without copying its private reconstruction lemmas.
   * Repository and pinned-Mathlib searches found no theorem stating the complete-context
     Kronecker identity. Mathlib's `Matrix.kroneckerMap_apply`, `Matrix.single`, and the canonical
     permutation matrix `(Equiv.prodComm _ _).toPEquiv.toMatrix` supply its representation. -/

open scoped BigOperators ComplexOrder Kronecker Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurements.CompleteContextCollisionConservation

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Tomography.CompleteContextTomography
open D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Measurements.CompleteContextPurityIdentities

set_option maxHeartbeats 1000000 in
-- The entrywise frame calculation expands nested finite matrix sums.
/-- A complete family of pairwise complementary rank-one measurements satisfies the projective
two-design operator identity and, by contraction against a density matrix, the corresponding
collision-probability conservation law. -/
theorem complete_context_collision_conservation
    {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hRecord : forall l, IsRecordMeasurement (context l).projector)
    (hOverlap : forall l k j r,
      Matrix.trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹)
    (rho : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1) :
    (∑ l, ∑ j, (context l).projector j ⊗ₖ (context l).projector j =
      (1 : Matrix (Fin (n + 1) × Fin (n + 1))
        (Fin (n + 1) × Fin (n + 1)) ℂ) +
        (Equiv.prodComm (Fin (n + 1)) (Fin (n + 1))).toPEquiv.toMatrix) ∧
    (∑ l, ∑ j, basisProbability rho (context l) j ^ 2 =
      1 + (Matrix.trace (rho * rho)).re) := by
  classical
  have hTraceResolution
      (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (l : Fin (n + 2)) :
      ∑ j, Matrix.trace (X * (context l).projector j) = Matrix.trace X := by
    calc
      ∑ j, Matrix.trace (X * (context l).projector j) =
          Matrix.trace (X * ∑ j, (context l).projector j) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = Matrix.trace X := by rw [(context l).resolvesIdentity, Matrix.mul_one]
  have hFrame (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
      ∑ l, ∑ j, Matrix.trace (X * (context l).projector j) •
          (context l).projector j =
        X + Matrix.trace X • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    apply sub_eq_zero.mp
    apply (complete_context_tomography context hOverlap).2.1
    intro k r
    rw [Matrix.sub_mul, Matrix.trace_sub]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
    have hContext (l : Fin (n + 2)) :
        (∑ j, Matrix.trace (X * (context l).projector j) *
          Matrix.trace ((context l).projector j * (context k).projector r)) =
        if l = k then Matrix.trace (X * (context k).projector r)
        else Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹ := by
      by_cases hlk : l = k
      · subst l
        simp [hOverlap]
      · rw [if_neg hlk]
        simp_rw [hOverlap, hlk, if_false]
        rw [← Finset.sum_mul, hTraceResolution]
    simp_rw [hContext]
    have hOuter :
        (∑ l : Fin (n + 2),
          if l = k then Matrix.trace (X * (context k).projector r)
          else Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹) =
        Matrix.trace (X * (context k).projector r) + Matrix.trace X := by
      have hDimension : (((n + 1 : Nat) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      calc
        (∑ l : Fin (n + 2),
            if l = k then Matrix.trace (X * (context k).projector r)
            else Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹) =
            ∑ l : Fin (n + 2),
              (Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹ +
                if l = k then
                  Matrix.trace (X * (context k).projector r) -
                    Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹
                else 0) := by
          apply Finset.sum_congr rfl
          intro l _
          by_cases hlk : l = k <;> simp [hlk]
        _ = (∑ _l : Fin (n + 2),
              Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹) +
            ∑ l : Fin (n + 2),
              if l = k then
                Matrix.trace (X * (context k).projector r) -
                  Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹
              else 0 := Finset.sum_add_distrib
        _ = ((n + 2 : Nat) : ℂ) *
              (Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹) +
            (Matrix.trace (X * (context k).projector r) -
              Matrix.trace X * ((n + 1 : Nat) : ℂ)⁻¹) := by simp
        _ = Matrix.trace (X * (context k).projector r) + Matrix.trace X := by
          field_simp [hDimension]
          push_cast
          ring
    rw [hOuter]
    simp [Matrix.add_mul, Matrix.trace_add,
      Matrix.trace_smul, (context k).rankOne r |>.2.2.1]
  refine ⟨?_, (complete_context_purity_identities context hRecord hOverlap rho hrho).2⟩
  ext ⟨a, b⟩ ⟨c, d⟩
  have hSingleTrace
      (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
      Matrix.trace (Matrix.single d b 1 * P) = P b d := by
    calc
      Matrix.trace (Matrix.single d b 1 * P) =
          ∑ x, ∑ y, if d = x ∧ b = y then P y x else 0 := by
        simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply]
      _ = ∑ x, if d = x then P b x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hdx : d = x
        · subst x
          simp
        · simp [hdx]
      _ = P b d := by simp
  have hSingleDiagonal :
      Matrix.trace (Matrix.single d b (1 : ℂ)) = if b = d then 1 else 0 := by
    calc
      Matrix.trace (Matrix.single d b 1) =
          Matrix.trace (Matrix.single d b 1 * 1) := by rw [Matrix.mul_one]
      _ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) b d := hSingleTrace 1
      _ = if b = d then 1 else 0 := by simp [Matrix.one_apply]
  have hEntry := congrArg
    (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M a c)
    (hFrame (Matrix.single d b 1))
  have hEntryNormalized :
      (∑ l, ∑ j,
        (context l).projector j b d * (context l).projector j a c) =
        (if a = d ∧ b = c then 1 else 0) +
          (if a = c ∧ b = d then 1 else 0) := by
    calc
      (∑ l, ∑ j,
          (context l).projector j b d * (context l).projector j a c) =
          (Matrix.single d b (1 : ℂ) +
            Matrix.trace (Matrix.single d b (1 : ℂ)) •
              (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) a c := by
        simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          hSingleTrace] using hEntry
      _ = (if a = d ∧ b = c then 1 else 0) +
          (if a = c ∧ b = d then 1 else 0) := by
        rw [Matrix.add_apply, Matrix.single_apply, hSingleDiagonal,
          Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
        by_cases had : a = d <;> by_cases hbc : b = c <;>
          by_cases hac : a = c <;> by_cases hbd : b = d <;> simp_all <;> aesop
  have hOperatorEntry :
      (∑ l, ∑ j,
        (context l).projector j a c * (context l).projector j b d) =
        (if a = c ∧ b = d then 1 else 0) +
          (if a = d ∧ b = c then 1 else 0) := by
    calc
      (∑ l, ∑ j,
          (context l).projector j a c * (context l).projector j b d) =
          ∑ l, ∑ j,
            (context l).projector j b d * (context l).projector j a c := by
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
      _ = (if a = d ∧ b = c then 1 else 0) +
          (if a = c ∧ b = d then 1 else 0) := hEntryNormalized
      _ = (if a = c ∧ b = d then 1 else 0) +
          (if a = d ∧ b = c then 1 else 0) := add_comm _ _
  have hSwapMatrixEntry :
      ((Equiv.prodComm (Fin (n + 1)) (Fin (n + 1))).toPEquiv.toMatrix :
          Matrix (Fin (n + 1) × Fin (n + 1))
            (Fin (n + 1) × Fin (n + 1)) ℂ) (a, b) (c, d) =
        if a = d ∧ b = c then 1 else 0 := by
    rw [PEquiv.toMatrix_apply]
    by_cases had : a = d <;> by_cases hbc : b = c <;>
      simp_all [Equiv.toPEquiv_apply]
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.add_apply,
    Matrix.one_apply, Prod.mk.injEq, hSwapMatrixEntry]
  exact hOperatorEntry

/-- The complete-context and density hypotheses are jointly satisfiable. -/
example : ∃ (context : Fin 2 -> RankOneContext 1)
    (rho : Matrix (Fin 1) (Fin 1) ℂ),
    (∀ l, IsRecordMeasurement (context l).projector) ∧
      (∀ l k j r,
        Matrix.trace ((context l).projector j * (context k).projector r) =
          if l = k then (if j = r then 1 else 0) else (1 : ℂ)⁻¹) ∧
      rho.PosSemidef ∧ Matrix.trace rho = 1 := by
  let B : RankOneContext 1 :=
    { projector := fun _ => 1
      rankOne := by
        intro j
        refine ⟨by simp, by simp, by simp, ?_⟩
        intro X
        ext i k
        fin_cases i
        fin_cases k
        simp [Matrix.trace, Matrix.mul_apply]
      resolvesIdentity := by simp }
  have hB : IsRecordMeasurement B.projector := by
    refine ⟨?_, ?_, ?_, B.resolvesIdentity⟩
    · intro j
      simpa only [Matrix.star_eq_conjTranspose] using (B.rankOne j).1
    · intro j
      exact (B.rankOne j).2.1
    · intro j k hjk
      exact (hjk (Subsingleton.elim j k)).elim
  refine ⟨fun _ => B, 1, fun _ => hB, ?_, Matrix.PosSemidef.one, ?_⟩
  · intro l k j r
    have hjr : j = r := Subsingleton.elim _ _
    subst r
    simp [B]
  · simp [Matrix.trace]

#print axioms complete_context_collision_conservation

end D5.S3.Quantum.Measurements.CompleteContextCollisionConservation
