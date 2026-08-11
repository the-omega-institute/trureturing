/- GID: D5/S3/QuantumContext/ProjectionValuationObstruction
   generality: G
   mirror-B: D5/B/S3/QuantumContext/ProjectionValuationObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An exact eighteen-ray parity configuration obstructs binary projection valuations. -/

/- Library-search audit trail (2026-08-12):
   * Searches of the pinned mathlib tree for Kochen-Specker, contextuality, and an
     eighteen-ray parity theorem found no existing result to wrap.
   * `Matrix.vecMulVec_mul_vecMulVec`, `Finset.sum_fiberwise_eq_sum_filter`,
     `Finset.sum_bij`, `Finset.card_filter`, `Finset.sum_boole`, `Even`, and `Odd`
     were checked as possible ingredients. The concrete nine equations are small enough
     that `omega` exposes the parity contradiction directly.
   * `Matrix.vecMulVec` and the finite matrix APIs are reused for the exact rank-one
     projectors. All finite certificates use kernel reduction.
-/

import Mathlib

/-!
# A dimension-four projection-valuation certificate

This module verifies one explicit configuration of eighteen rank-one projections in complex
dimension four. It is an instance-level projective obstruction, not a proof of a general
projection-valuation theorem in every dimension at least three.
-/

namespace D5.S3.QuantumContext.ProjectionValuationObstruction

open scoped BigOperators ComplexOrder

/-- Integer representatives of rays in four-dimensional complex space. -/
abbrev KSVector := Fin 4 → ℤ

/-- Complex column vectors in dimension four. -/
abbrev FourVector := Fin 4 → ℂ

/-- Complex matrices in dimension four. -/
abbrev FourMatrix := Matrix (Fin 4) (Fin 4) ℂ

/-- Integer matrices used as exact certificates for the complex projections. -/
abbrev FourIntMatrix := Matrix (Fin 4) (Fin 4) ℤ

/-- The integer dot product used to audit orthogonality before normalization. -/
def dotZ (u v : KSVector) : ℤ := ∑ i, u i * v i

/-- Eighteen distinct integer ray representatives. -/
def ksVectors : Fin 18 → KSVector :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![1, -1, 0, 0],
    ![1, 1, 0, 0],
    ![0, 1, -1, 0],
    ![0, 1, 1, 0],
    ![1, 0, 0, 0],
    ![0, 0, 1, -1],
    ![1, -1, -1, -1],
    ![1, -1, 1, 1],
    ![1, 1, -1, -1],
    ![1, 1, 1, 1],
    ![0, 1, 0, -1],
    ![0, 1, 0, 1],
    ![1, 0, 0, 1],
    ![1, 1, 1, -1],
    ![1, -1, 1, -1],
    ![1, 0, -1, 0]]

/-- Nine orthogonal tetrads. Every ray label occurs in exactly two slots. -/
def contextRay : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3],
    ![0, 4, 5, 6],
    ![7, 8, 9, 3],
    ![7, 2, 10, 11],
    ![1, 12, 13, 6],
    ![4, 8, 14, 15],
    ![12, 16, 17, 11],
    ![13, 9, 17, 15],
    ![5, 16, 14, 10]]

/-- Squared lengths of the chosen integer representatives. -/
def rayNormSq : Fin 18 → ℕ :=
  ![1, 1, 2, 2, 2, 2, 1, 2, 4, 4, 4, 4, 2, 2, 2, 4, 4, 2]

/-- Cast an integer ray representative into complex four-space. -/
def ray (r : Fin 18) : FourVector := fun i ↦ ((ksVectors r i : ℤ) : ℂ)

/-- Four times the normalized outer-product projector. Every norm in the table divides four. -/
def projectionCode (r : Fin 18) : FourIntMatrix := fun i j ↦
  ((4 / rayNormSq r : ℕ) : ℤ) * ksVectors r i * ksVectors r j

/-- Entrywise cast of an integer matrix into complex matrices. -/
noncomputable def castCode (M : FourIntMatrix) : FourMatrix :=
  M.map (Int.castRingHom ℂ)

/-- The normalized rank-one projection carried by a ray label. -/
noncomputable def projection (r : Fin 18) : FourMatrix :=
  (4 : ℂ)⁻¹ • castCode (projectionCode r)

/-- The common factor in `projectionCode` cancels exactly against the outer scaling. -/
theorem projection_scale_exact (r : Fin 18) :
    (4 : ℂ)⁻¹ * (4 / rayNormSq r : ℕ) = (rayNormSq r : ℂ)⁻¹ := by
  fin_cases r <;> norm_num [rayNormSq]

/-- Casting a projector-code entry recovers its exact scaled outer-product entry. -/
theorem projectionCode_cast_apply (r : Fin 18) (i j : Fin 4) :
    ((projectionCode r i j : ℤ) : ℂ) =
      (4 / rayNormSq r : ℕ) * (ksVectors r i : ℂ) * (ksVectors r j : ℂ) := by
  fin_cases r <;> simp [projectionCode, rayNormSq]

/-- Each complex matrix is exactly the normalized outer product of its displayed ray. -/
theorem projection_eq_normalized_outer_product (r : Fin 18) :
    projection r =
      ((rayNormSq r : ℂ)⁻¹) • Matrix.vecMulVec (ray r) (star (ray r)) := by
  ext i j
  unfold projection castCode ray
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.vecMulVec_apply]
  change (4 : ℂ)⁻¹ * ((projectionCode r i j : ℤ) : ℂ) = _
  rw [projectionCode_cast_apply]
  simp only [Pi.star_def, star_intCast]
  calc
    (4 : ℂ)⁻¹ *
        ((4 / rayNormSq r : ℕ) * (ksVectors r i : ℂ) * (ksVectors r j : ℂ)) =
      ((4 : ℂ)⁻¹ * (4 / rayNormSq r : ℕ)) *
        (ksVectors r i : ℂ) * (ksVectors r j : ℂ) := by ring
    _ = (rayNormSq r : ℂ)⁻¹ *
        ((ksVectors r i : ℂ) * (ksVectors r j : ℂ)) := by
          rw [projection_scale_exact]
          ring

/-- The eighteen displayed integer representatives are pairwise distinct. -/
theorem ks_vectors_injective : Function.Injective ksVectors := by
  decide

/-- None of the displayed ray representatives is zero. -/
theorem ks_vectors_nonzero (r : Fin 18) : ksVectors r ≠ 0 := by
  fin_cases r <;> decide

/-- The norm table is the exact integer self-dot-product table. -/
theorem ray_norm_sq_exact (r : Fin 18) :
    dotZ (ksVectors r) (ksVectors r) = rayNormSq r := by
  fin_cases r <;> decide

/-- Each context lists four different ray labels. -/
theorem contextRay_injective (c : Fin 9) : Function.Injective (contextRay c) := by
  fin_cases c <;> decide

/-- Every displayed tetrad is pairwise orthogonal over the integers. -/
theorem ks_contexts_orthogonal (c : Fin 9) (a b : Fin 4) (hab : a ≠ b) :
    dotZ (ksVectors (contextRay c a)) (ksVectors (contextRay c b)) = 0 := by
  revert c a b
  decide

/-- Complex inner products of the cast rays are their integer dot products. -/
theorem ray_inner_eq_dotZ (a b : Fin 18) :
    star (ray a) ⬝ᵥ ray b = (dotZ (ksVectors a) (ksVectors b) : ℂ) := by
  simp [dotZ, ray, dotProduct]

/-- Every ray occurs in exactly two of the thirty-six context slots. -/
theorem ks_incidence_two (r : Fin 18) :
    (Finset.univ.filter
      (fun slot : Fin 9 × Fin 4 ↦ contextRay slot.1 slot.2 = r)).card = 2 := by
  fin_cases r <;> decide

/-- The integer projector codes are pairwise distinct, so no two displayed rays are proportional. -/
theorem projectionCode_injective : Function.Injective projectionCode := by
  decide

/-- Each integer projector code has trace four. -/
theorem projectionCode_trace_four (r : Fin 18) :
    Matrix.trace (projectionCode r) = 4 := by
  fin_cases r <;> decide

/-- Each integer projector code is symmetric. -/
theorem projectionCode_symmetric (r : Fin 18) :
    (projectionCode r).transpose = projectionCode r := by
  fin_cases r <;> decide

/-- The square of each integer projector code is four times itself. -/
theorem projectionCode_idempotent_scaled (r : Fin 18) :
    projectionCode r * projectionCode r = 4 • projectionCode r := by
  fin_cases r <;> decide

/-- Projector codes from different slots in a context have zero product. -/
theorem projectionCode_context_orthogonal (c : Fin 9) (a b : Fin 4) (hab : a ≠ b) :
    projectionCode (contextRay c a) * projectionCode (contextRay c b) = 0 := by
  revert c a b
  decide

/-- The four projector codes in a context sum to four times the identity. -/
theorem projectionCode_context_sum (c : Fin 9) :
    ∑ k, projectionCode (contextRay c k) = 4 • (1 : FourIntMatrix) := by
  fin_cases c <;> decide

/-- Casting integer matrices to complex matrices is injective. -/
theorem castCode_injective : Function.Injective castCode := by
  intro A B h
  ext i j
  apply Int.cast_injective (α := ℂ)
  exact congrFun (congrFun h i) j

/-- Entrywise casting preserves matrix multiplication. -/
theorem castCode_mul (A B : FourIntMatrix) :
    castCode A * castCode B = castCode (A * B) := by
  exact (Matrix.map_mul (f := Int.castRingHom ℂ)).symm

/-- Entrywise casting sends natural scaling to complex scaling. -/
theorem castCode_nsmul (n : ℕ) (A : FourIntMatrix) :
    castCode (n • A) = (n : ℂ) • castCode A := by
  ext i j
  change (((n : ℤ) * A i j : ℤ) : ℂ) = (n : ℂ) * (A i j : ℂ)
  push_cast
  rfl

/-- The eighteen rank-one projections are pairwise distinct. -/
theorem projection_injective : Function.Injective projection := by
  intro a b h
  apply projectionCode_injective
  apply castCode_injective
  have hscaled := congrArg (fun M : FourMatrix ↦ (4 : ℂ) • M) h
  simpa [projection, smul_smul] using hscaled

/-- Every normalized outer product has trace one. -/
theorem projection_trace_one (r : Fin 18) : Matrix.trace (projection r) = 1 := by
  have htrace : Matrix.trace (castCode (projectionCode r)) = (4 : ℂ) := by
    change ∑ i, (((projectionCode r) i i : ℤ) : ℂ) = 4
    exact_mod_cast projectionCode_trace_four r
  simp [projection, htrace]

/-- Every displayed normalized rank-one projection is nonzero. -/
theorem projection_nonzero (r : Fin 18) : projection r ≠ 0 := by
  intro hr
  have htrace := projection_trace_one r
  rw [hr, Matrix.trace_zero] at htrace
  norm_num at htrace

/-- Every displayed normalized rank-one projection is self-adjoint. -/
theorem projection_self_adjoint (r : Fin 18) : star (projection r) = projection r := by
  ext i j
  have hcode := congrFun (congrFun (projectionCode_symmetric r) i) j
  change (projectionCode r) j i = (projectionCode r) i j at hcode
  change star ((4 : ℂ)⁻¹ * ((projectionCode r) j i : ℂ)) =
    (4 : ℂ)⁻¹ * ((projectionCode r) i j : ℂ)
  simpa [star_mul, star_inv₀, mul_comm] using
    congrArg (fun z : ℤ ↦ (4 : ℂ)⁻¹ * (z : ℂ)) hcode

/-- Every displayed normalized rank-one projection is idempotent. -/
theorem projection_idempotent (r : Fin 18) : projection r * projection r = projection r := by
  have hcast : castCode (projectionCode r) * castCode (projectionCode r) =
      (4 : ℂ) • castCode (projectionCode r) := by
    rw [castCode_mul, projectionCode_idempotent_scaled]
    simpa using castCode_nsmul 4 (projectionCode r)
  rw [projection, smul_mul_smul, hcast, smul_smul]
  norm_num

/-- Distinct projectors in any displayed context have zero product. -/
theorem context_projections_orthogonal (c : Fin 9) (a b : Fin 4) (hab : a ≠ b) :
    projection (contextRay c a) * projection (contextRay c b) = 0 := by
  have hcast : castCode (projectionCode (contextRay c a)) *
      castCode (projectionCode (contextRay c b)) = 0 := by
    rw [castCode_mul, projectionCode_context_orthogonal c a b hab]
    simp [castCode]
  simp only [projection]
  rw [smul_mul_smul, hcast, smul_zero]

/-- The four rank-one projections in every displayed context resolve the identity. -/
theorem context_projections_sum_identity (c : Fin 9) :
    ∑ k, projection (contextRay c k) = 1 := by
  have hcast : ∑ k, castCode (projectionCode (contextRay c k)) =
      (4 : ℂ) • (1 : FourMatrix) := by
    calc
      ∑ k, castCode (projectionCode (contextRay c k)) =
          castCode (∑ k, projectionCode (contextRay c k)) := by
            ext i j
            simp [castCode, Matrix.sum_apply]
      _ = castCode (4 • (1 : FourIntMatrix)) := by rw [projectionCode_context_sum c]
      _ = (4 : ℂ) • castCode (1 : FourIntMatrix) := castCode_nsmul 4 _
      _ = (4 : ℂ) • (1 : FourMatrix) := by simp [castCode]
  simp_rw [projection]
  rw [← Finset.smul_sum, hcast, smul_smul]
  norm_num

/-- A binary assignment selecting rays one, four, nine, and eleven. -/
def eightContextValuation : Fin 18 → Fin 2 :=
  ![0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]

/-- Dropping the ninth context leaves a satisfiable, nontrivial constraint system. -/
theorem eight_contexts_satisfiable :
    ∀ c : Fin 9, c.val < 8 →
      ∑ k : Fin 4, (eightContextValuation (contextRay c k)).val = 1 := by
  decide

/-- The nine one-per-context equations contradict the exact double-incidence table. -/
theorem nine_context_parity_contradiction
    (value : Fin 18 → Fin 2)
    (hvalue : ∀ c : Fin 9, ∑ k : Fin 4, (value (contextRay c k)).val = 1) : False := by
  have h0 : (value 0).val + (value 1).val + (value 2).val + (value 3).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 0
  have h1 : (value 0).val + (value 4).val + (value 5).val + (value 6).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 1
  have h2 : (value 7).val + (value 8).val + (value 9).val + (value 3).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 2
  have h3 : (value 7).val + (value 2).val + (value 10).val + (value 11).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 3
  have h4 : (value 1).val + (value 12).val + (value 13).val + (value 6).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 4
  have h5 : (value 4).val + (value 8).val + (value 14).val + (value 15).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 5
  have h6 : (value 12).val + (value 16).val + (value 17).val + (value 11).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 6
  have h7 : (value 13).val + (value 9).val + (value 17).val + (value 15).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 7
  have h8 : (value 5).val + (value 16).val + (value 14).val + (value 10).val = 1 := by
    simpa [contextRay, Fin.sum_univ_succ, add_assoc] using hvalue 8
  omega

/-- The subtype consisting of the eighteen displayed rank-one projections. -/
abbrev ConfigurationProjection := {P : FourMatrix // P ∈ Set.range projection}

/-- A ray label viewed as its actual projection in the finite configuration. -/
noncomputable def labeledProjection (r : Fin 18) : ConfigurationProjection :=
  ⟨projection r, ⟨r, rfl⟩⟩

/-- Distinct labels give distinct elements of the projection configuration. -/
theorem labeledProjection_injective : Function.Injective labeledProjection := by
  intro a b h
  apply projection_injective
  exact congrArg Subtype.val h

/-- No 0/1 valuation on the eighteen projections selects exactly one in every complete context. -/
theorem projection_valuation_obstruction :
    ¬ ∃ value : ConfigurationProjection → Fin 2,
      ∀ c : Fin 9,
        ∑ k : Fin 4, (value (labeledProjection (contextRay c k))).val = 1 := by
  rintro ⟨value, hvalue⟩
  exact nine_context_parity_contradiction (fun r ↦ value (labeledProjection r)) hvalue

end D5.S3.QuantumContext.ProjectionValuationObstruction
