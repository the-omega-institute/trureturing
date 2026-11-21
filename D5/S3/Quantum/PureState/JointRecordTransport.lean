/- GID: D5/S3/Quantum/PureState/JointRecordTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/JointRecordTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Occupied-subspace transport preserves the full set of finite POVM successes. -/

import D5.S3.Quantum.PureState.JointRecordDecoding

/-! Transport of all finite joint POVM success probabilities along the occupied subspace. -/

namespace JointRecordDecoding

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
open D5.S3.Quantum.PureState.PureStateHandshake

variable {X A B : Type*} [Fintype X] [Nonempty X]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private theorem complement_posSemidef {P : Matrix A A ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) : (1 - P).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  have heq : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hP.eq, Matrix.sub_mul, one_mul,
      Matrix.mul_sub, mul_one, hPP, sub_self, sub_zero]
  rwa [heq] at h

private theorem success_set_compress (p : X → ℝ) (rho : X → DensityState A)
    (sig : X → DensityState B) (V : Matrix B A ℂ)
    (hres : (1 - Vᴴ * V).PosSemidef)
    (hsupp : ∀ j, (Vᴴ * V) * CStarMatrix.ofMatrix.symm (rho j).1 =
      CStarMatrix.ofMatrix.symm (rho j).1)
    (hmap : ∀ j, CStarMatrix.ofMatrix.symm (sig j).1 =
      V * CStarMatrix.ofMatrix.symm (rho j).1 * Vᴴ) :
    successProbabilitySet p sig ⊆ successProbabilitySet p rho := by
  classical
  let j₀ := Classical.choice (inferInstance : Nonempty X)
  rintro a ⟨M, hM, hsum, rfl⟩
  let N : X → Matrix A A ℂ := fun j => Vᴴ * M j * V + if j = j₀ then 1 - Vᴴ * V else 0
  refine ⟨N, ?_, ?_, ?_⟩
  · intro j
    refine ((hM j).conjTranspose_mul_mul_same V).add ?_
    split_ifs
    · exact hres
    · exact Matrix.PosSemidef.zero
  · simp only [N, Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum,
      Matrix.mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel
  · unfold successProbability
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    apply congrArg Complex.re
    have hz : (1 - Vᴴ * V) * CStarMatrix.ofMatrix.symm (rho j).1 = 0 := by
      rw [Matrix.sub_mul, one_mul, hsupp j, sub_self]
    have hbase : trace (Vᴴ * M j * V * CStarMatrix.ofMatrix.symm (rho j).1) =
        trace (M j * CStarMatrix.ofMatrix.symm (sig j).1) := by
      rw [hmap j]
      simp only [Matrix.mul_assoc]
      rw [trace_mul_comm Vᴴ]
      simp only [Matrix.mul_assoc]
    dsimp only [N]
    rw [Matrix.add_mul, trace_add, hbase]
    split_ifs <;> simp [hz]

/-- A partial isometry transporting the occupied state subspace preserves the genuine success set.
The residual projector in each direction is assigned to a fixed label. -/
theorem success_set_partialIsometry (p : X → ℝ) (rho : X → DensityState A)
    (sig : X → DensityState B) (V : Matrix B A ℂ)
    (hV : V * (Vᴴ * V) = V)
    (hsupp : ∀ j, (Vᴴ * V) * CStarMatrix.ofMatrix.symm (rho j).1 =
      CStarMatrix.ofMatrix.symm (rho j).1)
    (hmap : ∀ j, CStarMatrix.ofMatrix.symm (sig j).1 =
      V * CStarMatrix.ofMatrix.symm (rho j).1 * Vᴴ) :
    successProbabilitySet p sig = successProbabilitySet p rho := by
  have hstar : (Vᴴ * V) * Vᴴ = Vᴴ := by
    simpa [conjTranspose_mul] using congrArg Matrix.conjTranspose hV
  have hP : (Vᴴ * V) * (Vᴴ * V) = Vᴴ * V := by
    rw [Matrix.mul_assoc Vᴴ V, hV]
  have hQ : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc V Vᴴ, ← Matrix.mul_assoc Vᴴ V, hstar]
  have hresP := complement_posSemidef (isHermitian_conjTranspose_mul_self V) hP
  have hresQ := complement_posSemidef (isHermitian_mul_conjTranspose_self V) hQ
  refine Set.Subset.antisymm (success_set_compress p rho sig V hresP hsupp hmap) ?_
  apply success_set_compress p sig rho Vᴴ
  · simpa only [conjTranspose_conjTranspose] using hresQ
  · intro j
    rw [conjTranspose_conjTranspose, hmap j]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc V Vᴴ V, hV]
  · intro j
    let R := CStarMatrix.ofMatrix.symm (rho j).1
    have hR : R.IsHermitian :=
      (D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef (rho j)).isHermitian
    have hleft : (Vᴴ * V) * R = R := hsupp j
    have hright : R * (Vᴴ * V) = R := by
      simpa [conjTranspose_mul, hR.eq] using congrArg Matrix.conjTranspose hleft
    rw [conjTranspose_conjTranspose, hmap j]
    change R = Vᴴ * (V * R * Vᴴ) * V
    calc
      R = ((Vᴴ * V) * R) * (Vᴴ * V) := by rw [hleft, hright]
      _ = _ := by simp only [Matrix.mul_assoc]

private theorem sandwich_rankOne (V : Matrix B A ℂ) (v : A → ℂ) :
    V * rankOneDensity v * Vᴴ = rankOneDensity (V *ᵥ v) := by
  rw [rankOneDensity, rankOneDensity, mul_vecMulVec, vecMulVec_mul,
    ← star_mulVec]

/-- A rectangular partial isometry between the occupied pure-state subspaces preserves
the full set of finite POVM success values. -/
theorem success_set_pure_partialIsometry (p : X → ℝ) (v : X → A → ℂ)
    (w : X → B → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hw : ∀ j, star (w j) ⬝ᵥ w j = 1) (V : Matrix B A ℂ)
    (hV : V * (Vᴴ * V) = V)
    (hsupp : ∀ j, (Vᴴ * V) *ᵥ v j = v j)
    (hmap : ∀ j, V *ᵥ v j = w j) :
    successProbabilitySet p (fun j => pureState (w j) (hw j)) =
      successProbabilitySet p (fun j => pureState (v j) (hv j)) := by
  apply success_set_partialIsometry p _ _ V hV
  · intro j
    rw [pureState_matrix, rankOneDensity, mul_vecMulVec, hsupp j]
  · intro j
    rw [pureState_matrix, pureState_matrix, sandwich_rankOne, hmap j]

/-- A rectangular partial isometry between the occupied pure-state subspaces preserves the optimum
over all joint POVMs. -/
theorem pGuess_pure_partialIsometry (p : X → ℝ) (v : X → A → ℂ)
    (w : X → B → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hw : ∀ j, star (w j) ⬝ᵥ w j = 1) (V : Matrix B A ℂ)
    (hV : V * (Vᴴ * V) = V)
    (hsupp : ∀ j, (Vᴴ * V) *ᵥ v j = v j)
    (hmap : ∀ j, V *ᵥ v j = w j) :
    pGuess p (fun j => pureState (w j) (hw j)) =
      pGuess p (fun j => pureState (v j) (hv j)) :=
  congrArg sSup (success_set_pure_partialIsometry p v w hv hw V hV hsupp hmap)

end

end JointRecordDecoding
