import GRH.Lib.DiscreteSeries.FlenstedJensen.FlenstedJensenInvariance
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: The coefficient as a smooth function on the group; continuity. -/

open Set Matrix.Norms.L2Operator

attribute [-simp] finsum_eq_sum_of_fintype

variable {n : Type} [Fintype n] {ε} (l : @HCParam n ε)

/-- The restriction of ψ_λ to U(diag ε), as an element of the space of smooth complex-valued
functions on that group. -/
@[simps] noncomputable def HCParam.dsCoeffSmooth : SmoothU ε ℂ := ⟨(l.dsCoeff ·),
  (SmoothPartitionOfUnity.exists_isSubordinate _ isClosedEmbedding_U.2 _ (fun _ ↦ isOpen_analyticAt
  ℂ l.dsCoeff) (subset_iUnion_of_subset () (range_subset_iff.2 analyticAt_dsCoeff))).elim fun f h ↦
  ⟨⟨_,
  (f.contMDiff_finsum_smul fun i _ x ↦ (h i x).restrictScalars.contDiffAt.contMDiffAt).contDiff⟩,
  funext (by simp [↓← finsum_smul, f.sum_eq_one])⟩⟩

@[fun_prop] lemma continuous_dsCoeff {X} [TopologicalSpace X] {f : X → USign ε} :
    Continuous f → Continuous (l.dsCoeff <| f ·) := (SmoothU.continuous l.dsCoeffSmooth).comp
