/- GID: D5/S3/Zeros/GRH/New/RealPlace/BesselOrthonormal
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/BesselOrthonormal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.BesselOrthonormal. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/BesselOrthonormal.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bessel.RealMeasures
import D5.S3.Zeros.GRH.New.RealPlace.CellNeighbourhood
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! This file: the coordinates of the full function of a Bessel system are orthonormal. -/

open Matrix MeasureTheory Complex Subgroup ComplexConjugate

/-- The coordinates W_i of the full function of a Bessel system are orthonormal in L²(𝖴∖G₁): the
integral of W_i times the conjugate of W_j is δ_ij. -/
lemma BesselSystem.orthonormal {𝔰 b f} (B : BesselSystem 𝔰 b f) i j :
    ∫ y, B.W .full y i * conj (B.W .full y j) ∂besselQuotMeasure = ite (i = j) 1 0 := by
  obtain ⟨⟨a, h2, _⟩, ⟨⟩⟩ := B.tail, B.tail.isBesselFunction .full
  have {i j} := (h2.eval_piLp i).mul_of_top_left ((a .full).memLp_top.eval_piLp j).star
  simp [Pi.mul_def] at this
  apply (B.irreducible (of _) fun s ↦ .symm ((commute_unitary_iff_star_right_conjugate (by simp)).2
    (ext fun i j ↦ .trans ?_ (identDistrib_orbitMeasure_comp (measurePreserving_conj_bessel
    mem_besselU besselS_le_normalizer_besselU (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem s)))
    (measurePreserving_mul_left _ (embedH s)) ?_ ?_).integral_eq))
    ).elim fun c hc ↦ congr($hc i j).symm.trans (by
      apply_fun trace at hc
      simp_all [← mul_conj', trace, integral_finsetSum, PiLp.norm_sq_eq_of_L2, ← ofReal_inj,
    lintegral_enorm_sq _ (a _).memLp_top, ← integral_complex_ofReal]) <;> generalize ⇑(B.W .full) =
    F at *
  simp (disch := fun_prop) [mul_apply, ↓← integral_const_mul, ← integral_finsetSum, ↓mul_comm]
  repeat simp [smul_def, *, mulVec_eq_sum, mul_conj',
    ← Finset.sum_mul, ← mul_assoc, mul_comm, mul_right_comm _ (F _ i)]
