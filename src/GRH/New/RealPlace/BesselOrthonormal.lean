import GRH.Lib.DiscreteSeries.Bessel.RealMeasures
import GRH.New.RealPlace.CellNeighbourhood
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

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
