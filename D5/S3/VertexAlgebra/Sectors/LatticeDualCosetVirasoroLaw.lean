/- GID: D5/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoroLaw
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeDualCosetVirasoroLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual original conformal vector has rank-central-charge Virasoro modes on every dual-coset module. -/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetVirasoro

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeDualCosetConformal
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeSugawaraVirasoro
open scoped BigOperators
noncomputable section

variable (D : LatticeData)

private theorem base_shift_commutator
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (u : Fin D.rank → ℂ) (m n : ℤ) :
    ⁅sugawaraMode D H m,shiftCurrent D u n⁆ = -(n : ℂ) • shiftCurrent D u (m+n) := by
  classical
  change sugawaraMode D H m * shiftCurrent D u n -
    shiftCurrent D u n * sugawaraMode D H m = _
  simp only [shiftCurrent,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,
    smul_mul_assoc,← Finset.sum_sub_distrib,← smul_sub]
  simp_rw [sugawaraMode_current_commutator D H hHG hGH,smul_smul]
  simp only [Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

private theorem shift_shift_commutator (u : Fin D.rank → ℂ) (m n : ℤ) :
    ⁅shiftCurrent D u m,shiftCurrent D u n⁆ =
      (if m+n=0 then (m : ℂ) * (∑ i,∑ j,u i * (D.G i j : ℂ) * u j) else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  classical
  have product (m n : ℤ) : shiftCurrent D u m * shiftCurrent D u n =
      ∑ i,∑ j,(u i*u j) • (neutralMode D i m * neutralMode D j n) := by
    simp only [shiftCurrent,Finset.sum_mul,Finset.mul_sum,
      smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (u j) (u i)]
  have reverse : shiftCurrent D u n * shiftCurrent D u m =
      ∑ i,∑ j,(u i*u j) • (neutralMode D j n * neutralMode D i m) := by
    rw [product,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (u j) (u i)]
  change shiftCurrent D u m * shiftCurrent D u n -
    shiftCurrent D u n * shiftCurrent D u m = _
  rw [product,reverse]
  simp only [← Finset.sum_sub_distrib,← smul_sub]
  simp_rw [neutralMode_heisenberg D,smul_smul]
  by_cases hmn : m+n=0
  · simp only [hmn,ite_true,← Finset.sum_smul]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [hmn]

/-- Universal Virasoro for actual original-omega modes, without positivity or rationality. -/
theorem moduleL_virasoro (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1) (m n : ℤ) :
    moduleL D β H m * moduleL D β H n - moduleL D β H n * moduleL D β H m =
      ((m-n : ℤ) : ℂ) • moduleL D β H (m+n) +
        (if m+n=0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D)) := by
  classical
  let u : Fin D.rank → ℂ := fun i => ∑ j,H i j*(β j : ℂ)
  have hGu : ∀ i,∑ j,(D.G i j : ℂ)*u j=(β i : ℂ) := inverse_dual_vector D β H hGH
  have hl := moduleL_shift_complex D β H hHG hGH u hGu
  have hb : ⁅sugawaraMode D H m,sugawaraMode D H n⁆ =
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n) +
        (if m+n=0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D)) := sugawaraMode_virasoro D H hHG hGH m n
  have ho : ⁅shiftCurrent D u m,sugawaraMode D H n⁆ =
      (m : ℂ) • shiftCurrent D u (m+n) := by
    have h := base_shift_commutator D H hHG hGH u n m
    simp only [Ring.lie_def] at h ⊢
    rw [add_comm n m] at h
    linear_combination (norm := module) -h
  change ⁅moduleL D β H m,moduleL D β H n⁆ = _
  rw [hl m,hl n,hl (m+n)]
  have expansion :
      ⁅sugawaraMode D H m + shiftCurrent D u m +
          (if m=0 then halfNorm D u else 0) • (1 : Module.End ℂ (Carrier D)),
        sugawaraMode D H n + shiftCurrent D u n +
          (if n=0 then halfNorm D u else 0) • (1 : Module.End ℂ (Carrier D))⁆ =
      ⁅sugawaraMode D H m,sugawaraMode D H n⁆ +
        ⁅sugawaraMode D H m,shiftCurrent D u n⁆ +
        ⁅shiftCurrent D u m,sugawaraMode D H n⁆ +
        ⁅shiftCurrent D u m,shiftCurrent D u n⁆ := by
    simp only [Ring.lie_def,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      mul_one,one_mul,smul_smul]
    module
  rw [expansion,hb,base_shift_commutator D H hHG hGH,ho,shift_shift_commutator]
  have hk : (∑ i,∑ j,u i*(D.G i j : ℂ)*u j) = 2*halfNorm D u := by
    unfold halfNorm
    ring
  rw [hk]
  by_cases hmn : m+n=0
  · have hn : (n : ℂ)=-(m : ℂ) := by
      have : n = -m := by omega
      simp [this]
    simp only [hmn,ite_true,Int.cast_sub,hn]
    module
  · simp only [hmn,ite_false,zero_smul,add_zero,Int.cast_sub]
    module

end
end D5.S3.VertexAlgebra.LatticeDualCosetConformal
