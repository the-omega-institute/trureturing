/- GID: D5/S3/VertexAlgebra/LatticeDualCosetVirasoroLaw
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetVirasoroLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual original conformal vector has rank-central-charge Virasoro modes on every dual-coset module. -/

import D5.S3.VertexAlgebra.LatticeDualCosetVirasoro
import Mathlib.Algebra.Lie.OfAssociative

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
  have h (i : Fin D.rank) : ⁅sugawaraMode D H m,neutralMode D i n⁆ =
      -(n : ℂ) • neutralMode D i (m+n) :=
    sugawaraMode_current_commutator D H hHG hGH i m n
  simp only [shiftCurrent,lie_sum,lie_smul,h,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

private theorem shift_shift_commutator (u : Fin D.rank → ℂ) (m n : ℤ) :
    ⁅shiftCurrent D u m,shiftCurrent D u n⁆ =
      (if m+n=0 then (m : ℂ) * (∑ i,∑ j,u i * (D.G i j : ℂ) * u j) else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  classical
  have h (i j : Fin D.rank) : ⁅neutralMode D i m,neutralMode D j n⁆ =
      (if m+n=0 then (m : ℂ)*(D.G i j : ℂ) else 0) •
        (1 : Module.End ℂ (Carrier D)) := neutralMode_heisenberg D i j m n
  simp only [shiftCurrent,sum_lie_sum,smul_lie,lie_smul,h,smul_smul]
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
    rw [lie_skew,base_shift_commutator D H hHG hGH u n m]
    simp [add_comm]
  have h1 (A : Module.End ℂ (Carrier D)) : ⁅(1 : Module.End ℂ (Carrier D)),A⁆=0 := by
    simp [Ring.lie_def]
  have h2 (A : Module.End ℂ (Carrier D)) : ⁅A,(1 : Module.End ℂ (Carrier D))⁆=0 := by
    simp [Ring.lie_def]
  change ⁅moduleL D β H m,moduleL D β H n⁆ = _
  simp_rw [hl,add_lie,lie_add,smul_lie,lie_smul,h1,h2,smul_zero,zero_add,add_zero]
  rw [hb,base_shift_commutator D H hHG hGH,ho,shift_shift_commutator]
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
