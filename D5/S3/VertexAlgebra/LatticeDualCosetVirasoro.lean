/- GID: D5/S3/VertexAlgebra/LatticeDualCosetVirasoro
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetVirasoro
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original-omega dual-coset modes satisfy Virasoro with the original rank central charge. -/

import D5.S3.VertexAlgebra.LatticeDualCosetConformalShift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeDualCosetConformal
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeSugawaraVirasoro
open scoped BigOperators VertexOperator
noncomputable section

variable (D : LatticeData) (β : Charge D)

def shiftCurrent (u : Fin D.rank → ℂ) (m : ℤ) : Module.End ℂ (Carrier D) :=
  ∑ i, u i • neutralMode D i m

def halfNorm (u : Fin D.rank → ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ i, ∑ j, u i * (D.G i j : ℂ) * u j

/-- Both inverse contractions for an arbitrary complex dual vector. -/
theorem inverse_dual_contractions
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Fin D.rank → ℂ) (hGu : ∀ i, ∑ j, (D.G i j : ℂ) * u j = (β i : ℂ)) :
    (∀ i, ∑ j, H i j * (β j : ℂ) = u i) ∧
      (∀ j, ∑ i, H i j * (β i : ℂ) = u j) := by
  classical
  have row (i a : Fin D.rank) : ∑ j, H i j * (D.G j a : ℂ) = if i=a then 1 else 0 := by
    simpa [Matrix.mul_apply,gramComplex,Matrix.one_apply] using congrArg (fun M => M i a) hHG
  have col (j a : Fin D.rank) : ∑ i, H i j * (D.G i a : ℂ) = if j=a then 1 else 0 := by
    simpa [Matrix.mul_apply,gramComplex,Matrix.one_apply,D.symmetric a,mul_comm,eq_comm]
      using congrArg (fun M => M a j) hGH
  constructor
  · intro i
    calc
      _ = ∑ a, (∑ j, H i j * (D.G j a : ℂ)) * u a := by
        simp only [← hGu,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp [row]
  · intro j
    calc
      _ = ∑ a, (∑ i, H i j * (D.G i a : ℂ)) * u a := by
        simp only [← hGu,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp [col]

/-- The shift formula is proved for the actual action of the original omega. -/
theorem moduleL_shift_complex
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Fin D.rank → ℂ) (hGu : ∀ i, ∑ j, (D.G i j : ℂ) * u j = (β i : ℂ)) (m : ℤ) :
    moduleL D β H m = sugawaraMode D H m + shiftCurrent D u m +
      (if m=0 then halfNorm D u else 0) • (1 : Module.End ℂ (Carrier D)) := by
  classical
  obtain ⟨hr,hc⟩ := inverse_dual_contractions D β H hHG hGH u hGu
  have first : (∑ i, ∑ j, (H i j * (β j : ℂ)) • neutralMode D i m) = shiftCurrent D u m := by
    simp_rw [← Finset.sum_smul,hr]
    rfl
  have second : (∑ i, ∑ j, (H i j * (β i : ℂ)) • neutralMode D j m) = shiftCurrent D u m := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul,hc]
    rfl
  have scalar : (2 : ℂ)⁻¹ * (∑ i, ∑ j, H i j * ((β i : ℂ)*(β j : ℂ))) = halfNorm D u := by
    unfold halfNorm
    congr 1
    calc
      _ = ∑ j, (∑ i, H i j * (β i : ℂ)) * (β j : ℂ) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp_rw [hc,← hGu,Finset.mul_sum]; rfl
  rw [moduleL_normal]
  simp_rw [normal_current_shift,smul_add,smul_smul,Finset.sum_add_distrib]
  rw [first,second]
  rw [show (∑ i, ∑ j, H i j • ((quadraticSummand D i j)[[m+1]])) =
    (2 : ℂ) • sugawaraMode D H m by rw [sugawaraMode_coefficient_sum,smul_smul]; norm_num]
  by_cases hm : m=0
  · simp only [hm,ite_true,← Finset.sum_smul,smul_add,smul_smul]
    rw [scalar]
    module
  · simp only [hm,ite_false,mul_zero,zero_smul,Finset.sum_const_zero,add_zero,
      smul_add,smul_smul]
    module

/-- The original inverse provides a dual vector without rationality or positivity. -/
theorem inverse_dual_vector (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hGH : gramComplex D * H = 1) :
    ∀ i, ∑ j, (D.G i j : ℂ) * (∑ k, H j k * (β k : ℂ)) = (β i : ℂ) := by
  have h := congrArg (fun M => M *ᵥ (fun k => (β k : ℂ))) hGH
  rw [← Matrix.mulVec_mulVec,Matrix.one_mulVec] at h
  exact fun i => congrFun h i

end
end D5.S3.VertexAlgebra.LatticeDualCosetConformal
