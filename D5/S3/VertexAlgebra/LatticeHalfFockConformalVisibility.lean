/- GID: D5/S3/VertexAlgebra/LatticeHalfFockConformalVisibility
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockConformalVisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Public exact compatibility suppliers for the original private tensor and trace identities. -/

import D5.S3.VertexAlgebra.LatticeHalfFockTensorFields
import D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeHalfFockConformalVisibility

noncomputable section

open D5.S3.VertexAlgebra.LatticeHalfFock
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open scoped TensorProduct

theorem tensorEnd_mul (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]
    (A B : Module.End ℂ (Oscillator D)) :
    tensorEnd D T (A * B) = tensorEnd D T A * tensorEnd D T B := by
  apply TensorProduct.ext'
  intro polynomial ground
  simp [tensorEnd, Module.End.mul_apply]

theorem tensorPair_eq (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]
    (i l : Fin D.rank) (j k : ℤ) :
    tensorPair D T i l j k =
      if j < 0 then tensorCurrent D T i j * tensorCurrent D T l k
      else tensorCurrent D T l k * tensorCurrent D T i j := by
  unfold tensorPair normalPair
  split_ifs
  · exact tensorEnd_mul D T _ _
  · exact tensorEnd_mul D T _ _

theorem tensorPair_finite (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]
    (i l : Fin D.rank) (m : ℤ) (v : Oscillator D ⊗[ℂ] T) :
    Function.HasFiniteSupport (fun j : ℤ => tensorPair D T i l j (m-j-1) v) := by
  obtain ⟨R, hR⟩ := tensor_current_truncation D T v
  exact (Set.finite_Icc _ _).subset (tensorPair_support_of_bound D T i l m v R hR)

theorem inverse_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeHalfFock.gramComplex D = 1) :
    ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l * (D.G i l : ℂ) = (D.rank : ℂ) := by
  have row (i : Fin D.rank) : ∑ l, H i l * (D.G i l : ℂ) = 1 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i i) hHG
    simpa [Matrix.mul_apply, LatticeHalfFock.gramComplex, D.symmetric i] using h
  simp_rw [row]
  simp

end
end D5.S3.VertexAlgebra.LatticeHalfFockConformalVisibility
