/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstNilpotence
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstNilpotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Creation cyclicity propagates the actual critical BRST square from the ghost vacuum to every algebraic tensor state. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare
import D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance
import D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  BcGhostFockSupport
open scoped TensorProduct

noncomputable section

private theorem square_b_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (mode : ℤ) :
    (Q D H * Q D H) * B D mode - B D mode * (Q D H * Q D H) = 0 := by
  calc
    _ = Q D H * (Q D H * B D mode + B D mode * Q D H) -
        (Q D H * B D mode + B D mode * Q D H) * Q D H := by
      simp only [mul_add, add_mul, mul_assoc]
      abel
    _ = Q D H * (M D H mode + G D mode) -
        (M D H mode + G D mode) * Q D H := by
      rw [ward_identity]
    _ = 0 := by
      simpa [hcritical] using
        LatticeBcGhostBrstTotalCovariance.total_covariance D H hHG hGH mode

private theorem tensor_kernel_stable (D : LatticeData)
    (square : Module.End ℂ (State D)) (ghostMode : Module.End ℂ (Fock ℂ))
    (hcommutes : square * TensorProduct.map LinearMap.id ghostMode -
      TensorProduct.map LinearMap.id ghostMode * square = 0)
    (matter : Carrier D) (ghost : Fock ℂ)
    (hghost : square (matter ⊗ₜ[ℂ] ghost) = 0) :
    square (matter ⊗ₜ[ℂ] ghostMode ghost) = 0 := by
  have hevaluated := congrArg
    (fun operator : Module.End ℂ (State D) => operator (matter ⊗ₜ[ℂ] ghost)) hcommutes
  change square (TensorProduct.map LinearMap.id ghostMode (matter ⊗ₜ[ℂ] ghost)) -
    TensorProduct.map LinearMap.id ghostMode (square (matter ⊗ₜ[ℂ] ghost)) = 0 at hevaluated
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, hghost, map_zero, sub_zero]
    using hevaluated

private theorem square_tmul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (matter : Carrier D) (ghost : Fock ℂ) :
    (Q D H * Q D H) (matter ⊗ₜ[ℂ] ghost) = 0 := by
  let action : Fock ℂ →ₗ[ℂ] State D :=
    (Q D H * Q D H).comp ((TensorProduct.mk ℂ (Carrier D) (Fock ℂ)) matter)
  let kernel : Submodule ℂ (Fock ℂ) := LinearMap.ker action
  have hvacuum : vacuum ∈ kernel := by
    change (Q D H * Q D H) (matter ⊗ₜ[ℂ] vacuum) = 0
    exact LatticeBcGhostBrstVacuumSquare.vacuum_square D H hHG hGH matter
  have hb : ∀ mode : ℤ, mode ≤ -2 → ∀ state ∈ kernel, b mode state ∈ kernel := by
    intro mode _hmode state hstate
    change (Q D H * Q D H) (matter ⊗ₜ[ℂ] state) = 0 at hstate
    change (Q D H * Q D H) (matter ⊗ₜ[ℂ] b mode state) = 0
    exact tensor_kernel_stable D (Q D H * Q D H) (b (K := ℂ) mode)
      (by simpa only [B] using square_b_commutator D H hHG hGH hcritical mode)
      matter state hstate
  have hc : ∀ mode : ℤ, mode ≤ 1 → ∀ state ∈ kernel, c mode state ∈ kernel := by
    intro mode _hmode state hstate
    change (Q D H * Q D H) (matter ⊗ₜ[ℂ] state) = 0 at hstate
    change (Q D H * Q D H) (matter ⊗ₜ[ℂ] c mode state) = 0
    exact tensor_kernel_stable D (Q D H * Q D H) (c (K := ℂ) mode)
      (by simpa only [C] using
        LatticeBcGhostBrstSquareCCommutator.square_c_commutator D H mode)
      matter state hstate
  have htop : kernel = ⊤ := creation_cyclic kernel hvacuum hb hc
  have hmember : ghost ∈ kernel := by
    rw [htop]
    exact Submodule.mem_top
  change (Q D H * Q D H) (matter ⊗ₜ[ℂ] ghost) = 0 at hmember
  exact hmember

theorem nilpotent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : Q D H * Q D H = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro matter
  apply LinearMap.ext
  intro ghost
  change (Q D H * Q D H) (matter ⊗ₜ[ℂ] ghost) = 0
  exact square_tmul D H hHG hGH hcritical matter ghost

#print axioms nilpotent

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
