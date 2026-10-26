/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorRankZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank-zero sectors are the scalar identity-field theory, not the zero theory. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorMultiplicityFusion

/-! The rank-zero boundary of the actual sector construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality MvPolynomial
noncomputable section

private theorem emptyIndex (D : LatticeData) (h : D.rank = 0) : IsEmpty (Index D) :=
  ⟨fun i => by have j : Fin 0 := h ▸ i.1; exact Fin.elim0 j⟩

/-- No oscillator variables means the actual scalar algebra, canonically. -/
def rankZeroCoordinates (D : LatticeData) (h : D.rank = 0) : Oscillator D ≃ₐ[ℂ] ℂ := by
  letI := emptyIndex D h
  exact MvPolynomial.isEmptyAlgEquiv ℂ (Index D)

/-- Every actual mixed field in rank zero is the scalar identity field. -/
theorem rankZero_field (D : LatticeData) (h : D.rank = 0) (α β : Charge D)
    (u v : Oscillator D) (n : ℤ) :
    rankZeroCoordinates D h (canonical D α β u n v) =
      if n = -1 then rankZeroCoordinates D h u * rankZeroCoordinates D h v else 0 := by
  letI := emptyIndex D h
  have charge (δ : Charge D) : δ = 0 := by
    ext i
    have j : Fin 0 := h ▸ i
    exact Fin.elim0 j
  rw [charge α, charge β]
  let e := rankZeroCoordinates D h
  have scalar : u = e u • (1 : Oscillator D) := by
    have hr := e.symm_apply_apply u
    simpa [e, rankZeroCoordinates, MvPolynomial.smul_eq_C_mul] using hr.symm
  have field : canonical D 0 0 u n v = if n = -1 then e u • v else 0 := by
    change action D 0 u n v = _
    rw [scalar]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [action_vacuum]
    split_ifs <;> simp
  rw [field]
  split_ifs
  · change e (e u • v) = e u * e v
    simpa only [smul_eq_mul, AlgEquiv.toLinearMap_apply] using e.toLinearMap.map_smul (e u) v
  · exact map_zero e

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
