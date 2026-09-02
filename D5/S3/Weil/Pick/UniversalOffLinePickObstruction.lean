/- GID: D5/S3/Weil/Pick/UniversalOffLinePickObstruction
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/UniversalOffLinePickObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Right-side zero images give a fixed determinant-minus-one Pick matrix. -/

import D5.S3.Weil.Pick.MinimalRelationalVisibility

/-!
# Universal off-line Pick obstruction

The off-line disk point is constructed from its real displacement and ordinate.
The existing minimal relational-visibility theorem then supplies the canonical
two-point Pick calculation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix
open scoped ComplexConjugate ComplexOrder

namespace D5.S3.Weil.Pick.UniversalOffLinePickObstruction

open D5.S3.Weil.Pick.MinimalRelationalVisibility

/-- A zero to the right of the critical midline maps inside the disk. At a
unit Schur contact, its two-point Pick matrix and determinant are fixed, with
the ordinate `gamma` bound but absent from both resulting constants. -/
theorem universal_off_line_pick_obstruction
    (schur : Complex -> Complex) (sigma gamma : Real)
    (hright : (1 : Real) / 2 < sigma)
    (hzero : schur 0 = 0)
    (hcontact :
      schur (1 - ((sigma : Complex) + Complex.I * (gamma : Complex))⁻¹) = 1) :
    let rho : Complex := (sigma : Complex) + Complex.I * (gamma : Complex)
    let zrho : Complex := 1 - rho⁻¹
    let pickKernel : Complex -> Complex -> Complex := fun z w =>
      (1 - schur z * conj (schur w)) / (1 - z * conj w)
    let points : Fin 2 -> Complex := ![0, zrho]
    let relation : Matrix (Fin 2) (Fin 2) Complex := fun i j =>
      pickKernel (points i) (points j)
    norm zrho < 1 /\
      relation = !![(1 : Complex), 1; 1, 0] /\
      Matrix.det relation = -1 := by
  dsimp only
  let rho : Complex := (sigma : Complex) + Complex.I * (gamma : Complex)
  have hsigma_pos : 0 < sigma := by linarith
  have hrho_ne : rho ≠ 0 := by
    intro hrho
    have hre : sigma = 0 := by
      simpa [rho] using congrArg Complex.re hrho
    exact (ne_of_gt hsigma_pos) hre
  have hsquares : norm (rho - 1) ^ 2 < norm rho ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp [rho]
    nlinarith
  have hnorm_lt : norm (rho - 1) < norm rho :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  have hzrho : 1 - rho⁻¹ = (rho - 1) / rho := by
    field_simp [hrho_ne]
  have hinside : norm (1 - rho⁻¹) < 1 := by
    rw [hzrho, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hrho_ne)).mpr hnorm_lt
  let point : Complex.UnitDisc := Complex.UnitDisc.mk (1 - rho⁻¹) hinside
  have hminimal := minimal_relational_visibility schur point hzero (by
    simpa [point, rho] using hcontact)
  dsimp only at hminimal
  have hmatrix := hminimal.1
  have hdet := hminimal.2.2.1
  refine ⟨by simpa only [rho] using hinside, ?_, ?_⟩
  · simpa only [point, rho, Complex.UnitDisc.coe_mk] using hmatrix
  · simpa only [point, rho, Complex.UnitDisc.coe_mk] using hdet

#print axioms universal_off_line_pick_obstruction

end D5.S3.Weil.Pick.UniversalOffLinePickObstruction
