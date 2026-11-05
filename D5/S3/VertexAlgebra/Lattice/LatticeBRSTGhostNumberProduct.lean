/-
SOURCE-ONLY consumer of the fixed original Field/Product/P0/integer drafts.
No native elaboration, kernel check, or official acceptance is claimed; native
adaptation remains pending. No live repair or peer result is used.

The original tensor State, Y, tensorNumber, cycles, boundaries, full Cohomology,
product, Pg, Pi, grade and Delta are unchanged. The charge-Q commutator is
already supplied by LatticeMatterGhostDegree.tensorNumber_Q and is NOT reproved
or wrapped. The integer supplier consumes it in homogeneous_cycle_lift.

The finite tensor convolution is the supplied original one. Bakalov--Kac's
lattice construction, Scott Carnahan / vertexAlg's field coefficient calculus,
Kalle Kytölä's Sugawara architecture, and the repository/Mathlib authors retain
their attribution as in the fixed suppliers. No literature novelty is claimed.
This gives product degree zero on the existing full quotient, and does not
claim integer parity/sign compatibility, bracket transfer, BV axioms, or the
full Moonshine/VOA/CFT/anomaly/fusion/string/AdS-CFT goal. That goal stays active.
-/

import D5.S3.Quantum.Fermionic.BcGhostStateFieldGhostNumber
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTGhostNumberGrading
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTGhostNumberProduct

open LatticeGeneratingFieldLocality (LatticeData Carrier)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State)
open LatticeMatterGhostDegree (tensorNumber)
open LatticeMatterGhostStateField (Y)
open LatticeBRSTCohomologyField (Cohomology classOf cycleMode product)
open LatticeBRSTGhostNumberGrading (Pg grade)
open D5.S3.Quantum.Fermionic
open private term term_finite Y_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

noncomputable section

private theorem term_number (D : LatticeData) (a : State D) (n k : ℤ) :
    tensorNumber D * term D n k a - term D n k a * tensorNumber D =
      term D n k (tensorNumber D a) := by
  induction a using TensorProduct.inductionOn with
  | tmul u g =>
    apply TensorProduct.ext'
    intro v w
    have h := LinearMap.congr_fun
      (BcGhostStateFieldGhostNumber.stateField_ghostNumber g (n - 1 - k)) w
    simpa only [tensorNumber, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
      term, TensorProduct.map₂_apply_tmul, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.tmul_sub] using
      congrArg (fun b => ((LatticeAllStateField.Y D u)[[k]]) v ⊗ₜ[ℂ] b) h
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, mul_add, add_mul]
    rw [show ∀ A B C E : Module.End ℂ (State D),
      (A + B) - (C + E) = (A - C) + (B - E) by intros; abel, ha, hb]

/-- Actual ghost-number derivation on all original mixed tensor fields. The
finite families are taken separately at x and tensorNumber x. -/
theorem stateField_ghostNumber (D : LatticeData) (a : State D) (n : ℤ) :
    tensorNumber D * ((Y D a)[[n]]) - ((Y D a)[[n]]) * tensorNumber D =
      ((Y D (tensorNumber D a))[[n]]) := by
  apply LinearMap.ext
  intro x
  change tensorNumber D (((Y D a)[[n]]) x) -
      ((Y D a)[[n]]) (tensorNumber D x) = ((Y D (tensorNumber D a))[[n]]) x
  simp only [Y_modes]
  rw [map_finsum (tensorNumber D) (term_finite D a x n),
    ← finsum_sub_distrib ((term_finite D a x n).fun_comp (map_zero (tensorNumber D)))
      (term_finite D a (tensorNumber D x) n)]
  exact finsum_congr (fun k => LinearMap.congr_fun (term_number D a n k) x)

/-- Integer degree addition is derived from the actual mode identity; the
mode index n and both integer eigenvalues are unrestricted. -/
private theorem mode_degree (D : LatticeData) (k l n : ℤ) (a b : State D)
    (ha : tensorNumber D a = (k : ℂ) • a)
    (hb : tensorNumber D b = (l : ℂ) • b) :
    tensorNumber D (((Y D a)[[n]]) b) =
      ((k + l : ℤ) : ℂ) • (((Y D a)[[n]]) b) := by
  have h := LinearMap.congr_fun (stateField_ghostNumber D a n) b
  change tensorNumber D (((Y D a)[[n]]) b) - ((Y D a)[[n]]) (tensorNumber D b) =
    ((Y D (tensorNumber D a))[[n]]) b at h
  rw [ha, hb] at h
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply] at h
  calc
    _ = (k : ℂ) • (((Y D a)[[n]]) b) + (l : ℂ) • (((Y D a)[[n]]) b) :=
      sub_eq_iff_eq_add.mp h
    _ = _ := by rw [Int.cast_add, add_smul]

/-- Degree ZERO of the EXISTING full BRST quotient product. Both classes are
arbitrary elements of the original quotient with only their stated homogeneous
membership. Actual homogeneous cycles are obtained from the fixed integer
supplier; their actual -1 mode represents the supplied product. -/
theorem product_mem_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k l : ℤ) (a b : Cohomology D H h26 hHG hGH)
    (ha : a ∈ grade D H h26 hHG hGH k)
    (hb : b ∈ grade D H h26 hHG hGH l) :
    product D H h26 hHG hGH a b ∈ grade D H h26 hHG hGH (k + l) := by
  obtain ⟨x, hx, hNx⟩ := LatticeBRSTGhostNumberGrading.homogeneous_cycle_lift
    D H h26 hHG hGH k a ((LatticeBRSTGhostNumberGrading.mem_grade
      D H h26 hHG hGH k a).mp ha)
  obtain ⟨y, hy, hNy⟩ := LatticeBRSTGhostNumberGrading.homogeneous_cycle_lift
    D H h26 hHG hGH l b ((LatticeBRSTGhostNumberGrading.mem_grade
      D H h26 hHG hGH l b).mp hb)
  rw [← hx, ← hy, LatticeBRSTCohomologyField.product_classOf]
  apply (LatticeBRSTGhostNumberGrading.mem_grade D H h26 hHG hGH (k + l) _).mpr
  rw [LatticeBRSTGhostNumberGrading.Pi_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change Pg D (k + l) (cycleMode D H (-1) x y : State D) =
    (cycleMode D H (-1) x y : State D)
  apply (LatticeBRSTGhostNumberGrading.Pg_fixed_iff D (k + l) _).mpr
  simpa only [LatticeBRSTCohomologyField.cycleMode_val,
    LatticeBRSTCohomologyField.originalMode_apply] using
    mode_degree D k l (-1) (x : State D) (y : State D) hNx hNy

end
end D5.S3.VertexAlgebra.LatticeBRSTGhostNumberProduct
