/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTOppositeRootBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTOppositeRootBracket
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Opposite-charge bracket vector in the original physical Lie image. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalBilinearInvariant
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber

/-!
SOURCE_ONLY_UNCOMPILED. This source has not been elaborated or kernel checked.
The imported candidate suppliers inherit no acceptance. Before native intake,
apply the accompanying minimal PhysicalLieSectors prerequisite patch: it
replaces the retired zero-energy call by existing physicalStates_current.
The sealed supplier bytes themselves have not been changed here.

The bracket, physical image, global quotient and bilinear form below are the
original definitions. Both global quotient slots retain incoming primitives
in all State D. The signed shell is derived from the actual integral quadratic
energy, with no positivity or nonzero-charge assumption. Neutral coordinates
are recovered by the original Cartan equivalence; invariance and the actual
minus-Gram computation determine the bracket vector. Every private helper
below is consumed by this inference.

Attribution: the original lattice fields, Wick pairing and BRST suppliers
retain their Bakalov--Kac, Carnahan, Kytölä, Kato--Ogawa and Lian--Zuckerman
attribution. Finite sums, linear maps and quotient algebra use Mathlib.
The full string-theory objective remains ACTIVE INCOMPLETE.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

open private physical_shell from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear unitCharge)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy chargeEnergy_zero)
open LatticeBRSTCohomologyField (Cohomology)
open LatticeBRSTCohomologyBVSecondOrder (cohomologyCurrent)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology (inclusion)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie (physicalImage)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan (cartanState cartanRepresentative
  cartanPhysicalImage neutralPhysicalImage neutralCartanEquiv gamma cartan_adjoint)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear (physicalBilinearForm
  physicalBilinearForm_representatives)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalBilinearInvariant (physicalBilinearForm_invariant)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber (physicalChargeFiber physicalChargeFiber_eq_fixedImage)

private theorem charge_energy_neg (D : LatticeData) (p : Charge D) :
    chargeEnergy D (-p) = chargeEnergy D p := by
  simp only [chargeEnergy, bilinear, Pi.neg_apply, neg_mul, mul_neg, neg_neg]

private theorem bilinear_opposite (D : LatticeData) (p : Charge D) :
    bilinear D p (-p) = -bilinear D p p := by
  simp only [bilinear, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

private theorem unit_bilinear (D : LatticeData) (i : Fin D.rank) (p : Charge D) :
    (bilinear D (unitCharge D i) p : ℂ) =
      ∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ) := by
  classical
  have h : bilinear D (unitCharge D i) p = ∑ j, D.G i j * p j := by
    unfold bilinear
    calc
      _ = ∑ k : Fin D.rank, if k = i then ∑ j, D.G k j * p j else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hki : k = i
        · simp only [unitCharge, if_pos hki, one_mul]
        · simp only [unitCharge, if_neg hki, zero_mul, Finset.sum_const_zero]
      _ = _ := by simp
  rw [h]
  push_cast <;> rfl

private theorem gamma_expansion (D : LatticeData)
    (f : Fin D.rank → ℂ) (p : Charge D) :
    gamma D f p =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, f i * (D.G i j : ℂ) * (p j : ℂ) := by
  unfold gamma
  simp only [unit_bilinear, Finset.mul_sum, mul_assoc]

private theorem gamma_neg (D : LatticeData) (f : Fin D.rank → ℂ) (p : Charge D) :
    gamma D f (-p) = -gamma D f p := by
  rw [gamma_expansion, gamma_expansion]
  simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

/-- Right multiplication by the supplied inverse recovers every row vector. -/
private theorem gram_row_recovery (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)
    (v : Fin D.rank → ℂ) (j : Fin D.rank) :
    (∑ k : Fin D.rank, (∑ i : Fin D.rank, v i * (D.G i k : ℂ)) * H k j) = v j := by
  classical
  have hentry (i : Fin D.rank) :
      (∑ k : Fin D.rank, (D.G i k : ℂ) * H k j) =
        if i = j then 1 else 0 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i j) hGH
    change (∑ k : Fin D.rank, (D.G i k : ℂ) * H k j) = _ at h
    simpa only [Matrix.one_apply] using h
  calc
    _ = ∑ i : Fin D.rank, v i * (∑ k : Fin D.rank, (D.G i k : ℂ) * H k j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ i : Fin D.rank, v i * (if i = j then 1 else 0) := by
      simp_rw [hentry]
    _ = v j := by simp [mul_ite]

/-- Basis tests of the actual minus-Gram form, followed by G H = 1. -/
private theorem coordinates_of_tests (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hGH : gramComplex D * H = 1)
    (p : Charge D) (b : ℂ) (e : Fin D.rank → ℂ)
    (htest : ∀ f : Fin D.rank → ℂ,
      -(∑ i : Fin D.rank, ∑ j : Fin D.rank, e i * (D.G i j : ℂ) * f j) =
        gamma D f p * b) :
    e = (-b) • (fun i => (p i : ℂ)) := by
  classical
  have hrow (j : Fin D.rank) :
      (∑ i : Fin D.rank, e i * (D.G i j : ℂ)) =
        (-b) * ∑ i : Fin D.rank, (p i : ℂ) * (D.G i j : ℂ) := by
    have h := htest (fun k => if k = j then 1 else 0)
    have hleft :
        (∑ i : Fin D.rank, ∑ k : Fin D.rank,
          e i * (D.G i k : ℂ) * (if k = j then 1 else 0)) =
          ∑ i : Fin D.rank, e i * (D.G i j : ℂ) := by
      simp [mul_ite]
    have hright : gamma D (fun k => if k = j then 1 else 0) p =
        ∑ i : Fin D.rank, (p i : ℂ) * (D.G i j : ℂ) := by
      calc
        _ = (bilinear D (unitCharge D j) p : ℂ) := by simp [gamma, ite_mul]
        _ = ∑ i : Fin D.rank, (D.G j i : ℂ) * (p i : ℂ) := unit_bilinear D j p
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [D.symmetric j i]
          ring
    rw [hleft, hright] at h
    linear_combination -h
  funext j
  change e j = (-b) * (p j : ℂ)
  calc
    e j = ∑ k : Fin D.rank, (∑ i : Fin D.rank, e i * (D.G i k : ℂ)) * H k j :=
      (gram_row_recovery D H hGH e j).symm
    _ = ∑ k : Fin D.rank,
        ((-b) * ∑ i : Fin D.rank, (p i : ℂ) * (D.G i k : ℂ)) * H k j := by
      simp_rw [hrow]
    _ = (-b) * (∑ k : Fin D.rank,
        (∑ i : Fin D.rank, (p i : ℂ) * (D.G i k : ℂ)) * H k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (-b) * (p j : ℂ) := by
      rw [gram_row_recovery D H hGH (fun i => (p i : ℂ)) j]

private theorem cartan_global_pairing (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (e f : Fin D.rank → ℂ) :
    physicalBilinearForm D H h26 hHG hGH
      (cartanPhysicalImage D H h26 hHG hGH e)
      (cartanPhysicalImage D H h26 hHG hGH f) =
      -(∑ i : Fin D.rank, ∑ j : Fin D.rank, e i * (D.G i j : ℂ) * f j) := by
  rw [physicalBilinearForm_representatives D H h26 hHG hGH
    (cartanPhysicalImage D H h26 hHG hGH e)
    (cartanPhysicalImage D H h26 hHG hGH f)
    (cartanRepresentative D H hHG hGH e) (cartanRepresentative D H hHG hGH f) rfl rfl]
  change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm.statePairing D (cartanState D e) (cartanState D f) = _
  exact D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm.statePairing_cartan (D := D) e f

private theorem bracket_neutral (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (x y : physicalImage D H h26 hHG hGH)
    (hx : (x : Cohomology D H h26 hHG hGH) ∈
      LinearMap.range (inclusion D H h26 hHG hGH p))
    (hy : (y : Cohomology D H h26 hHG hGH) ∈
      LinearMap.range (inclusion D H h26 hHG hGH (-p))) :
    ((⁅x, y⁆ : physicalImage D H h26 hHG hGH) : Cohomology D H h26 hHG hGH) ∈
      neutralPhysicalImage D H h26 hHG hGH := by
  have hxf : (x : Cohomology D H h26 hHG hGH) ∈ physicalChargeFiber D H h26 hHG hGH p :=
    ⟨x.property, hx⟩
  have hyf : (y : Cohomology D H h26 hHG hGH) ∈ physicalChargeFiber D H h26 hHG hGH (-p) :=
    ⟨y.property, hy⟩
  rw [physicalChargeFiber_eq_fixedImage D H h26 hHG hGH p] at hxf
  rw [physicalChargeFiber_eq_fixedImage D H h26 hHG hGH (-p)] at hyf
  have hadd := D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLieSectors.fixedImage_current_addition
    D H h26 hHG hGH p (-p) (1 - chargeEnergy D p) (1 - chargeEnergy D (-p))
    (physical_shell D p) (physical_shell D (-p)) x y hxf hyf
  have hlevel : (1 - chargeEnergy D p) + (1 - chargeEnergy D (-p)) - 1 -
      bilinear D p (-p) = 1 := by
    rw [charge_energy_neg, bilinear_opposite]
    have h := two_chargeEnergy D p
    omega
  have hout :
      ((⁅x, y⁆ : physicalImage D H h26 hHG hGH) : Cohomology D H h26 hHG hGH) ∈
        D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalImage H 0 1 h26 hHG hGH := by
    change cohomologyCurrent D H h26 hHG hGH x y ∈ _
    simpa only [add_neg_cancel, hlevel] using hadd
  change ((⁅x, y⁆ : physicalImage D H h26 hHG hGH) : Cohomology D H h26 hHG hGH) ∈
    physicalChargeFiber D H h26 hHG hGH 0
  rw [physicalChargeFiber_eq_fixedImage D H h26 hHG hGH 0]
  simpa only [chargeEnergy_zero, sub_zero] using hout

/-- The actual opposite-charge physical bracket, including zero charge.
The coefficient sign is forced by the original minus-Gram normalization. -/
theorem opposite_charge_bracket (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (x y : physicalImage D H h26 hHG hGH)
    (hx : (x : Cohomology D H h26 hHG hGH) ∈
      LinearMap.range (inclusion D H h26 hHG hGH p))
    (hy : (y : Cohomology D H h26 hHG hGH) ∈
      LinearMap.range (inclusion D H h26 hHG hGH (-p))) :
    ⁅x, y⁆ = (-physicalBilinearForm D H h26 hHG hGH x y) •
      cartanPhysicalImage D H h26 hHG hGH (fun i => (p i : ℂ)) := by
  let z : neutralPhysicalImage D H h26 hHG hGH :=
    ⟨((⁅x, y⁆ : physicalImage D H h26 hHG hGH) : Cohomology D H h26 hHG hGH),
      bracket_neutral D H h26 hHG hGH p x y hx hy⟩
  let E := neutralCartanEquiv D H h26 hHG hGH
  let e : Fin D.rank → ℂ := E.symm z
  have he : cartanPhysicalImage D H h26 hHG hGH e = ⁅x, y⁆ := by
    apply Subtype.ext
    change ((E e : neutralPhysicalImage D H h26 hHG hGH) :
      Cohomology D H h26 hHG hGH) = (z : Cohomology D H h26 hHG hGH)
    exact congrArg Subtype.val (E.apply_symm_apply z)
  have htest (f : Fin D.rank → ℂ) :
      -(∑ i : Fin D.rank, ∑ j : Fin D.rank, e i * (D.G i j : ℂ) * f j) =
        gamma D f p * physicalBilinearForm D H h26 hHG hGH x y := by
    have hyh : ⁅y, cartanPhysicalImage D H h26 hHG hGH f⁆ = gamma D f p • y := by
      calc
        _ = -⁅cartanPhysicalImage D H h26 hHG hGH f, y⁆ :=
          lie_skew y (cartanPhysicalImage D H h26 hHG hGH f)
        _ = -(gamma D f (-p) • y) := by
          rw [cartan_adjoint D H h26 hHG hGH f (-p) y hy]
        _ = gamma D f p • y := by rw [gamma_neg, neg_smul, neg_neg]
    calc
      _ = physicalBilinearForm D H h26 hHG hGH
          (cartanPhysicalImage D H h26 hHG hGH e)
          (cartanPhysicalImage D H h26 hHG hGH f) :=
        (cartan_global_pairing D H h26 hHG hGH e f).symm
      _ = physicalBilinearForm D H h26 hHG hGH ⁅x, y⁆
          (cartanPhysicalImage D H h26 hHG hGH f) := by rw [he]
      _ = physicalBilinearForm D H h26 hHG hGH x
          ⁅y, cartanPhysicalImage D H h26 hHG hGH f⁆ :=
        physicalBilinearForm_invariant D H h26 hHG hGH x y
          (cartanPhysicalImage D H h26 hHG hGH f)
      _ = gamma D f p * physicalBilinearForm D H h26 hHG hGH x y := by
        simp only [hyh, map_smul, smul_eq_mul]
  have hecoord : e = (-physicalBilinearForm D H h26 hHG hGH x y) •
      (fun i => (p i : ℂ)) :=
    coordinates_of_tests D H hGH p (physicalBilinearForm D H h26 hHG hGH x y) e htest
  calc
    ⁅x, y⁆ = cartanPhysicalImage D H h26 hHG hGH e := he.symm
    _ = cartanPhysicalImage D H h26 hHG hGH
        ((-physicalBilinearForm D H h26 hHG hGH x y) • (fun i => (p i : ℂ))) := by
      rw [hecoord]
    _ = _ := map_smul (cartanPhysicalImage D H h26 hHG hGH) _ _

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeRootBracket
