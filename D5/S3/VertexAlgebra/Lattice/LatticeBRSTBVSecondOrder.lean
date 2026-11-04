/-
SOURCE-ONLY: this candidate and its fixed current suppliers are uncompiled
source drafts. No parsing, elaboration, kernel or official acceptance is claimed.

Proof reuse: OriginalTopologicalApplications.quotientDefect_class,
quotient_B0_second_order_on_zero_representatives and quotient_B0_second_order
(fixed SHA256 85302c4b23c6e4e0f271ca7aa794ba69c65fbef4af813ca5e0204940696d95ad,
lines 482--515 and 587--613) supply the representative/linear-quotient mechanism.
The present raw identity is the collected actual_B0_second_order in
LatticeMatterGhostAntighostSecondOrder, not the historical operator or carrier.
The existing homogeneous_zero_energy_cycle_lift already reuses the current
homogeneous_cycle_lift; neither representative theory is reconstructed here.

Attribution is retained: Bakalov--Kac for the lattice construction;
Scott Carnahan / vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea
for field/residue calculus; Kalle Kytölä for the Sugawara suppliers; the original
ghost authors and Mathlib's Apache-2.0 linear/quotient machinery. No novelty
claim is made. Historical DerivedBracketProofs (fixed SHA256
0d2f1d2fede88c6f22c7025f98342bfe03972552d5577f499394b453a38b27e4) is retained
as provenance for the later derived-bracket consumer; it is not imported,
copied, instantiated or reproved in this concrete second-order transfer.

Only the existing FULL Cohomology D H h26 hHG hGH, its existing product and
the existing P0-reduced Delta are used. State retains every charge, oscillator
and ghost occupation. Zero energy is a choice of cycle representatives, not
a replacement quotient. There is no raw P0 multiplicativity or raw b0 descent
on nonzero-energy cycles. All raw terms below have actual Q-cycle witnesses.
The sign is literally the raw supplier's (-1)^((p+1)*q), without relabelling.
The parent full string/AdS-CFT goal remains active and incomplete.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyProduct
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyParity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTBVSecondOrder

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeBRST (totalCharge)
open LatticeBRSTCohomologyField
  (cycles Cohomology classOf classOf_surjective cycleMode product product_classOf)
open LatticeBRSTZeroEnergyReduction
  (P0 totalL0 totalL0_P0 P0_fixed_iff cycleP0 classOf_P0
    B0_P0_cycle Delta Delta_classOf)
open LatticeBRSTZeroEnergyProduct (zero_energy_mu Delta_product_classOf)
open LatticeBRSTZeroEnergyParity (homogeneous_zero_energy_cycle_lift)
open LatticeMatterGhostAntighostSecondOrder (mu)

noncomputable section

-- All declaration parameters are explicit; there are no section variables.

/-- The genuinely consumed defect of the existing product and existing Delta.
The label p is the first class's parity grade in Delta_second_order. -/
def quotientDefect (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : ℕ) (u v : Cohomology D H h26 hHG hGH) :
    Cohomology D H h26 hHG hGH :=
  Delta D H h26 hHG hGH (product D H h26 hHG hGH u v) -
    product D H h26 hHG hGH (Delta D H h26 hHG hGH u) v -
    (-1 : ℂ)^p • product D H h26 hHG hGH u (Delta D H h26 hHG hGH v)

-- This is only existing cycleMode closure at mode -1 on the full carrier.
private theorem mu_cycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x y : cycles D H) :
    totalCharge D H (mu D (x : State D) (y : State D)) = 0 :=
  (cycleMode D H (-1) x y).property

-- Raw b0 is used only after proving that the input is fixed by P0.
private theorem B0_cycle_of_zero_energy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : cycles D H) (hx : totalL0 D H (x : State D) = 0) :
    totalCharge D H (ghostB D 0 (x : State D)) = 0 := by
  have fixed : P0 D (x : State D) = (x : State D) :=
    (P0_fixed_iff D H hHG hGH _).mpr hx
  have closed := B0_P0_cycle D H h26 hHG hGH (x : State D) x.property
  change totalCharge D H (ghostB D 0 (P0 D (x : State D))) = 0 at closed
  rw [fixed] at closed
  exact closed

-- Each of the three raw defect summands has a separate genuine Q-cycle proof.
-- No parity hypothesis is needed for this closure fact.
private theorem raw_defect_cycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : ℕ) (x y : cycles D H)
    (hx : totalL0 D H (x : State D) = 0)
    (hy : totalL0 D H (y : State D) = 0) :
    totalCharge D H
      (LatticeMatterGhostAntighostSecondOrder.defect D p (x : State D) (y : State D)) =
        0 := by
  have hxB := B0_cycle_of_zero_energy D H h26 hHG hGH x hx
  have hyB := B0_cycle_of_zero_energy D H h26 hHG hGH y hy
  have hxy := mu_cycle D H x y
  have hxyL := zero_energy_mu D H hHG hGH (x : State D) (y : State D) hx hy
  have hBxy : totalCharge D H (ghostB D 0 (mu D (x : State D) (y : State D))) = 0 :=
    B0_cycle_of_zero_energy D H h26 hHG hGH
      ⟨mu D (x : State D) (y : State D), hxy⟩ hxyL
  have hleft : totalCharge D H (mu D (ghostB D 0 (x : State D)) (y : State D)) = 0 :=
    mu_cycle D H ⟨ghostB D 0 (x : State D), hxB⟩ y
  have hright : totalCharge D H (mu D (x : State D) (ghostB D 0 (y : State D))) = 0 :=
    mu_cycle D H x ⟨ghostB D 0 (y : State D), hyB⟩
  simp only [LatticeMatterGhostAntighostSecondOrder.defect,
    map_sub, map_smul, hBxy, hleft, hright, smul_zero, sub_zero]

/-- On actual zero-energy cycles the full quotient defect is the class of
the actual raw antighost defect. In particular its classOf argument is a cycle.
Delta_product_classOf consumes the previously proved reduced-product fixity. -/
theorem quotientDefect_classOf_zero_energy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : ℕ) (x y : cycles D H)
    (hx : totalL0 D H (x : State D) = 0)
    (hy : totalL0 D H (y : State D) = 0) :
    quotientDefect D H h26 hHG hGH p
      (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y) =
      classOf D H h26 hHG hGH
        ⟨LatticeMatterGhostAntighostSecondOrder.defect D p (x : State D) (y : State D),
          by
            change totalCharge D H
              (LatticeMatterGhostAntighostSecondOrder.defect D p
                (x : State D) (y : State D)) = 0
            exact raw_defect_cycle D H h26 hHG hGH p x y hx hy⟩ := by
  have hxP : P0 D (x : State D) = (x : State D) :=
    (P0_fixed_iff D H hHG hGH _).mpr hx
  have hyP : P0 D (y : State D) = (y : State D) :=
    (P0_fixed_iff D H hHG hGH _).mpr hy
  unfold quotientDefect
  rw [Delta_product_classOf D H h26 hHG hGH x y,
    Delta_classOf D H h26 hHG hGH x, Delta_classOf D H h26 hHG hGH y,
    product_classOf, product_classOf]
  rw [← map_sub, ← map_smul, ← map_sub]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change ghostB D 0 (mu D (P0 D (x : State D)) (P0 D (y : State D))) -
      mu D (ghostB D 0 (P0 D (x : State D))) (y : State D) -
      (-1 : ℂ)^p • mu D (x : State D) (ghostB D 0 (P0 D (y : State D))) =
    LatticeMatterGhostAntighostSecondOrder.defect D p (x : State D) (y : State D)
  simp only [hxP, hyP, LatticeMatterGhostAntighostSecondOrder.defect]

-- Historical zero-representative transfer, now on the PRESENT full quotient.
-- Products containing defects need only cycleMode closure, not an extra
-- spectral statement for b0 or a new zero-energy carrier.
private theorem Delta_second_order_on_zero_representatives (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p q : ℕ) (x y z : cycles D H)
    (hx : totalL0 D H (x : State D) = 0)
    (hy : totalL0 D H (y : State D) = 0)
    (hz : totalL0 D H (z : State D) = 0)
    (hxp : LatticeMatterGhostStateField.parity D (x : State D) =
      (-1 : ℂ)^p • (x : State D))
    (hyq : LatticeMatterGhostStateField.parity D (y : State D) =
      (-1 : ℂ)^q • (y : State D)) :
    quotientDefect D H h26 hHG hGH p (classOf D H h26 hHG hGH x)
        (product D H h26 hHG hGH
          (classOf D H h26 hHG hGH y) (classOf D H h26 hHG hGH z)) =
      product D H h26 hHG hGH
          (quotientDefect D H h26 hHG hGH p
            (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y))
          (classOf D H h26 hHG hGH z) +
        (-1 : ℂ)^((p + 1) * q) • product D H h26 hHG hGH
          (classOf D H h26 hHG hGH y)
          (quotientDefect D H h26 hHG hGH p
            (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH z)) := by
  have hyz : totalL0 D H (cycleMode D H (-1) y z : State D) = 0 :=
    zero_energy_mu D H hHG hGH (y : State D) (z : State D) hy hz
  rw [product_classOf D H h26 hHG hGH y z,
    quotientDefect_classOf_zero_energy D H h26 hHG hGH p x
      (cycleMode D H (-1) y z) hx hyz,
    quotientDefect_classOf_zero_energy D H h26 hHG hGH p x y hx hy,
    quotientDefect_classOf_zero_energy D H h26 hHG hGH p x z hx hz,
    product_classOf, product_classOf]
  rw [← map_smul, ← map_add]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change LatticeMatterGhostAntighostSecondOrder.defect D p (x : State D)
      (mu D (y : State D) (z : State D)) =
    mu D (LatticeMatterGhostAntighostSecondOrder.defect D p (x : State D) (y : State D))
        (z : State D) +
      (-1 : ℂ)^((p + 1) * q) • mu D (y : State D)
        (LatticeMatterGhostAntighostSecondOrder.defect D p (x : State D) (z : State D))
  exact LatticeMatterGhostAntighostSecondOrder.actual_B0_second_order D p q
    (x : State D) (y : State D) (z : State D) hxp hyq

/-- Genuine second order for the existing P0-reduced Delta and existing product
on the full current cohomology. Only u and v have parity eigenvalue hypotheses;
w is arbitrary, including mixed parity, charges and representative energies. -/
theorem Delta_second_order (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p q : ℕ) (u v w : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u =
      (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v =
      (-1 : ℂ)^q • v) :
    quotientDefect D H h26 hHG hGH p u (product D H h26 hHG hGH v w) =
      product D H h26 hHG hGH (quotientDefect D H h26 hHG hGH p u v) w +
        (-1 : ℂ)^((p + 1) * q) • product D H h26 hHG hGH v
          (quotientDefect D H h26 hHG hGH p u w) := by
  obtain ⟨x, hxclass, hx, hxp⟩ :=
    homogeneous_zero_energy_cycle_lift D H h26 hHG hGH u p hu
  obtain ⟨y, hyclass, hy, hyq⟩ :=
    homogeneous_zero_energy_cycle_lift D H h26 hHG hGH v q hv
  obtain ⟨z, hzclass⟩ := classOf_surjective D H h26 hHG hGH w
  have hz : totalL0 D H (cycleP0 D H h26 hHG hGH z : State D) = 0 :=
    totalL0_P0 D H hHG hGH (z : State D)
  have hzclass0 : classOf D H h26 hHG hGH (cycleP0 D H h26 hHG hGH z) = w :=
    (classOf_P0 D H h26 hHG hGH z).trans hzclass
  rw [← hxclass, ← hyclass, ← hzclass0]
  exact Delta_second_order_on_zero_representatives D H h26 hHG hGH p q
    x y (cycleP0 D H h26 hHG hGH z) hx hy hz hxp hyq

end
end D5.S3.VertexAlgebra.LatticeBRSTBVSecondOrder
