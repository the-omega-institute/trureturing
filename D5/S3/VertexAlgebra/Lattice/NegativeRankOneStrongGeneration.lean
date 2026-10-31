/- GID: D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual all-state outer-insertion obstruction for negative rank one.
-/

import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NegativeRankOneStrongGeneration

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticePositiveEnergy LatticeCoefficientEnergy
open scoped BigOperators VertexOperator

noncomputable section

/- The coefficient of the oscillator constant in a fixed charge sector. -/
def groundCoefficient (D : LatticeData) (q : Charge D) : Carrier D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (q, 0)).comp (carrierCoeffEquiv D).toLinearMap

@[simp] theorem groundCoefficient_apply (D : LatticeData) (q : Charge D)
    (v : Carrier D) :
    groundCoefficient D q v = (v q).coeff 0 := by
  rfl

/- This is the exact projection consequence of the original all-state grading;
   it applies to arbitrary oscillator polynomials and arbitrary finite charge
   mixtures, with no positivity or global lower-bound premise. -/
theorem groundCoefficient_mode_eq_zero_of_grade_mismatch
    (D : LatticeData) (m n k : ℤ) (q : Charge D) (u v : Carrier D)
    (hu : u ∈ grade D m) (hv : v ∈ grade D n)
    (hneq : energy D (q, 0) ≠ m + n - k - 1) :
    groundCoefficient D q (((Y D u)[[k]]) v) = 0 := by
  have hout := actual_mode_grade D m n k u v hu hv
  have hz := (mem_grade_iff D (m + n - k - 1) _).mp hout (q, 0) hneq
  exact hz

/- The strict inequality which drives the positive-charge outer insertion in
   G=-2d.  The factors r,t are arbitrary oscillator degrees; no lower bound
   on the total charge energy is used. -/
theorem negative_rank_one_outer_energy_mismatch
    (d s q r t k : ℤ)
    (hd : 0 < d) (hs : 0 < s) (hsq : s < q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hk : k < 0) :
    -d * q ^ 2 ≠ (r - d * s ^ 2) + (t - d * (q - s) ^ 2) - k - 1 := by
  intro h
  have hqs : 0 < q - s := by omega
  have hprod : 0 < 2 * d * s * (q - s) := by positivity
  nlinarith

/- A directly consumable all-state specialization: whenever the two input
   homogeneous grades have the negative rank-one values and the output charge
   is q=s+(q-s), the oscillator-constant output of every strictly negative
   mode vanishes. The grade hypotheses are intentionally explicit so this
   statement remains faithful to the actual grading API. -/
theorem negative_rank_one_outer_insertion_zero
    (d s q r t k : ℤ) (D : LatticeData)
    (u v : Carrier D) (charge : Charge D)
    (hd : 0 < d) (hs : 0 < s) (hsq : s < q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hk : k < 0)
    (hu : u ∈ grade D (r - d * s ^ 2))
    (hv : v ∈ grade D (t - d * (q - s) ^ 2))
    (hcharge : energy D (charge, 0) = -d * q ^ 2) :
    groundCoefficient D charge (((Y D u)[[k]]) v) = 0 := by
  apply groundCoefficient_mode_eq_zero_of_grade_mismatch D
      (r - d * s ^ 2) (t - d * (q - s) ^ 2) k charge u v hu hv
  rw [hcharge]
  exact negative_rank_one_outer_energy_mismatch d s q r t k hd hs hsq hr ht hk

end
end D5.S3.VertexAlgebra.Lattice.NegativeRankOneStrongGeneration

