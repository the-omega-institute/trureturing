/-
HISTORICAL SOURCE-ONLY provenance: direct specialization of the collected DerivedBracketProofs proof
terms (SHA256 0d2f1d2fede88c6f22c7025f98342bfe03972552d5577f499394b453a38b27e4).
Its bracket_apply, bracket_mem, bracket_leibniz, bracket_antisymmetric,
bracket_delta, bracket_leibniz_left, bracket_delta_right and bracket_jacobi
supply the proof mechanisms below. No historical BVData record or generic
bracket theory is introduced or imported. The obsolete SuperFieldProducts
bridges are unused; power_mod_two is only their needed scalar normalization.

The earlier eight SOURCE DRAFT suppliers are historical provenance only;
authoritative actual dependencies: inputs.json's native_five_supplier_custody_ref.
All classes are in the identical original
Cohomology D H h26 hHG hGH, on every original state and the full quotient with
BOTH inverse Gram hypotheses. The actual product, quotient parity and Delta
are imported unchanged. Delta is [b0 P0], never bare b0 on arbitrary cycles.
No raw second order, projection/homotopy, associativity, supercommutativity or
Delta-square proof is reconstructed here. The historical grade-membership
steps are specialized to the actual quotient parity eigenvalue equations.

Attribution of the collected proof terms and their suppliers is retained:
Bakalov--Kac for the lattice realization, Scott Carnahan / vertexAlg for field
and residue calculus, Kalle Kytola for Sugawara suppliers, and the original
ghost and Mathlib authors under their source notices. No novelty is asserted.
This is a parity-indexed super bracket, not a full integer ghost grading.
No parsing, elaboration, kernel, official or full-parent acceptance is claimed.
Native API/tactic adaptation remains pending on the same released hot tree;
no live repair source or result is an input to this source-only port.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTBVSecondOrder
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.LatticeBRSTBVBracket

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeBRSTCohomologyField
  (Cohomology product product_parity product_supercomm)
open LatticeBRSTZeroEnergyReduction (Delta Delta_square)
open LatticeBRSTZeroEnergyParity (Delta_parity_odd)
open LatticeBRSTBVSecondOrder (quotientDefect Delta_second_order)

noncomputable section

-- The historical sign was (-1)^(p % 2). Only this scalar conversion is needed.
private theorem power_mod_two (p : ℕ) :
    (-1 : ℂ)^p = (-1 : ℂ)^(p % 2) := by
  calc
    (-1 : ℂ)^p = (-1 : ℂ)^(p % 2 + 2 * (p / 2)) := by
      rw [Nat.mod_add_div]
    _ = (-1 : ℂ)^(p % 2) := by
      rw [pow_add, pow_mul]
      norm_num

private theorem power_case (p : ℕ) :
    (-1 : ℂ)^p = if p % 2 = 0 then 1 else -1 := by
  rcases Nat.mod_two_eq_zero_or_one p with residue | residue
  · simp [power_mod_two p, residue]
  · simp [power_mod_two p, residue]

/-- The actual bilinear derived bracket of the existing product and [b0 P0]. -/
def bracket (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : ℕ) :
    Cohomology D H h26 hHG hGH →ₗ[ℂ] Cohomology D H h26 hHG hGH →ₗ[ℂ] Cohomology D H h26 hHG hGH :=
  (-1 : ℂ)^p •
    ((product D H h26 hHG hGH).compr₂ (Delta D H h26 hHG hGH) -
      (product D H h26 hHG hGH).compl₁₂ (Delta D H h26 hHG hGH) LinearMap.id -
      (-1 : ℂ)^p • (product D H h26 hHG hGH).compl₁₂ LinearMap.id (Delta D H h26 hHG hGH))

/-- Collected bracket_apply, with literal natural powers in place of sign. -/
theorem bracket_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : ℕ) (u v : Cohomology D H h26 hHG hGH) :
    bracket D H h26 hHG hGH p u v =
      (-1 : ℂ)^p • Delta D H h26 hHG hGH (product D H h26 hHG hGH u v) -
      (-1 : ℂ)^p • product D H h26 hHG hGH (Delta D H h26 hHG hGH u) v -
      product D H h26 hHG hGH u (Delta D H h26 hHG hGH v) := by
  have hp := power_mod_two p
  rcases Nat.mod_two_eq_zero_or_one p with residue | residue <;>
    simp [bracket, hp, residue] <;> abel

-- Actual eigen-equation version of the consumed product grade-membership step.
private theorem product_eigen (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p q : ℕ) (u v : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v = (-1 : ℂ)^q • v) :
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH (product D H h26 hHG hGH u v) = (-1 : ℂ)^(p + q) • product D H h26 hHG hGH u v := by
  rw [product_parity D H h26 hHG hGH u v, hu, hv]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, pow_add, mul_comm]

-- Actual eigen-equation version of the consumed Delta grade-membership step.
private theorem Delta_eigen (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : ℕ) (u : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u) :
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH (Delta D H h26 hHG hGH u) = (-1 : ℂ)^(p + 1) • Delta D H h26 hHG hGH u := by
  rw [Delta_parity_odd D H h26 hHG hGH u, hu, map_smul]
  simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- Collected bracket_mem: the same three homogeneous summands, expressed
using actual quotient parity rather than an abstract grading submodule. -/
theorem bracket_parity (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p q : ℕ) (u v : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v = (-1 : ℂ)^q • v) :
    LatticeBRSTCohomologyField.parity D H h26 hHG hGH (bracket D H h26 hHG hGH p u v) = (-1 : ℂ)^(p + q + 1) • bracket D H h26 hHG hGH p u v := by
  have h₁ := Delta_eigen D H h26 hHG hGH (p + q) (product D H h26 hHG hGH u v)
    (product_eigen D H h26 hHG hGH p q u v hu hv)
  have h₂ : LatticeBRSTCohomologyField.parity D H h26 hHG hGH (product D H h26 hHG hGH (Delta D H h26 hHG hGH u) v) =
      (-1 : ℂ)^(p + q + 1) • product D H h26 hHG hGH (Delta D H h26 hHG hGH u) v := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      product_eigen D H h26 hHG hGH (p + 1) q (Delta D H h26 hHG hGH u) v
        (Delta_eigen D H h26 hHG hGH p u hu) hv
  have h₃ : LatticeBRSTCohomologyField.parity D H h26 hHG hGH (product D H h26 hHG hGH u (Delta D H h26 hHG hGH v)) =
      (-1 : ℂ)^(p + q + 1) • product D H h26 hHG hGH u (Delta D H h26 hHG hGH v) := by
    simpa only [Nat.add_assoc] using
      product_eigen D H h26 hHG hGH p (q + 1) u (Delta D H h26 hHG hGH v)
        hu (Delta_eigen D H h26 hHG hGH q v hv)
  simp only [bracket_apply, map_sub, map_smul, h₁, h₂, h₃,
    smul_sub, smul_smul, mul_comm]

/-- The left bracket action derives product; w is an arbitrary full class.
Collected scalar-congruence proof, consuming the real Delta_second_order. -/
theorem bracket_leibniz (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p q : ℕ) (u v w : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v = (-1 : ℂ)^q • v) :
    bracket D H h26 hHG hGH p u (product D H h26 hHG hGH v w) =
      product D H h26 hHG hGH (bracket D H h26 hHG hGH p u v) w +
        (-1 : ℂ)^((p + 1) * q) • product D H h26 hHG hGH v (bracket D H h26 hHG hGH p u w) := by
  have equality := congrArg (fun state => (-1 : ℂ)^p • state)
    (Delta_second_order D H h26 hHG hGH p q u v w hu hv)
  change (-1 : ℂ)^p •
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH u (product D H h26 hHG hGH v w)) -
        product D H h26 hHG hGH (Delta D H h26 hHG hGH u) (product D H h26 hHG hGH v w) -
        (-1 : ℂ)^p • product D H h26 hHG hGH u (Delta D H h26 hHG hGH (product D H h26 hHG hGH v w))) =
    product D H h26 hHG hGH ((-1 : ℂ)^p •
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH u v) - product D H h26 hHG hGH (Delta D H h26 hHG hGH u) v -
        (-1 : ℂ)^p • product D H h26 hHG hGH u (Delta D H h26 hHG hGH v))) w +
    (-1 : ℂ)^((p + 1) * q) • product D H h26 hHG hGH v ((-1 : ℂ)^p •
      (Delta D H h26 hHG hGH (product D H h26 hHG hGH u w) - product D H h26 hHG hGH (Delta D H h26 hHG hGH u) w -
        (-1 : ℂ)^p • product D H h26 hHG hGH u (Delta D H h26 hHG hGH w)))
  simpa only [quotientDefect, map_smul, LinearMap.smul_apply, smul_add, smul_smul, mul_comm]
    using equality

/-- Collected super antisymmetry, using actual product_supercomm. -/
theorem bracket_antisymmetric (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p q : ℕ) (u v : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v = (-1 : ℂ)^q • v) :
    bracket D H h26 hHG hGH p u v =
      -((-1 : ℂ)^((p + 1) * (q + 1))) • bracket D H h26 hHG hGH q v u := by
  rw [bracket_apply, bracket_apply,
    product_supercomm D H h26 hHG hGH v u q p hv hu,
    product_supercomm D H h26 hHG hGH (Delta D H h26 hHG hGH v) u (q + 1) p
      (Delta_eigen D H h26 hHG hGH q v hv) hu,
    product_supercomm D H h26 hHG hGH v (Delta D H h26 hHG hGH u) q (p + 1)
      hv (Delta_eigen D H h26 hHG hGH p u hu)]
  simp only [map_smul]

  have hp := power_mod_two p
  have hq := power_mod_two q
  have hp_case := power_case p
  have hq_case := power_case q
  rcases Nat.mod_two_eq_zero_or_one p with first_residue | first_residue <;>
    rcases Nat.mod_two_eq_zero_or_one q with second_residue | second_residue <;>
    simp [power_mod_two, Nat.add_mod, Nat.mul_mod, hp, hq,
      hp_case, hq_case, first_residue, second_residue] <;> module

/-- Collected Delta compatibility, with no parity premise on either class. -/
theorem bracket_delta (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : ℕ) (u v : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH (bracket D H h26 hHG hGH p u v) =
      bracket D H h26 hHG hGH (p + 1) (Delta D H h26 hHG hGH u) v + (-1 : ℂ)^(p + 1) • bracket D H h26 hHG hGH p u (Delta D H h26 hHG hGH v) := by
  simp only [bracket_apply, map_sub, map_smul, Delta_square D H h26 hHG hGH, map_zero,
    LinearMap.zero_apply]

  have hp := power_mod_two p
  have hp_case := power_case p
  rcases Nat.mod_two_eq_zero_or_one p with residue | residue <;>
    simp [power_mod_two, Nat.add_mod, Nat.mul_mod, hp, hp_case, residue] <;> module

/-- Collected Leibniz in the left product argument; its original third
parity premise is explicit. Jacobi below does not use this premise. -/
theorem bracket_leibniz_left (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p q r : ℕ) (u v w : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v = (-1 : ℂ)^q • v)
    (hw : LatticeBRSTCohomologyField.parity D H h26 hHG hGH w = (-1 : ℂ)^r • w) :
    bracket D H h26 hHG hGH (p + q) (product D H h26 hHG hGH u v) w =
      product D H h26 hHG hGH u (bracket D H h26 hHG hGH q v w) +
        (-1 : ℂ)^(q * (r + 1)) • product D H h26 hHG hGH (bracket D H h26 hHG hGH p u w) v := by
  rw [bracket_antisymmetric D H h26 hHG hGH (p + q) r (product D H h26 hHG hGH u v) w
    (product_eigen D H h26 hHG hGH p q u v hu hv) hw,
    bracket_leibniz D H h26 hHG hGH r p w u v hw hu,
    bracket_antisymmetric D H h26 hHG hGH r p w u hw hu,
    bracket_antisymmetric D H h26 hHG hGH r q w v hw hv]
  simp only [map_smul, LinearMap.smul_apply]

  have hp := power_mod_two p
  have hq := power_mod_two q
  have hr := power_mod_two r
  have hp_case := power_case p
  have hq_case := power_case q
  have hr_case := power_case r
  rcases Nat.mod_two_eq_zero_or_one p with first_residue | first_residue <;>
    rcases Nat.mod_two_eq_zero_or_one q with second_residue | second_residue <;>
    rcases Nat.mod_two_eq_zero_or_one r with third_residue | third_residue <;>
    simp [power_mod_two, Nat.add_mod, Nat.mul_mod, hp, hq, hr,
      hp_case, hq_case, hr_case, first_residue, second_residue, third_residue] <;> module

-- Only the consumed rearrangement of the collected bracket_delta.
private theorem bracket_delta_right (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p : ℕ) (u v : Cohomology D H h26 hHG hGH) :
    bracket D H h26 hHG hGH p u (Delta D H h26 hHG hGH v) = (-1 : ℂ)^(p + 1) •
      (Delta D H h26 hHG hGH (bracket D H h26 hHG hGH p u v) - bracket D H h26 hHG hGH (p + 1) (Delta D H h26 hHG hGH u) v) := by
  rw [bracket_delta]
  have hp := power_mod_two p
  have hp_case := power_case p
  rcases Nat.mod_two_eq_zero_or_one p with residue | residue
  · have hpsucc : (-1 : ℂ) ^ (p + 1) = -1 := by
      rw [pow_succ, hp]
      simp [residue]
    rw [hpsucc]
    module
  · have hpsucc : (-1 : ℂ) ^ (p + 1) = 1 := by
      rw [pow_succ, hp]
      simp [residue]
    rw [hpsucc]
    module

/-- Collected odd/super Jacobi on the identical actual full quotient.
Only u and v are parity eigenclasses; w is arbitrary, including mixed parity.
Natural labels record parity only, with no full integer ghost grading. -/
theorem bracket_jacobi (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (p q : ℕ) (u v w : Cohomology D H h26 hHG hGH)
    (hu : LatticeBRSTCohomologyField.parity D H h26 hHG hGH u = (-1 : ℂ)^p • u)
    (hv : LatticeBRSTCohomologyField.parity D H h26 hHG hGH v = (-1 : ℂ)^q • v) :
    bracket D H h26 hHG hGH p u (bracket D H h26 hHG hGH q v w) =
      bracket D H h26 hHG hGH (p + q + 1) (bracket D H h26 hHG hGH p u v) w +
        (-1 : ℂ)^((p + 1) * (q + 1)) • bracket D H h26 hHG hGH q v (bracket D H h26 hHG hGH p u w) := by
  rw [bracket_apply D H h26 hHG hGH q v w]
  simp only [map_sub, map_smul]
  rw [bracket_delta_right,
    bracket_leibniz D H h26 hHG hGH p (q + 1) u (Delta D H h26 hHG hGH v) w
      hu (Delta_eigen D H h26 hHG hGH q v hv),
    bracket_leibniz D H h26 hHG hGH p q u v (Delta D H h26 hHG hGH w) hu hv,
    bracket_leibniz D H h26 hHG hGH p q u v w hu hv,
    bracket_leibniz D H h26 hHG hGH (p + 1) q (Delta D H h26 hHG hGH u) v w
      (Delta_eigen D H h26 hHG hGH p u hu) hv,
    bracket_delta_right D H h26 hHG hGH p u v,
    bracket_delta_right D H h26 hHG hGH p u w,
    bracket_apply D H h26 hHG hGH (p + q + 1), bracket_apply D H h26 hHG hGH q]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]

  have hp := power_mod_two p
  have hq := power_mod_two q
  have hp_case := power_case p
  have hq_case := power_case q
  rcases Nat.mod_two_eq_zero_or_one p with first_residue | first_residue <;>
    rcases Nat.mod_two_eq_zero_or_one q with second_residue | second_residue <;>
    simp [power_mod_two, Nat.add_mod, Nat.mul_mod, hp, hq, hp_case, hq_case,
      first_residue, second_residue] <;> module

end
end D5.S3.VertexAlgebra.LatticeBRSTBVBracket
