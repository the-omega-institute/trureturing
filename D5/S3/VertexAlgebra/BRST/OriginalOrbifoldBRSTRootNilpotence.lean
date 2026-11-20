/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRootNilpotence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRootNilpotence
   mirror-E: none(waiver:algebraic-original-orbifold-brst-root-nilpotence)
   anchors: []
   utility: none
   digest: Positive-norm physical roots act locally nilpotently by the native BRST bracket. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalSpectrum
import Mathlib.Algebra.Lie.OfAssociative

/-! Adjoint powers shift momentum by repeated addition of the root momentum.
At positive norm the shifted sectors eventually exceed the relative mass-shell cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRootNilpotence

open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)
open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData orbifoldMode)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTMomentum
  (physicalMomentum degreeOne_bracket_mem_physicalMomentum physicalMomentum_grading)
open OriginalOrbifoldBRSTPhysicalSpectrum
  (ghostOneCohomologyEquivPhysicalMomentum physicalMomentumEquivOrbifoldGrade)
open OriginalOrbifoldRelativeMassShell (hyperbolic_chargeEnergy)
open OriginalOrbifoldRelativeQuartet (orbifoldGrade)
open OriginalOrbifoldRelativeSpectrum (ghostOneCohomology_subsingleton_of_one_lt)

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

/-- A momentum sector above the mass-shell cutoff is zero in the physical Lie algebra. -/
theorem physicalMomentum_eq_bot_of_one_lt {p : UCharge} (hp : 1 < p 0 * p 1) :
    physicalMomentum p = ⊥ := by
  let _ := ghostOneCohomology_subsingleton_of_one_lt p ((hyperbolic_chargeEnergy p).symm ▸ hp)
  let _ : Subsingleton (physicalMomentum p) :=
    (ghostOneCohomologyEquivPhysicalMomentum p).symm.injective.subsingleton
  exact Submodule.subsingleton_iff_eq_bot.mp inferInstance

private theorem one_lt_shifted_product {p : UCharge} (hp : 0 < p 0 * p 1) (q : UCharge) :
    ∃ n : ℕ, 1 < (q + n • p) 0 * (q + n • p) 1 := by
  let n := (q 0).natAbs + (q 1).natAbs + 2
  have hn : (n : ℤ) = |q 0| + |q 1| + 2 := by
    simp only [n, Nat.cast_add, Int.natCast_natAbs, Nat.cast_ofNat]
  have shift (a b : ℤ) (hb : 0 < b) (ha : 2 - (n : ℤ) ≤ a) :
      2 ≤ a + (n : ℤ) * b := by
    have hmul := mul_nonneg (Int.natCast_nonneg n) (show 0 ≤ b - 1 by omega)
    nlinarith only [ha, hmul]
  have product (a b : ℤ) (ha : 2 ≤ a) (hb : 2 ≤ b) : 1 < a * b :=
    (show (1 : ℤ) < 2 * 2 by decide).trans_le (mul_le_mul ha hb (by decide) (by omega))
  refine ⟨n, ?_⟩
  change 1 < (q 0 + n • p 0) * (q 1 + n • p 1)
  simp only [nsmul_eq_mul]
  rcases mul_pos_iff.mp hp with ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩
  · exact product _ _
      (shift _ _ hp0 (by linarith only [hn, neg_le_abs (q 0), abs_nonneg (q 1)]))
      (shift _ _ hp1 (by linarith only [hn, neg_le_abs (q 1), abs_nonneg (q 0)]))
  · have h0 := shift _ _ (neg_pos.mpr hp0)
      (show 2 - (n : ℤ) ≤ -q 0 by linarith only [hn, le_abs_self (q 0), abs_nonneg (q 1)])
    have h1 := shift _ _ (neg_pos.mpr hp1)
      (show 2 - (n : ℤ) ≤ -q 1 by linarith only [hn, le_abs_self (q 1), abs_nonneg (q 0)])
    rw [mul_neg, ← neg_add] at h0 h1
    rw [← neg_mul_neg]
    exact product _ _ h0 h1

set_option maxHeartbeats 1000000 in
-- Rewriting compositions elaborates the endomorphism instances on the BRST quotient.
private theorem ad_pow_mem_physicalMomentum {p q : UCharge} {x z : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hz : z ∈ physicalMomentum q) (n : ℕ) :
    ((LieAlgebra.ad ℂ DegreeOne x) ^ n) z ∈ physicalMomentum (q + n • p) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, zero_nsmul, add_zero] using hz
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change ⁅x, ((LieAlgebra.ad ℂ DegreeOne x) ^ n) z⁆ ∈ physicalMomentum (q + (n + 1) • p)
      simpa only [succ_nsmul', add_left_comm q p] using
        degreeOne_bracket_mem_physicalMomentum hx ih

set_option maxHeartbeats 1000000 in
-- The grading induction uses the submodule instances on the BRST quotient.
/-- The adjoint of a homogeneous positive-norm vector is locally nilpotent on degree one. -/
theorem ad_locally_nilpotent_of_pos {p : UCharge} {x : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hp : 0 < p 0 * p 1) (z : DegreeOne) :
    ∃ n : ℕ, ((LieAlgebra.ad ℂ DegreeOne x) ^ n) z = 0 := by
  let A : Module.End ℂ DegreeOne := LieAlgebra.ad ℂ DegreeOne x
  change ∃ n : ℕ, (A ^ n) z = 0
  have hz : z ∈ ⨆ q : UCharge, physicalMomentum q := by
    rw [physicalMomentum_grading.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction' physicalMomentum
    (motive := fun y _ => ∃ n : ℕ, (A ^ n) y = 0)
    ?_ ⟨0, map_zero _⟩ ?_ hz
  · intro q y hy
    obtain ⟨n, hn⟩ := one_lt_shifted_product (p := p) hp q
    have hbot : physicalMomentum (q + n • p) = ⊥ :=
      physicalMomentum_eq_bot_of_one_lt (p := q + n • p) hn
    have hmem : (A ^ n) y ∈ physicalMomentum (q + n • p) :=
      ad_pow_mem_physicalMomentum (p := p) (q := q) hx hy n
    exact ⟨n, ((physicalMomentum (q + n • p)).eq_bot_iff.mp hbot) _ hmem⟩
  · rintro y w _ _ ⟨m, hm⟩ ⟨n, hn⟩
    have hy : (A ^ max m n) y = 0 :=
      Module.End.pow_map_zero_of_le (f := A) (m := y) (le_max_left m n) hm
    have hw : (A ^ max m n) w = 0 :=
      Module.End.pow_map_zero_of_le (f := A) (m := w) (le_max_right m n) hn
    refine ⟨max m n, (map_add (A ^ max m n) y w).trans ?_⟩
    exact (congrArg₂ (fun a b : DegreeOne => a + b) hy hw).trans (zero_add 0)

private theorem coord_product_eq_one_of_ne_zero {p : UCharge} {x : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hx0 : x ≠ 0) (hp : 0 < p 0 * p 1) :
    p 0 * p 1 = 1 := by
  have hle : p 0 * p 1 ≤ 1 := by
    by_contra! h
    rw [physicalMomentum_eq_bot_of_one_lt (p := p) h] at hx
    exact hx0 ((Submodule.mem_bot ℂ).mp hx)
  omega

/-- A positive-norm momentum supporting a nonzero physical vector has squared norm two. -/
theorem root_norm_eq_two_of_pos {p : UCharge} {x : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hx0 : x ≠ 0) (hp : 0 < p 0 * p 1) :
    bilinear hyperbolicData p p = 2 := by
  rw [← two_chargeEnergy, hyperbolic_chargeEnergy, coord_product_eq_one_of_ne_zero hx hx0 hp,
    mul_one]

/-- Each nonzero positive-norm physical root space has multiplicity one. -/
theorem physicalMomentum_finrank_eq_one_of_pos {p : UCharge} {x : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hx0 : x ≠ 0) (hp : 0 < p 0 * p 1) :
    Module.finrank ℂ (physicalMomentum p) = 1 := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have he : chargeEnergy hyperbolicData p = 1 :=
    (hyperbolic_chargeEnergy p).trans (coord_product_eq_one_of_ne_zero hx hx0 hp)
  have hcut : massShellCutoff hyperbolicData p = 0 := by simp [massShellCutoff, he]
  calc
    _ = Module.finrank ℂ (orbifoldGrade (massShellCutoff hyperbolicData p)) :=
      (physicalMomentumEquivOrbifoldGrade p hp0 he.le).finrank_eq
    _ = 1 := by
      rw [hcut]
      change Module.finrank ℂ ((orbifoldMode 0).eigenspace ((0 : ℕ) : ℂ)) = 1
      rw [Nat.cast_zero]
      exact TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_low_spectrum.2.2.2.1

#print axioms physicalMomentum_eq_bot_of_one_lt
#print axioms ad_locally_nilpotent_of_pos
#print axioms root_norm_eq_two_of_pos
#print axioms physicalMomentum_finrank_eq_one_of_pos

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRootNilpotence
