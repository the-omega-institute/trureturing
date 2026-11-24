/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealRootLocalNilpotence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealRootLocalNilpotence
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The two real-root adjoints on actual relative BRST cohomology are locally nilpotent. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldEvenCurrent
import Mathlib.Algebra.Lie.OfAssociative

/-!
The native bracket shifts the plane momentum at each application. On both
real-root rays the plane energy eventually exceeds one, and the relative shell
in each of those momenta vanishes. Direct-sum induction gives a bound for every
cohomology class.

proof_shape: realRoot_ad_pow_incl_eq_zero, realRoot_ad_locallyNilpotent: content
admission_basis: escape-witness
escape_witness: Iterates of the native adjoint stay in the single summand
determined by the accumulated root shift. The two coordinate estimates place
that summand in the vanishing range of the actual relative shell.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (chargeEnergy)
open RelativeCohomology (GradedCycles GradedCohomology)

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H
local notation "ad" => LieAlgebra.ad ℂ MomentumH1

local instance (p : Momentum) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Momentum) : AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

private theorem ad_pow_incl_mem (σ q : Momentum) (u : H σ) (x : H q) (n : ℕ) :
    (ad (incl σ u) ^ n) (incl q x) ∈ LinearMap.range (incl (q + n • σ)) := by
  induction n with
  | zero =>
    have hdegree : q + (0 : ℕ) • σ = q := by
      funext i
      change q i + (0 : ℕ) • σ i = q i
      simp
    rw [pow_zero, Module.End.one_apply, congrArg (fun p => LinearMap.range (incl p)) hdegree]
    exact LinearMap.mem_range_self (incl q) x
  | succ n ih =>
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ih
    rw [pow_succ', Module.End.mul_apply, ← hy, LieAlgebra.ad_apply]
    change momentumBracket (incl σ u) (incl (q + n • σ) y) ∈ _
    rw [momentumBracket_incl]
    have hdegree : σ + (q + n • σ) = q + (n + 1) • σ := by
      rw [succ_nsmul]
      abel
    let z := incl (σ + (q + n • σ)) (bracket σ (q + n • σ) u y)
    change z ∈ LinearMap.range (incl (q + (n + 1) • σ))
    exact (congrArg (fun p => z ∈ LinearMap.range (incl p)) hdegree).mp
      (LinearMap.mem_range_self (incl (σ + (q + n • σ))) _)

/-- A negative available level kills every class in the native ghost-one quotient. -/
theorem ghostOne_eq_zero_of_negative_level (p : Momentum)
    (hp : 1 - chargeEnergy hyperbolicPlane p < 0) (x : H p) : x = 0 := by
  have hshell := relativeShell_eq_bot_of_negative_level p hp
  refine Submodule.Quotient.induction_on _ x (fun z => ?_)
  have hz : z.val.val = 0 :=
    ((relativeShell p).eq_bot_iff.mp hshell) _ z.val.property
  have hz' : z = 0 := Subtype.ext (Subtype.ext hz)
  rw [hz', Submodule.Quotient.mk_zero]

private theorem one_lt_mul_of_two_le {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    1 < a * b := by
  have h : (2 : ℤ) * 2 ≤ a * b := calc
    (2 : ℤ) * 2 ≤ a * 2 := mul_le_mul_of_nonneg_right ha (by decide)
    _ ≤ a * b := mul_le_mul_of_nonneg_left hb (by omega)
  omega

private theorem realRoot_shift_negative_level (σ q : Momentum)
    (hσ : σ = (fun _ => 1) ∨ σ = (fun _ => -1)) (n : ℕ)
    (hn : (q (0 : Fin 2)).natAbs + (q (1 : Fin 2)).natAbs + 2 ≤ n) :
    1 - chargeEnergy hyperbolicPlane (q + n • σ) < 0 := by
  have hbound : |q (0 : Fin 2)| + |q (1 : Fin 2)| + 2 ≤ (n : ℤ) := by
    rw [Int.abs_eq_natAbs (q (0 : Fin 2)), Int.abs_eq_natAbs (q (1 : Fin 2))]
    exact_mod_cast hn
  have hnonneg₀ := abs_nonneg (q (0 : Fin 2))
  have hnonneg₁ := abs_nonneg (q (1 : Fin 2))
  have hcoordinate (i : Fin 2) : (q + n • σ) i = q i + (n : ℤ) * σ i := by
    change q i + n • σ i = q i + (n : ℤ) * σ i
    rw [Int.nsmul_eq_mul]
  rw [plane_chargeEnergy, hcoordinate 0, hcoordinate 1]
  apply sub_neg.mpr
  rcases hσ with rfl | rfl
  · simp only [mul_one]
    have h₀ := neg_abs_le (q (0 : Fin 2))
    have h₁ := neg_abs_le (q (1 : Fin 2))
    exact one_lt_mul_of_two_le (by omega) (by omega)
  · simp only [mul_neg, mul_one]
    have h₀ := le_abs_self (q (0 : Fin 2))
    have h₁ := le_abs_self (q (1 : Fin 2))
    have h₀' : 2 ≤ -(q (0 : Fin 2) + -(n : ℤ)) := by omega
    have h₁' : 2 ≤ -(q (1 : Fin 2) + -(n : ℤ)) := by omega
    simpa only [neg_mul_neg] using one_lt_mul_of_two_le h₀' h₁'

/-- The adjoint of any class at momentum `(1,1)` or `(-1,-1)` vanishes on a
homogeneous input once the exponent exceeds the sum of the absolute coordinates
of the input momentum by at least two. -/
theorem realRoot_ad_pow_incl_eq_zero (σ q : Momentum) (u : H σ) (x : H q)
    (hσ : σ = (fun _ => 1) ∨ σ = (fun _ => -1)) (n : ℕ)
    (hn : (q (0 : Fin 2)).natAbs + (q (1 : Fin 2)).natAbs + 2 ≤ n) :
    (ad (incl σ u) ^ n) (incl q x) = 0 := by
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (ad_pow_incl_mem σ q u x n)
  rw [← hy, ghostOne_eq_zero_of_negative_level _ (realRoot_shift_negative_level σ q hσ n hn) y,
    map_zero]

/-- Both real-root adjoints are locally nilpotent on the full momentum direct sum. -/
theorem realRoot_ad_locallyNilpotent (σ : Momentum) (u : H σ)
    (hσ : σ = (fun _ => 1) ∨ σ = (fun _ => -1)) (x : MomentumH1) :
    ∃ N : ℕ, ∀ n ≥ N, (ad (incl σ u) ^ n) x = 0 := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, fun n _ => map_zero (ad (incl σ u) ^ n)⟩
  | of q y =>
    refine ⟨(q (0 : Fin 2)).natAbs + (q (1 : Fin 2)).natAbs + 2, fun n hn => ?_⟩
    change (ad (incl σ u) ^ n) (incl q y) = 0
    exact realRoot_ad_pow_incl_eq_zero σ q u y hσ n hn
  | add x y hx hy =>
    obtain ⟨Nx, hx⟩ := hx
    obtain ⟨Ny, hy⟩ := hy
    refine ⟨max Nx Ny, fun n hn => ?_⟩
    rw [map_add, hx n ((le_max_left Nx Ny).trans hn), hy n ((le_max_right Nx Ny).trans hn),
      add_zero]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
