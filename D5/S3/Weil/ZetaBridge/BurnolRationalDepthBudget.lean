/- GID: D5/S3/Weil/ZetaBridge/BurnolRationalDepthBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/BurnolRationalDepthBudget
   mirror-E: none(waiver:exact-arithmetic-budget-interface)
   anchors: []
   digest: Compute a common Burnol depth by integer arithmetic and transport certified rational majorant and support bounds to the actual full Weil Gram. -/

import D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
import D5.S3.Weil.ZetaBridge.WeilFullGramUniformRemainder
import Mathlib.Data.Nat.Log

/-!
# An executable rational depth budget

For C <= c/d and a desired positive error p/q, use
N0 = Nat.log 4 ((c*q)/(d*p)), where the inner division is natural division.
The strict inequality c*q < d*p*4^(N+1) holds for every N >= N0.
All denominators are required positive in the soundness theorem. The function
itself is total and uses only natural arithmetic, with no real logarithm,
choice of a convergence threshold, or floating-point rounding.

The analytic majorant bound is an explicit input to this arithmetic owner.
Downstream composition must derive it from test-function and zero-tail data;
this file does not turn that input into an unconditional numerical zeta bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget

/-- A computable depth from rational upper-majorant and error-budget data. -/
def rationalQuarterDepth (c d p q : ℕ) : ℕ :=
  Nat.log 4 ((c * q) / (d * p))

/-- A rational support radius at a specified common convolution depth. -/
def rationalBurnolRadius (B K : ℚ) (N : ℕ) : ℚ :=
  ((N : ℚ) + 1) * B + K

/-- The depth calculation certifies a strict inequality in exact integers. -/
theorem rationalQuarterDepth_integer_sound
    (c d p q N : ℕ) (hd : 0 < d) (hp : 0 < p)
    (hN : rationalQuarterDepth c d p q ≤ N) :
    c * q < (d * p) * 4 ^ (N + 1) := by
  have hden : 0 < d * p := Nat.mul_pos hd hp
  have hlog : Nat.log 4 ((c * q) / (d * p)) < N + 1 := by
    change Nat.log 4 ((c * q) / (d * p)) ≤ N at hN
    omega
  have hpow : (c * q) / (d * p) < 4 ^ (N + 1) :=
    Nat.lt_pow_of_log_lt (by decide : 1 < (4 : ℕ)) hlog
  have hmul := Nat.mul_le_mul_left (d * p) (Nat.succ_le_iff.mpr hpow)
  have hmod := Nat.mod_lt (c * q) hden
  have hdecomp := Nat.mod_add_div (c * q) (d * p)
  nlinarith

/-- Given a certified rational upper bound on a real majorant, no limiting
argument is needed to verify the requested geometric error budget. -/
theorem rationalQuarterDepth_real_sound
    (c d p q N : ℕ) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q)
    (hN : rationalQuarterDepth c d p q ≤ N)
    (C : ℝ) (hC : C ≤ (c : ℝ) / (d : ℝ)) :
    (1 / 4 : ℝ) ^ (N + 1) * C < (p : ℝ) / (q : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : (0 : ℝ) < 4 ^ (N + 1) := by positivity
  have hint := rationalQuarterDepth_integer_sound c d p q N hd hp hN
  have hcross : (c : ℝ) * (q : ℝ) <
      ((d : ℝ) * (p : ℝ)) * 4 ^ (N + 1) := by exact_mod_cast hint
  have hratio : ((c : ℝ) / (d : ℝ)) / 4 ^ (N + 1) <
      (p : ℝ) / (q : ℝ) := by
    rw [div_div]
    apply (div_lt_div_iff₀ (mul_pos hd' hpow) hq').2
    nlinarith [hcross]
  have hle : C / (4 : ℝ) ^ (N + 1) ≤
      ((c : ℝ) / (d : ℝ)) / 4 ^ (N + 1) :=
    div_le_div_of_nonneg_right hC hpow.le
  have heq : (1 / 4 : ℝ) ^ (N + 1) * C = C / 4 ^ (N + 1) := by
    rw [div_pow]
    simp only [one_pow]
    ring
  rw [heq]
  exact hle.trans_lt hratio

noncomputable section

open Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.WeilFullGramUniformRemainder
open scoped BigOperators Matrix

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The computed threshold controls the actual full Gram on every coefficient
vector and every later common depth. No arbitrary matrix substitutes for it. -/
theorem rationalQuarterDepth_full_gram_margin
    (F : FiniteEvenWeilOrbitFrame Z ι) (P : OrbitBurnolPacket F)
    (c d p q : ℕ) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q)
    (hC : finiteMixedMajorantTotal Z P.killer ≤ (c : ℝ) / (d : ℝ))
    (N : ℕ) (hN : rationalQuarterDepth c d p q ≤ N) (a : ι → ℂ) :
    (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
      -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  have heps := rationalQuarterDepth_real_sound c d p q N hd hp hq hN
    (finiteMixedMajorantTotal Z P.killer) hC
  have hm (i : ι) : (1 : ℝ) ≤ (Z.multiplicity (F.index i) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Z.multiplicity_pos (F.index i)))
  have ht : frameOddTargetQuadratic F a ≤ -4 * finiteComplexEnergy a := by
    simpa only [mul_one] using frameOddTargetQuadratic_le_massFloor F 1 hm a
  have hr := (le_abs_self _).trans (burnol_actual_gram_uniform_remainder F P N a)
  have hs := mul_le_mul_of_nonneg_right heps.le (finiteComplexEnergy_nonneg a)
  linarith

/-- A common support certificate plus a rational majorant yields a completely
specified support/margin pair at the computed depth. The rational arithmetic
is executable; the analytic premises remain proof obligations about the
actual peak and killer tests. -/
theorem rationalBurnol_support_and_margin
    (F : FiniteEvenWeilOrbitFrame Z ι) (P : OrbitBurnolPacket F)
    (B K : ℚ)
    (hpeak : tsupport (P.peak : ℝ → ℂ) ⊆ Set.Icc (-(B : ℝ)) (B : ℝ))
    (hkill : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Set.Icc (-(K : ℝ)) (K : ℝ))
    (c d p q : ℕ) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q)
    (hC : finiteMixedMajorantTotal Z P.killer ≤ (c : ℝ) / (d : ℝ))
    (N : ℕ) (hN : rationalQuarterDepth c d p q ≤ N) (a : ι → ℂ) :
    tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
        Set.Icc (-(rationalBurnolRadius B K N : ℝ)) (rationalBurnolRadius B K N : ℝ) ∧
      (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
        -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  constructor
  · simpa [rationalBurnolRadius] using
      burnolSynthesis_tsupport_subset F P (B : ℝ) (K : ℝ) hpeak hkill N a
  · exact rationalQuarterDepth_full_gram_margin F P c d p q hd hp hq hC N hN a

#print axioms rationalQuarterDepth_integer_sound
#print axioms rationalQuarterDepth_real_sound
#print axioms rationalQuarterDepth_full_gram_margin
#print axioms rationalBurnol_support_and_margin

end
end D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
