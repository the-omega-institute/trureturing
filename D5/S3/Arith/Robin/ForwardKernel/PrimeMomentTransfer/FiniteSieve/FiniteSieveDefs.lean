/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite uniform sieve variables define interval moments and explicit interval-moment hypotheses. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.IntervalCovariance
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SignedCubeMomentModel
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Totient

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

def sieveDensity (Q : ℕ+) : ℝ := (Q : ℝ) / (Nat.totient (Q : ℕ) : ℝ)
def sieveVariable (Q : ℕ+) (d : ℕ) (a : ZMod (Q : ℕ)) : ℝ :=
  sieveDensity Q * (if (a + (d : ZMod (Q : ℕ))).val.Coprime (Q : ℕ) then 1 else 0) - 1
def sieveExpectation (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) : ℝ := (∑ a, F a) / (Q : ℝ)
def sieveFunctional (Q : ℕ+) : (ZMod (Q : ℕ) → ℝ) →ₗ[ℝ] ℝ where
  toFun := sieveExpectation Q
  map_add' F G := by simp [sieveExpectation, Finset.sum_add_distrib, add_div]
  map_smul' c F := by
    change (∑ x, c * F x) / (Q : ℝ) = c * ((∑ x, F x) / (Q : ℝ))
    rw [← Finset.mul_sum]
    ring
def sieveIntervalSum (Q : ℕ+) (H a b : ℝ) (x : ZMod (Q : ℕ)) : ℝ :=
  ∑ d ∈ points H a b, sieveVariable Q d x
def sieveIntervalMoment {k : ℕ} (Q : ℕ+) (H : ℝ) (a b : Fin k → ℝ) : ℝ :=
  sieveExpectation Q (fun x => ∏ i, sieveIntervalSum Q H (a i) (b i) x)
def sieveIntervalPairing (Q : ℕ+) (H : ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  sieveIntervalMoment Q H ![a 0,a 1] ![b 0,b 1] * sieveIntervalMoment Q H ![a 2,a 3] ![b 2,b 3] +
  sieveIntervalMoment Q H ![a 0,a 2] ![b 0,b 2] * sieveIntervalMoment Q H ![a 1,a 3] ![b 1,b 3] +
  sieveIntervalMoment Q H ![a 0,a 3] ![b 0,b 3] * sieveIntervalMoment Q H ![a 1,a 2] ![b 1,b 2]
def sieveIntervalWickDefect (Q : ℕ+) (H : ℝ) (a b : Fin 4 → ℝ) : ℝ := sieveIntervalMoment Q H a b - sieveIntervalPairing Q H a b

def sieveCutoff (M H : ℝ) : ℕ := ⌊((M + 5) * H) ^ 10⌋₊
def primorialSieveModulus (M H : ℝ) : ℕ+ := ⟨primorial (sieveCutoff M H), primorial_pos _⟩
def finiteSingularSeries (y : ℕ) (D : Finset ℕ) : ℝ :=
  ∏ p ∈ y.primesLE,
    (1 - (D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion.localResidueCount
       (D.image (fun d : ℕ => (d : ℤ))) p : ℝ) / (p : ℝ)) /
    (1 - 1 / (p : ℝ)) ^ D.card
def centeredPairKernel (d e : ℕ) : ℝ := if d = e then 0 else center concreteSS {d,e}
private def pairKernelSquareSum (m : ℕ) : ℝ := kernelSquareSum centeredPairKernel m

/-- The square-sum asymptotic following from Montgomery–Soundararajan Theorem 2, equation (16). -/
def MSSecond : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
  |pairKernelSquareSum m + (m : ℝ) * Real.log m| ≤ C * m

def momentScale (k : ℕ) (H : ℝ) : ℝ := (H * Real.log H) ^ ((k : ℝ) / 2)
private def UniformSieveSmall (k : ℕ)
    (F : ℕ+ → ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ H : ℝ in atTop, ∀ a b : Fin k → ℝ, admissible M a b →
      |F (primorialSieveModulus M H) H a b| ≤ ε * momentScale k H

def FiniteSieveIntervals : Prop := UniformSieveSmall 3 sieveIntervalMoment ∧ UniformSieveSmall 4 sieveIntervalWickDefect
def finiteDistinctCorrelation {k : ℕ} (M H : ℝ) (a b : Fin k → ℝ) : ℝ :=
  corr (finiteSingularSeries (sieveCutoff M H)) H a b
def finitePairCorrelation (M H : ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  pairCorr (finiteSingularSeries (sieveCutoff M H)) H a b
def UniformIntervalSmall (k : ℕ) (F : ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (M : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℝ in atTop,
      ∀ a b : Fin k → ℝ, admissible M a b → |F H a b| ≤ ε * momentScale k H

def LocallyBoundedIntervalError {k : ℕ}
    (F : ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (M : ℝ) : Prop :=
  ∀ T : ℝ, 2 ≤ T → ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, H ∈ Icc 2 T →
    ∀ a b : Fin k → ℝ, admissible M a b → |F H a b| ≤ C * momentScale k H


/-- Each centered sieve indicator satisfies a quadratic identity. -/
theorem sieve_quadratic (Q : ℕ+) (d : ℕ) (x : ZMod (Q : ℕ)) :
    sieveVariable Q d x ^ 2 = (sieveDensity Q - 2) * sieveVariable Q d x + (sieveDensity Q - 1) := by
  unfold sieveVariable
  split_ifs <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- Translation preserves the totient count, so every sieve variable is centered. -/
theorem sieve_mean_zero (Q : ℕ+) (d : ℕ) : sieveExpectation Q (sieveVariable Q d) = 0 := by
  have hcard : (∑ x : ZMod (Q : ℕ),
      if x.val.Coprime (Q : ℕ) then (1 : ℝ) else 0) = Nat.totient (Q : ℕ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype]
    rw [← Fintype.card_congr (ZMod.unitsEquivCoprime (n := (Q : ℕ))),
      ZMod.card_units_eq_totient]
  have hshift := Equiv.sum_comp (Equiv.addRight (d : ZMod (Q : ℕ)))
    (fun x : ZMod (Q : ℕ) => if x.val.Coprime (Q : ℕ) then (1 : ℝ) else 0)
  simp only [Equiv.coe_addRight] at hshift
  have ht : (Nat.totient (Q : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr Q.pos).ne'
  unfold sieveExpectation sieveVariable
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hshift, hcard]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rw [sieveDensity, div_mul_cancel₀ _ ht, sub_self, zero_div]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
