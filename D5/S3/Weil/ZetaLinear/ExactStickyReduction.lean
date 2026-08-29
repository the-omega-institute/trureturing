/- GID: D5/S3/Weil/ZetaLinear/ExactStickyReduction
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/ExactStickyReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completing the positive complementary block preserves positivity and negative inertia. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Exact sticky reduction

The retained and complementary spaces are kept separate, so the result also
applies when the complementary Hilbert space is infinite-dimensional.  The
negative index is constructed from finite-dimensional negative-definite
subspaces and therefore does not collapse on that carrier.
-/

noncomputable section

namespace D5.S3.Weil.ZetaLinear.ExactStickyReduction

/-- Finite dimensions realized by negative-definite linear subspaces of an
energy. -/
def negativeRanks {V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : V → ℝ) : Set ℕ :=
  {n | ∃ T : (Fin n → ℝ) →ₗ[ℝ] V,
    Function.Injective T ∧ ∀ x, x ≠ 0 → energy (T x) < 0}

/-- The negative inertia index, allowing an infinite value when finite
negative-definite subspaces have unbounded dimension. -/
def negativeIndex {V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : V → ℝ) : WithTop ℕ :=
  sSup (((fun n : ℕ => (n : WithTop ℕ)) '' negativeRanks energy))

/-- The quadratic energy of the full retained/complementary block operator. -/
def blockEnergy
    {HP HQ : Type*}
    [NormedAddCommGroup HP] [InnerProductSpace ℝ HP]
    [NormedAddCommGroup HQ] [InnerProductSpace ℝ HQ]
    (APP : HP →ₗ[ℝ] HP) (AQP : HP →ₗ[ℝ] HQ) (AQQ : HQ →ₗ[ℝ] HQ)
    (z : HP × HQ) : ℝ :=
  inner ℝ (APP z.1) z.1 + 2 * inner ℝ (AQP z.1) z.2 + inner ℝ (AQQ z.2) z.2

/-- The Schur-complement energy after solving the complementary block. -/
def schurEnergy
    {HP HQ : Type*}
    [NormedAddCommGroup HP] [InnerProductSpace ℝ HP]
    [NormedAddCommGroup HQ] [InnerProductSpace ℝ HQ]
    (APP : HP →ₗ[ℝ] HP) (AQP : HP →ₗ[ℝ] HQ)
    (AQQ : HQ →ₗ[ℝ] HQ) (AQQInv : HQ →ₗ[ℝ] HQ) (p : HP) : ℝ :=
  let r := AQQInv (AQP p)
  inner ℝ (APP p) p - inner ℝ (AQQ r) r

private theorem completing_square
    {HP HQ : Type*}
    [NormedAddCommGroup HP] [InnerProductSpace ℝ HP]
    [NormedAddCommGroup HQ] [InnerProductSpace ℝ HQ]
    (APP : HP →ₗ[ℝ] HP) (AQP : HP →ₗ[ℝ] HQ)
    (AQQ : HQ →ₗ[ℝ] HQ) (AQQInv : HQ →ₗ[ℝ] HQ)
    (hQQSymm : ∀ x y, inner ℝ (AQQ x) y = inner ℝ x (AQQ y))
    (hQQInv : AQQ.comp AQQInv = LinearMap.id)
    (p : HP) (q : HQ) :
    blockEnergy APP AQP AQQ (p, q) =
      inner ℝ (AQQ (q + AQQInv (AQP p))) (q + AQQInv (AQP p)) +
        schurEnergy APP AQP AQQ AQQInv p := by
  have hinv : AQQ (AQQInv (AQP p)) = AQP p := by
    exact DFunLike.congr_fun hQQInv (AQP p)
  rw [blockEnergy, schurEnergy]
  simp only [LinearMap.map_add, inner_add_left, inner_add_right]
  rw [hinv, hQQSymm q (AQQInv (AQP p)), hinv]
  rw [real_inner_comm q (AQP p)]
  ring

private theorem negativeRanks_block_eq
    {HP HQ : Type*}
    [NormedAddCommGroup HP] [InnerProductSpace ℝ HP]
    [NormedAddCommGroup HQ] [InnerProductSpace ℝ HQ]
    (APP : HP →ₗ[ℝ] HP) (AQP : HP →ₗ[ℝ] HQ)
    (AQQ : HQ →ₗ[ℝ] HQ) (AQQInv : HQ →ₗ[ℝ] HQ)
    (hQQNonneg : ∀ q, 0 ≤ inner ℝ (AQQ q) q)
    (hQQSymm : ∀ x y, inner ℝ (AQQ x) y = inner ℝ x (AQQ y))
    (hQQInv : AQQ.comp AQQInv = LinearMap.id) :
    negativeRanks (blockEnergy APP AQP AQQ) =
      negativeRanks (schurEnergy APP AQP AQQ AQQInv) := by
  ext n
  constructor
  · rintro ⟨T, hTInjective, hTNegative⟩
    let TP : (Fin n → ℝ) →ₗ[ℝ] HP := (LinearMap.fst ℝ HP HQ).comp T
    have hTPInjective : Function.Injective TP := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      by_contra hx0
      have hneg := hTNegative x hx0
      have hfirst : (T x).1 = 0 := by
        exact hx
      have hnonneg : 0 ≤ blockEnergy APP AQP AQQ (T x) := by
        rw [show T x = ((T x).1, (T x).2) by rfl]
        rw [completing_square APP AQP AQQ AQQInv hQQSymm hQQInv]
        rw [hfirst]
        simp only [map_zero, add_zero, schurEnergy, inner_zero_right, zero_sub]
        simpa only [neg_zero, add_zero] using hQQNonneg (T x).2
      exact (not_lt_of_ge hnonneg) hneg
    refine ⟨TP, hTPInjective, ?_⟩
    intro x hx
    have hneg := hTNegative x hx
    rw [show T x = ((T x).1, (T x).2) by rfl] at hneg
    rw [completing_square APP AQP AQQ AQQInv hQQSymm hQQInv] at hneg
    have hsquare := hQQNonneg ((T x).2 + AQQInv (AQP (T x).1))
    change schurEnergy APP AQP AQQ AQQInv (T x).1 < 0
    linarith
  · rintro ⟨T, hTInjective, hTNegative⟩
    let TQ : (Fin n → ℝ) →ₗ[ℝ] HQ :=
      -(AQQInv.comp (AQP.comp T))
    let TFull : (Fin n → ℝ) →ₗ[ℝ] HP × HQ := T.prod TQ
    have hTFullInjective : Function.Injective TFull := by
      intro x y hxy
      apply hTInjective
      exact congrArg Prod.fst hxy
    refine ⟨TFull, hTFullInjective, ?_⟩
    intro x hx
    have hneg := hTNegative x hx
    rw [show TFull x = (T x, TQ x) by rfl]
    rw [completing_square APP AQP AQQ AQQInv hQQSymm hQQInv]
    change inner ℝ (AQQ (-AQQInv (AQP (T x)) + AQQInv (AQP (T x))))
        (-AQQInv (AQP (T x)) + AQQInv (AQP (T x))) +
          schurEnergy APP AQP AQQ AQQInv (T x) < 0
    simpa using hneg

/-- Completing the strictly positive complementary block preserves both
nonnegativity and the full negative inertia index. -/
theorem exact_sticky_reduction
    {HP HQ : Type*}
    [NormedAddCommGroup HP] [InnerProductSpace ℝ HP]
    [NormedAddCommGroup HQ] [InnerProductSpace ℝ HQ]
    (APP : HP →ₗ[ℝ] HP) (AQP : HP →ₗ[ℝ] HQ)
    (AQQ : HQ →ₗ[ℝ] HQ) (AQQInv : HQ →ₗ[ℝ] HQ)
    (hQQNonneg : ∀ q, 0 ≤ inner ℝ (AQQ q) q)
    (hQQSymm : ∀ x y, inner ℝ (AQQ x) y = inner ℝ x (AQQ y))
    (hQQInv : AQQ.comp AQQInv = LinearMap.id) :
    ((∀ z, 0 ≤ blockEnergy APP AQP AQQ z) ↔
        ∀ p, 0 ≤ schurEnergy APP AQP AQQ AQQInv p) ∧
      negativeIndex (blockEnergy APP AQP AQQ) =
        negativeIndex (schurEnergy APP AQP AQQ AQQInv) := by
  constructor
  · constructor
    · intro h p
      have hp := h (p, -AQQInv (AQP p))
      rw [completing_square APP AQP AQQ AQQInv hQQSymm hQQInv] at hp
      simpa using hp
    · intro h z
      rw [show z = (z.1, z.2) by rfl]
      rw [completing_square APP AQP AQQ AQQInv hQQSymm hQQInv]
      exact add_nonneg (hQQNonneg _) (h _)
  · unfold negativeIndex
    rw [negativeRanks_block_eq APP AQP AQQ AQQInv hQQNonneg hQQSymm hQQInv]

#print axioms exact_sticky_reduction

end D5.S3.Weil.ZetaLinear.ExactStickyReduction
