/- GID: D5/S3/Arith/Lattices/Klartag/State/StateInvariant2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/StateInvariant2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.StateInvariant
import D5.S3.Arith.Lattices.Klartag.Completion.Discharge
import D5.S3.Arith.Lattices.Klartag.State.StepGlue
import D5.S3.Arith.Lattices.Klartag.Completion.ParamsAdopted2

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.StateInvariant2

open MeasureTheory
open Matrix
open Finset
open Module
open ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant

noncomputable section

section Wired

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The union-bound cost at `N = ⌈16 n⁷ log n⌉`** — `Discharge.failure_le`'s successor at the new
`N` (`Discharge.failure_le` is stated for `ChainWiring.numStepsAdopted`, which is frozen). -/
theorem failure_le2 {n : ℕ} (hn : 3 ≤ n) {c : ℝ}
    (hc : c ≤ 4 * Real.exp (-(n : ℝ))
      + ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ))))) :
    c ≤ (33 * (n : ℝ) ^ 9 * Real.log n + 4) * Real.exp (-(n : ℝ)) := by
  have hexp : (0 : ℝ) < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hcost := ParamsAdopted2.stepGood_cost2_le hn
  have hrw : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ))))
      = (((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2))
        * Real.exp (-(n : ℝ)) := by ring
  rw [hrw] at hc
  nlinarith [hc, hcost, hexp]

end Wired

section Lift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The lift at one step is at most the number of newly broken constraints times the step's own
increment.**  The coefficient bound is `ChainWiring.coeff_le` — `1 − ⟪A + B, q i⟫ ≤ −⟪B, q i⟫`
because `A` already satisfies the constraint — and then Cauchy–Schwarz. -/
theorem norm_liftStep_le (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    ‖liftStep q W A₀ ξ k ω‖
      ≤ ((Chain.newActive q W A₀ ξ k ω).card : ℝ) * ‖gaussStep q W A₀ ξ k ω‖ := by
  classical
  set A := (Chain.chain q W A₀ ξ k ω).1 with hA
  set B := gaussStep q W A₀ ξ k ω with hB
  have hAk : A ∈ Chain.kSet q W := Chain.chain_fst_mem_kSet hA₀ hq hne k ω
  have hsub : liftStep q W A₀ ξ k ω
      = ∑ i ∈ Chain.violated q W (A + B), ((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i := by
    rw [liftStep]
    exact ChainWiring.lift_sub q W _
  have hterm : ∀ i ∈ Chain.violated q W (A + B),
      ‖((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i‖ ≤ ‖B‖ := by
    intro i hi
    obtain ⟨hiW, hilt⟩ := Chain.mem_violated.1 hi
    have hqne : q i ≠ 0 := hne i hiW
    have hq0 : (0 : ℝ) < ‖q i‖ := norm_pos_iff.2 hqne
    have hlam0 : (0 : ℝ) ≤ (1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2 := by
      apply div_nonneg (by linarith) (by positivity)
    have hle := ChainWiring.coeff_le hAk hi
    have hcs : |⟪B, q i⟫| ≤ ‖B‖ * ‖q i‖ := abs_real_inner_le_norm _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
    rw [div_mul_eq_mul_div, pow_two]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 - ⟪A + B, q i⟫) ≤ -⟪B, q i⟫ := by
      have h2 := (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < ‖q i‖ ^ 2)).1 hle
      linarith
    nlinarith [hcs, abs_le.1 hcs, hq0, h1]
  calc ‖liftStep q W A₀ ξ k ω‖
      = ‖∑ i ∈ Chain.violated q W (A + B), ((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i‖ := by
        rw [hsub]
    _ ≤ ∑ i ∈ Chain.violated q W (A + B), ‖((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i‖ :=
        norm_sum_le _ _
    _ ≤ ((Chain.violated q W (A + B)).card : ℝ) * ‖B‖ := by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Chain.newActive q W A₀ ξ k ω).card : ℝ) * ‖B‖ := rfl

end Lift

section Scaled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A linear isometry preserves `N(0, c²·Id)`, not just the standard Gaussian. -/
theorem scaled_map_isometry (c : ℝ) (U : E ≃ₗᵢ[ℝ] E) :
    (scaled c E).map U = scaled c E := by
  have hcomm : (U : E → E) ∘ (fun x : E => c • x) = (fun x : E => c • x) ∘ (U : E → E) := by
    funext x; simp [map_smul]
  rw [scaled, Measure.map_map U.continuous.measurable (by fun_prop), hcomm,
    ← Measure.map_map (by fun_prop) U.continuous.measurable, Increments.map_stdGaussian_isometry]

variable {α : Type*} [MeasurableSpace α]

/-- The frozen rotation at the level of joint laws, for `N(0, c²·Id)`. -/
theorem map_prod_isometry_scaled (c : ℝ) (μ : Measure α) [SFinite μ] (U : α → (E ≃ₗᵢ[ℝ] E))
    (hU : Measurable fun p : α × E => U p.1 p.2) :
    (μ.prod (scaled c E)).map (fun p => (p.1, U p.1 p.2)) = μ.prod (scaled c E) := by
  have hmeas : Measurable fun p : α × E => (p.1, U p.1 p.2) := measurable_fst.prodMk hU
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs), Measure.prod_apply hs]
  refine lintegral_congr fun a => ?_
  have hpre : (Prod.mk a ⁻¹' ((fun p : α × E => (p.1, U p.1 p.2)) ⁻¹' s))
      = (U a) ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  rw [hpre, ← Measure.map_apply (U a).continuous.measurable (measurable_prodMk_left hs),
    scaled_map_isometry]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem map_prod_eq_of_indepFun_scaled {c : ℝ} {Z : Ω → α} {ξ : Ω → E}
    (hZ : Measurable Z) (hξ : Measurable ξ) (hindep : IndepFun Z ξ P)
    (hlaw : P.map ξ = scaled c E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun p : α × E => U p.1 p.2) :
    P.map (fun ω => (Z ω, U (Z ω) (ξ ω))) = P.map (fun ω => (Z ω, ξ ω)) := by
  have hpair : P.map (fun ω => (Z ω, ξ ω)) = (P.map Z).prod (scaled c E) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw]
  have hcomp : (fun ω => (Z ω, U (Z ω) (ξ ω)))
      = (fun p : α × E => (p.1, U p.1 p.2)) ∘ (fun ω => (Z ω, ξ ω)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.prodMk hU) (hZ.prodMk hξ), hpair,
    map_prod_isometry_scaled c _ U hU]

/-- **The frozen rotation preserves the law, at scale `c`.** -/
theorem map_frozen_isometry_scaled {c : ℝ} {Z : Ω → α} {ξ : Ω → E}
    (hZ : Measurable Z) (hξ : Measurable ξ) (hindep : IndepFun Z ξ P)
    (hlaw : P.map ξ = scaled c E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun p : α × E => U p.1 p.2) :
    P.map (fun ω => U (Z ω) (ξ ω)) = scaled c E := by
  have hUZ : Measurable fun ω => U (Z ω) (ξ ω) := hU.comp (hZ.prodMk hξ)
  have h := map_prod_eq_of_indepFun_scaled hZ hξ hindep hlaw U hU
  have e1 : P.map (fun ω => U (Z ω) (ξ ω))
      = (P.map (fun ω => (Z ω, U (Z ω) (ξ ω)))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hUZ)]; rfl
  have e2 : P.map ξ = (P.map (fun ω => (Z ω, ξ ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hξ)]; rfl
  rw [e1, h, ← e2, hlaw]

/-- **…and it stays independent of the past, at scale `c`.** -/
theorem indepFun_frozen_isometry_scaled {c : ℝ} {Z : Ω → α} {ξ : Ω → E}
    (hZ : Measurable Z) (hξ : Measurable ξ) (hindep : IndepFun Z ξ P)
    (hlaw : P.map ξ = scaled c E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun p : α × E => U p.1 p.2) :
    IndepFun Z (fun ω => U (Z ω) (ξ ω)) P := by
  have hUZ : Measurable fun ω => U (Z ω) (ξ ω) := hU.comp (hZ.prodMk hξ)
  rw [indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hUZ.aemeasurable,
    map_prod_eq_of_indepFun_scaled hZ hξ hindep hlaw U hU,
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw,
    map_frozen_isometry_scaled hZ hξ hindep hlaw U hU]

end Scaled

section Past

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- The chain at step `k` reads only `ξ j` for `j < k`. -/
theorem chain_congr {Ω Ω' : Type*} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    {ξ' : ℕ → Ω' → EuclideanSpace ℝ (UT n)} {ω : Ω} {ω' : Ω'} (k : ℕ)
    (h : ∀ j, j < k → ξ j ω = ξ' j ω') :
    Chain.chain q W A₀ ξ k ω = Chain.chain q W A₀ ξ' k ω' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Chain.chain_succ, Chain.chain_succ,
      ih (fun j hj => h j (lt_trans hj (Nat.lt_succ_self k))), h k (Nat.lt_succ_self k)]

/-- The past of the increments, truncated at `k`. -/
def past {Ω : Type*} (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    ℕ → EuclideanSpace ℝ (UT n) := fun j => if j < k then ξ j ω else 0

/-- The chain read as a function of the past sequence. -/
def chainU (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (k : ℕ) (v : ℕ → EuclideanSpace ℝ (UT n)) : EuclideanSpace ℝ (UT n) × Finset ι :=
  Chain.chain q W A₀ (fun j (u : ℕ → EuclideanSpace ℝ (UT n)) => u j) k v

theorem chain_eq_chainU {Ω : Type*} (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    Chain.chain q W A₀ ξ k ω = chainU q W A₀ k (past ξ k ω) :=
  chain_congr k fun j hj => by simp [past, hj]

/-- The frozen reflection attached to an active set. -/
def reflOf (q : ι → EuclideanSpace ℝ (UT n)) (a : Finset ι) :
    EuclideanSpace ℝ (UT n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (UT n) :=
  Submodule.reflection (Chain.freeSub q a)

theorem measurable_U_uncurry (k : ℕ) :
    Measurable fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
      reflOf q (chainU q W A₀ k p.1).2 p.2 := by
  intro s hs
  have hset : (fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
        reflOf q (chainU q W A₀ k p.1).2 p.2) ⁻¹' s
      = ⋃ a : Finset ι,
          ({v : ℕ → EuclideanSpace ℝ (UT n) | (chainU q W A₀ k v).2 = a}
            ×ˢ ((reflOf q a) ⁻¹' s)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨(chainU q W A₀ k p.1).2, rfl, h⟩
    · rintro ⟨a, ha, h⟩
      rw [ha]
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun a => MeasurableSet.prod ?_ ?_
  · exact ChainWiring.measurableSet_active_eq
      (ξ := fun j (u : ℕ → EuclideanSpace ℝ (UT n)) => u j)
      (fun j => measurable_pi_apply j) k a
  · exact (reflOf q a).continuous.measurable hs

end Past

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

end Assembly

end

end D5.S3.Arith.Lattices.Klartag.State.StateInvariant2
