/- GID: D5/S3/Arith/Lattices/Klartag/State/StateInvariant4
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/StateInvariant4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.ReflStep2
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
import D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.StateInvariant4

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open Module
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant2
open D5.S3.Arith.Lattices.Klartag.State.StateInvariant3
open D5.S3.Arith.Lattices.Klartag.Drift.ReflStep2

noncomputable section

section HalfLaw

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem reflStep2_eq_fun (k : ℕ) :
    reflStep2 q W A₀ ξ k = StateInvariant.reflStep q W A₀ ξ k :=
  funext fun ω => reflStep2_eq_reflStep k ω

theorem measurable_reflStep2 (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (reflStep2 q W A₀ ξ k) := by

  have h : Measurable ((fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
        reflOf q (chainU q W A₀ k p.1).2 p.2) ∘ (fun ω : Ω => (past ξ k ω, ξ k ω))) :=
    Measurable.comp (measurable_U_uncurry (q := q) (W := W) (A₀ := A₀) k)
      (Measurable.prodMk (measurable_past (ξ := ξ) hξ k) (hξ k))
  exact h

/-- **The reflected increment is measurable.** -/
theorem measurable_reflStep (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (StateInvariant.reflStep q W A₀ ξ k) := by
  have h := measurable_reflStep2 (q := q) (W := W) (A₀ := A₀) hξ k
  rwa [reflStep2_eq_fun] at h

/-- The partial sum of reflected increments, read as a function of the past sequence. -/
def reflSumPast (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (k : ℕ) (v : ℕ → EuclideanSpace ℝ (UT n)) :
    EuclideanSpace ℝ (UT n) :=
  ∑ j ∈ Finset.range k, reflOf q (chainU q W A₀ j v).2 (v j)

theorem measurable_reflSumPast (k : ℕ) : Measurable (reflSumPast q W A₀ k) := by
  show Measurable fun v : ℕ → EuclideanSpace ℝ (UT n) =>
    ∑ j ∈ Finset.range k, reflOf q (chainU q W A₀ j v).2 (v j)
  refine Finset.measurable_sum _ fun j _ => ?_
  have h : Measurable ((fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
        reflOf q (chainU q W A₀ j p.1).2 p.2)
      ∘ (fun v : ℕ → EuclideanSpace ℝ (UT n) => (v, v j))) :=
    Measurable.comp (measurable_U_uncurry (q := q) (W := W) (A₀ := A₀) j)
      (Measurable.prodMk measurable_id (measurable_pi_apply j))
  exact h

theorem reflSumPast_past (k : ℕ) (ω : Ω) :
    reflSumPast q W A₀ k (past ξ k ω)
      = ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω :=
  Finset.sum_congr rfl fun _j hj => reflOf_past_eq_reflStep (Finset.mem_range.1 hj) ω

/-- **The per-step law of the reflected increment**: the frozen rotation preserves `N(0, c²·Id)`. -/
theorem map_reflStep {c : ℝ} (hξ : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P)
    (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n))) (k : ℕ) :
    P.map (StateInvariant.reflStep q W A₀ ξ k) = scaled c (EuclideanSpace ℝ (UT n)) := by
  have h1 : P.map (reflStep2 q W A₀ ξ k) = scaled c (EuclideanSpace ℝ (UT n)) :=
    map_frozen_isometry_scaled (measurable_past hξ k) (hξ k)
      (indepFun_past hξ hindep k) (hlaw k)
      (fun v => reflOf q (chainU q W A₀ k v).2) (measurable_U_uncurry k)
  rwa [reflStep2_eq_fun] at h1

/-- **…and it stays independent of the partial sum before it.**  The partial sum is
`reflSumPast ∘ past`, a measurable function of the past, so `IndepFun.comp` applies. -/
theorem indepFun_sum_reflStep {c : ℝ} (hξ : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P)
    (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n))) (k : ℕ) :
    IndepFun (fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω)
      (StateInvariant.reflStep q W A₀ ξ k) P := by
  have h1 : IndepFun (past ξ k) (reflStep2 q W A₀ ξ k) P :=
    indepFun_frozen_isometry_scaled (measurable_past hξ k) (hξ k)
      (indepFun_past hξ hindep k) (hlaw k)
      (fun v => reflOf q (chainU q W A₀ k v).2) (measurable_U_uncurry k)
  have h2 := h1.comp (measurable_reflSumPast (q := q) (W := W) (A₀ := A₀) k) measurable_id
  have e1 : (reflSumPast q W A₀ k ∘ past ξ k)
      = fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω :=
    funext fun ω => reflSumPast_past k ω
  have e2 : (id ∘ reflStep2 q W A₀ ξ k) = StateInvariant.reflStep q W A₀ ξ k :=
    reflStep2_eq_fun k
  rw [e1, e2] at h2
  exact h2

theorem map_sum_reflStep {c : ℝ} (hc : 0 ≤ c) (hξ : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n)))
    (k : ℕ) :
    P.map (fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
  map_sum_scaled hc (fun j => measurable_reflStep hξ j) (fun j => map_reflStep hξ hindep hlaw j)
    (fun m => indepFun_sum_reflStep hξ hindep hlaw m) k

/-- **`hacc`: the failure probability of the accumulated event**, with both half-laws supplied.
The frozen `StateInvariant.measureReal_compl_accGood_le` wants `0 < ρ k` for every `k`, which
`ρ k = √k·c` fails at `k = 0`; the `k = 0` term of the union bound is vacuous anyway
(`gaussSum … 0 ω = 0 ≤ r₀`), so the union runs over `Ico 1 N` here. -/
theorem measureReal_compl_accGood_le' {N : ℕ} {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 ≤ r₀)
    (hs : 1 ≤ s) (hξm : ∀ k, Measurable (ξ k)) (hindep : iIndepFun ξ P)
    (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n)))
    (hthr : 6 * (Real.sqrt N * c) * s * Real.sqrt n ≤ r₀) :
    P.real (accGood q W A₀ ξ N r₀)ᶜ ≤ (N : ℝ) * (2 * (4 * Real.exp (-(s ^ 2 * n)))) := by
  classical
  set cc : ℝ := 4 * Real.exp (-(s ^ 2 * n)) with hcc
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hfac : (0 : ℝ) ≤ 6 * c * s * Real.sqrt n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le) hs0) (Real.sqrt_nonneg _)
  have hthr_k : ∀ k, k ≤ N → 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤ r₀ := by
    intro k hk
    calc 6 * (Real.sqrt k * c) * s * Real.sqrt n
        = Real.sqrt k * (6 * c * s * Real.sqrt n) := by ring
      _ ≤ Real.sqrt N * (6 * c * s * Real.sqrt n) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hk)) hfac
      _ = 6 * (Real.sqrt N * c) * s * Real.sqrt n := by ring
      _ ≤ r₀ := hthr
  have hξlaw : ∀ k, P.map (fun ω => ∑ j ∈ Finset.range k, ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
    fun k => map_sum_xi hc.le hξm hindep hlaw k
  have hrlaw : ∀ k, P.map (fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
    fun k => map_sum_reflStep hc.le hξm hindep hlaw k
  have hsub : (accGood q W A₀ ξ N r₀)ᶜ ⊆ ⋃ k ∈ Finset.Ico 1 N,
      ({ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖}
        ∪ {ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
            (symMat (∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω))‖}) := by
    intro ω hω
    simp only [accGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · exfalso
        subst hk0
        have hz : StateInvariant.gaussSum q W A₀ ξ 0 ω = 0 := by
          simp [StateInvariant.gaussSum]
        rw [hz, symMat_zero, map_zero, norm_zero] at hlt
        linarith
      · exact hk0
    refine Set.mem_biUnion (Finset.mem_Ico.2 ⟨hk1, hk⟩) ?_
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
    have hb := opNorm_gaussSum_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) k ω
    have h1 := hthr_k k (le_of_lt hk)
    linarith [hcon.1, hcon.2, hb, hlt]
  have hcard : ((Finset.Ico 1 N).card : ℝ) ≤ (N : ℝ) := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le N 1
  have hcc0 : (0 : ℝ) ≤ 2 * cc := by
    have : (0 : ℝ) < Real.exp (-(s ^ 2 * n)) := Real.exp_pos _
    rw [hcc]; linarith
  calc P.real (accGood q W A₀ ξ N r₀)ᶜ
      ≤ P.real (⋃ k ∈ Finset.Ico 1 N, _) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ k ∈ Finset.Ico 1 N, P.real
          ({ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖}
          ∪ {ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
              (symMat (∑ j ∈ Finset.range k,
                StateInvariant.reflStep q W A₀ ξ j ω))‖}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico 1 N, (2 * cc) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        have hρ : 0 < Real.sqrt k * c := mul_pos (Real.sqrt_pos.2 hkR) hc
        refine (measureReal_union_le _ _).trans ?_
        have hA := measureReal_opNorm_symMat_ge hρ
          (Finset.measurable_sum _ fun j _ => hξm j) (hξlaw k) s hs
        have hB := measureReal_opNorm_symMat_ge hρ
          (Finset.measurable_sum _ fun j _ => measurable_reflStep hξm j) (hrlaw k) s hs
        rw [hcc]; linarith
    _ = ((Finset.Ico 1 N).card : ℝ) * (2 * cc) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (2 * cc) := mul_le_mul_of_nonneg_right hcard hcc0

end HalfLaw

section Count

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The count event.**  Route M's lift bound is `|C_k| · η`; this is the event that buys `|C_N|`,
and `Chain.chain_snd_mono` makes the terminal count dominate every earlier one. -/
def countGood (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (c₃ : ℝ) : Set Ω :=
  {ω | ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) ≤ c₃}

/-- The contact set only grows, so one bound at `N` bounds every `k ≤ N`. -/
theorem card_le_of_countGood {N : ℕ} {c₃ : ℝ} {ω : Ω}
    (hω : ω ∈ countGood q W A₀ ξ N c₃) {k : ℕ} (hk : k ≤ N) :
    ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ≤ c₃ := by
  refine le_trans ?_ hω
  exact_mod_cast Finset.card_le_card (Chain.chain_snd_mono hk ω)

theorem card_eq_sum_indicator (N : ℕ) (ω : Ω) :
    ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)
      = ∑ i ∈ W, Set.indicator {ω | i ∈ (Chain.chain q W A₀ ξ N ω).2} (fun _ => (1 : ℝ)) ω := by
  classical
  have hfil : W.filter (fun i => i ∈ (Chain.chain q W A₀ ξ N ω).2)
      = (Chain.chain q W A₀ ξ N ω).2 := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Chain.chain_snd_subset_window N ω h, h⟩⟩
  rw [← hfil, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ (Chain.chain q W A₀ ξ N ω).2 <;> simp [Set.indicator, hi]

theorem measurable_card_chain (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Measurable fun ω => ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) := by
  classical
  simp only [card_eq_sum_indicator]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator
    (Chain.measurableSet_mem_active hξ N i)

theorem integrable_card_chain (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Integrable (fun ω => ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)) P := by
  classical
  have hint : ∀ i ∈ W, Integrable
      (fun ω => Set.indicator {ω | i ∈ (Chain.chain q W A₀ ξ N ω).2} (fun _ => (1 : ℝ)) ω) P :=
    fun i _ => (integrable_const (1 : ℝ)).indicator (Chain.measurableSet_mem_active hξ N i)
  have h := integrable_finsetSum (μ := P) W hint
  simpa only [← card_eq_sum_indicator] using h

/-- **Markov.**  The count event fails with probability at most `(∫ |C_N|)/c₃`. -/
theorem measureReal_compl_countGood_le (hξ : ∀ k, Measurable (ξ k)) {N : ℕ} {c₃ : ℝ}
    (hc₃ : 0 < c₃) :
    P.real (countGood q W A₀ ξ N c₃)ᶜ
      ≤ (∫ ω, ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) ∂P) / c₃ := by
  classical
  have hnn : (0 : ℝ → ℝ) = 0 := rfl
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => ((Chain.chain q W A₀ ξ N ω).2.card : ℝ))
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
    (integrable_card_chain hξ N) c₃
  have hsub : (countGood q W A₀ ξ N c₃)ᶜ
      ⊆ {ω | c₃ ≤ ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)} := by
    intro ω hω
    simp only [countGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    exact le_of_lt hω
  have hmono : P.real (countGood q W A₀ ξ N c₃)ᶜ
      ≤ P.real {ω | c₃ ≤ ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)} :=
    measureReal_mono hsub (measure_ne_top P _)
  rw [le_div_iff₀ hc₃, mul_comm]
  calc c₃ * P.real (countGood q W A₀ ξ N c₃)ᶜ
      ≤ c₃ * P.real {ω | c₃ ≤ ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)} :=
        mul_le_mul_of_nonneg_left hmono hc₃.le
    _ ≤ ∫ ω, ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) ∂P := hmk

theorem measureReal_compl_countGood_le_expected (hξ : ∀ k, Measurable (ξ k)) {N : ℕ} {c₃ : ℝ}
    (hc₃ : 0 < c₃) (weight err : ι → ℝ)
    (htail : ∀ i ∈ W, P.real {ω | i ∈ (Chain.chain q W A₀ ξ N ω).2} ≤ 2 * weight i + err i)
    {θ E : ℝ} (hθ : ∑ i ∈ W, weight i ≤ θ) (hE : ∑ i ∈ W, err i ≤ E) :
    P.real (countGood q W A₀ ξ N c₃)ᶜ ≤ (2 * θ + E) / c₃ := by
  refine le_trans (measureReal_compl_countGood_le hξ hc₃) ?_
  refine div_le_div_of_nonneg_right ?_ hc₃.le
  exact ChainDataInst.expected_card_le P W (fun ω => (Chain.chain q W A₀ ξ N ω).2)
    (fun ω => Chain.chain_snd_subset_window N ω)
    (fun i _ => Chain.measurableSet_mem_active hξ N i) weight err htail hθ hE

end Count

section Wired

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

end Wired

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

end Assembly

section Numeric

end Numeric

end

end D5.S3.Arith.Lattices.Klartag.State.StateInvariant4
