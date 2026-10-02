/- GID: D5/S1/Digit/ZeckendorfProblem1Refutation
   generality: I
   mirror-B: none(waiver:external-named-problem-resolution)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: The exact partial MSD Fibonacci machine minimum has no positive uniform linear lower bound. -/

import D5.S1.Digit.ZeckendorfResidualMachine
import D5.S1.Digit.ZeckendorfResidualNormalForm
import D5.S1.Digit.ZeckendorfAvoidanceCount
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfProblem1Refutation

open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfContextualReplacement
open D5.S1.Digit.ZeckendorfResidualMachine
open D5.S1.Digit.ZeckendorfResidualNormalForm
open D5.S1.Digit.ZeckendorfAvoidanceCount
open Filter Topology

/-- Problem 1 of Moradi–Rampersad–Shallit,
https://arxiv.org/html/2603.21645v1#Thmproblem1;
preregistered source question: https://github.com/the-omega-institute/trureturing/issues/11703.
The source sequence is the parity of the occupied canonical Fibonacci digits,
and `residual c [] w` reads its shift at the actual padded MSD value of w.
The
minimum taken over all reachable finite partial Boolean MSD machines defined
exactly on legal padded Fibonacci words, with a counted zero-loop start. -/
def Problem1 : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c →
    a * c ≤ minimumStates c ∧ (minimumStates c : ℝ) ≤ b * c

/-- Literal negation of the full eventual uniform statement. Complete residual
normalization gives an unbounded Fibonacci family with sublinear state counts;
correctness is on every valid padded input, and every invalid input is undefined. -/
theorem problem1_refuted : ¬ Problem1 := by
  classical
  let φ := Real.goldenRatio
  let δ := 1 - (φ ^ (14 : ℕ))⁻¹
  have φpos : 0 < φ := Real.goldenRatio_pos
  have φone : 1 < φ := Real.one_lt_goldenRatio
  have δnonneg : 0 ≤ δ := by
    have hp : 1 ≤ φ ^ 14 := one_le_pow₀ φone.le
    have := inv_le_one_of_one_le₀ hp
    dsimp [δ]
    linarith
  have δlt : δ < 1 := by
    have := inv_pos.mpr (pow_pos φpos 14)
    dsimp [δ]
    linarith
  have realized (c : ℕ) : Admissible c (minimumStates c) ∧ 0 < minimumStates c ∧
      ∀ k, Admissible c k → minimumStates c ≤ k := by
    obtain ⟨hf,ha⟩ := finite_residual_realization c
    have nonempty : ({k | Admissible c k} : Set ℕ).Nonempty := ⟨_,ha⟩
    have hm : Admissible c (minimumStates c) := csInf_mem nonempty
    refine ⟨hm,?_,fun k hk => csInf_le (OrderBot.bddBelow _) hk⟩
    obtain ⟨P,o,hz,hout,hreach⟩ := hm
    have := P.start.isLt
    omega
  have enumeration (n : ℕ) (b : Fin 2) (w : List (Fin 2)) :
      w ∈ legalWords n b ↔ w.length = n ∧ NoAdjacentOnes (b :: w) := by
    induction n generalizing b w with
    | zero => cases w <;> simp [legalWords,NoAdjacentOnes]
    | succ n ih =>
      cases w with
      | nil => simp [legalWords]
      | cons a w =>
        fin_cases a <;> fin_cases b <;>
          simp [legalWords,ih,NoAdjacentOnes,List.isChain_cons_cons]
  have count_bound (H : ℕ) (hH : 14 ≤ H) :
      (minimumStates (Nat.fib H) : ℝ) ≤ 128 * φ ^ (H + 1) * δ ^ (H / 14) := by
    obtain ⟨hf,ha⟩ := finite_residual_realization (Nat.fib H)
    letI : Finite (ResidualState (Nat.fib H)) := hf
    let good := (legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))
    have reps (s : ResidualState (Nat.fib H)) :
        ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧
          s.val = residual (Nat.fib H) v ∧ ¬ B1 <:+: v.drop 7 := by
      obtain ⟨w,hw,he⟩ := s.property
      obtain ⟨v,hv,hl,hr,havoid⟩ := normalized_state_cover H hH w hw
      exact ⟨v,hv,hl,he.symm.trans hr,havoid⟩
    let rep (s : ResidualState (Nat.fib H)) := (reps s).choose
    have rep_spec (s : ResidualState (Nat.fib H)) :
        NoAdjacentOnes (rep s) ∧ (rep s).length = H + 7 ∧
          s.val = residual (Nat.fib H) (rep s) ∧ ¬ B1 <:+: (rep s).drop 7 :=
      (reps s).choose_spec
    have tail_mem (s : ResidualState (Nat.fib H)) : (rep s).drop 7 ∈ good := by
      apply List.mem_filter.mpr
      refine ⟨(enumeration H 0 _).mpr ⟨?_,?_⟩,?_⟩
      · simp [rep_spec s |>.2.1]
      · have hc := (rep_spec s).1.drop 7
        simpa [NoAdjacentOnes,List.isChain_cons] using hc
      · exact decide_eq_true (rep_spec s |>.2.2.2)
    let code (s : ResidualState (Nat.fib H)) :
        (Fin 7 → Fin 2) × Fin good.length :=
      (fun i => (rep s)[i.val]'(by have := (rep_spec s).2.1; omega),
        ⟨good.idxOf ((rep s).drop 7),List.idxOf_lt_length_of_mem (tail_mem s)⟩)
    have injective : Function.Injective code := by
      intro s t h
      have hp := congrArg Prod.fst h
      have ht := congrArg (fun x => x.2.val) h
      have tails : (rep s).drop 7 = (rep t).drop 7 := by
        have hs := List.getElem?_idxOf (tail_mem s)
        have ht' := List.getElem?_idxOf (tail_mem t)
        change good.idxOf ((rep s).drop 7) = good.idxOf ((rep t).drop 7) at ht
        rw [ht] at hs
        exact Option.some.inj (hs.symm.trans ht')
      have heads : (rep s).take 7 = (rep t).take 7 := by
        apply List.ext_getElem
        · simp [(rep_spec s).2.1,(rep_spec t).2.1]
        · intro i hi hj
          have hi7 : i < 7 := by
            simp only [List.length_take] at hi
            exact (lt_min_iff.mp hi).1
          simpa only [List.getElem_take] using congrFun hp ⟨i,hi7⟩
      have same : rep s = rep t := by
        have hs := List.take_append_drop 7 (rep s)
        have ht := List.take_append_drop 7 (rep t)
        rw [heads,tails] at hs
        exact hs.symm.trans ht
      apply Subtype.ext
      rw [(rep_spec s).2.2.1,(rep_spec t).2.2.1,same]
    have card_bound : Nat.card (ResidualState (Nat.fib H)) ≤ 128 * good.length := by
      have h := Nat.card_le_card_of_injective code injective
      simpa [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun] using h
    have min_bound := (realized (Nat.fib H)).2.2 _ ha
    have numeric := uniform_avoidance_count H
    change (good.length : ℝ) ≤ φ ^ (H + 1) * δ ^ (H / 14) at numeric
    have hn : (minimumStates (Nat.fib H) : ℝ) ≤ 128 * (good.length : ℝ) := by
      exact_mod_cast min_bound.trans card_bound
    nlinarith
  let C := 128 * (2 * φ + 1)
  have Cpos : 0 < C := by dsimp [C]; positivity
  have ratio_bound (H : ℕ) (hH : 14 ≤ H) :
      (minimumStates (Nat.fib H) : ℝ) ≤ C * δ ^ (H / 14) * Nat.fib H := by
    have hcount := count_bound H hH
    have monotone := Nat.fib_le_fib_succ (n := H - 1)
    have hr := Nat.fib_add_two (n := H - 1)
    have he : H - 1 + 1 = H := by omega
    have he' : H - 1 + 2 = H + 1 := by omega
    rw [he] at monotone
    rw [he,he'] at hr
    have hs : (Nat.fib (H + 1) : ℝ) ≤ 2 * Nat.fib H := by exact_mod_cast (by omega : Nat.fib (H+1) ≤ 2 * Nat.fib H)
    have hg : φ ^ (H + 1) ≤ (2 * φ + 1) * Nat.fib H := by
      have eq := Real.goldenRatio_mul_fib_succ_add_fib H
      change φ * Nat.fib (H + 1) + Nat.fib H = φ ^ (H + 1) at eq
      nlinarith
    have hd : 0 ≤ δ ^ (H / 14) := pow_nonneg δnonneg _
    have hh := mul_le_mul_of_nonneg_right hg (mul_nonneg (by norm_num : (0:ℝ) ≤ 128) hd)
    dsimp [C]
    nlinarith
  have limit : Tendsto (fun H : ℕ => C * δ ^ (H / 14)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one δnonneg δlt).const_mul C).comp
        (Nat.tendsto_div_const_atTop (by decide : (14 : ℕ) ≠ 0))
  have sublinear : Tendsto (fun H : ℕ =>
      (minimumStates (Nat.fib H) : ℝ) / Nat.fib H) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun H => div_nonneg (by positivity) (by positivity))) _ limit
    apply eventually_atTop.2
    refine ⟨14,fun H hH => ?_⟩
    have hfpos : 0 < (Nat.fib H : ℝ) := by
      exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < H))
    exact (div_le_iff₀ hfpos).mpr (ratio_bound H hH)
  intro h
  obtain ⟨a,b,ha,hb,c0,hlower⟩ := h
  have eventually_small : ∀ᶠ H : ℕ in atTop,
      (minimumStates (Nat.fib H) : ℝ) / Nat.fib H < a :=
    (tendsto_order.1 sublinear).2 a ha
  obtain ⟨K,hK⟩ := eventually_atTop.1 eventually_small
  let H := max K (c0 + 14)
  have hH : 14 ≤ H := by dsimp [H]; omega
  have hc : c0 ≤ Nat.fib H := by
    have hf := Nat.le_fib_add_one H
    dsimp [H] at hf ⊢
    omega
  have hfpos : 0 < (Nat.fib H : ℝ) := by
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < H))
  have hsmall : (minimumStates (Nat.fib H) : ℝ) / Nat.fib H < a :=
    hK H (le_max_left _ _)
  have lower := (hlower (Nat.fib H) hc).1
  have strict := (div_lt_iff₀ hfpos).mp hsmall
  linarith

#print axioms problem1_refuted

end D5.S1.Digit.ZeckendorfProblem1Refutation
