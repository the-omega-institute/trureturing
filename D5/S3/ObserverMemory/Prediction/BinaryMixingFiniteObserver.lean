/- GID: D5/S3/ObserverMemory/Prediction/BinaryMixingFiniteObserver
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/BinaryMixingFiniteObserver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive binary mixing admits finite observers at every positive uniform accuracy. -/

import D5.S3.ObserverMemory.Prediction.BinaryMixingMemoryDivergence
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

namespace D5.S3.ObserverMemory.Prediction.BinaryMixingFiniteObserver

open D5.S3.ObserverMemory.Prediction.BinaryMixingMemoryDivergence

/-- Positive binary mixing admits one finite deterministic observer for every positive error
allowance. Its fixed tables work for every chronological history, including the empty word. -/
theorem finite_suffix_observer_exists (p r ε : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (hr : 0 < r) (hr' : r < 1 / 2) (hε : 0 < ε) :
    (∀ w : List Bool, 0 < wordMass p r w) ∧
    ∃ (S : Type) (_ : Fintype S) (s₀ : S) (T₀ T₁ : S → S) (t : S → ℝ),
      (∀ s, t s ∈ Set.Icc 0 1) ∧
      ∀ w : List Bool,
        |t (w.foldl (fun s b => if b then T₁ s else T₀ s) s₀) - prediction p r w| ≤ ε := by
  classical
  have hp1 : 0 < 1-p := by linarith
  have hr1 : 0 < 1-r := by linarith
  -- Positive mixing contracts log odds uniformly over both emitted symbols.
  let η := 1-2*r
  have hη : 0 < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  let B := Real.log ((1-r)/r)
  have hB : 0 < B := Real.log_pos ((one_lt_div hr).2 (by linarith))
  let G (x : ℝ) := Real.log (r+(1-r)*Real.exp x) - Real.log (1-r+r*Real.exp x)
  have hnum (x : ℝ) : 0 < r+(1-r)*Real.exp x := by positivity
  have hden (x : ℝ) : 0 < 1-r+r*Real.exp x := by positivity
  have hGderiv (x : ℝ) : HasDerivAt G
      (η*Real.exp x / ((r+(1-r)*Real.exp x)*(1-r+r*Real.exp x))) x := by
    have hn := (((Real.hasDerivAt_exp x).const_mul (1-r)).const_add r).log (ne_of_gt (hnum x))
    have hd := (((Real.hasDerivAt_exp x).const_mul r).const_add (1-r)).log (ne_of_gt (hden x))
    exact (hn.sub hd).congr_deriv (by dsimp [η]; field_simp; ring)
  have hGderiv_bound (x : ℝ) :
      |η*Real.exp x / ((r+(1-r)*Real.exp x)*(1-r+r*Real.exp x))| ≤ η := by
    have hD : 0 < (r+(1-r)*Real.exp x)*(1-r+r*Real.exp x) := mul_pos (hnum x) (hden x)
    rw [abs_of_pos (div_pos (mul_pos hη (Real.exp_pos x)) hD)]
    apply (div_le_iff₀ hD).2
    have hs : 0 ≤ r*(1-r)*(Real.exp x-1)^2 := mul_nonneg (mul_pos hr hr1).le (sq_nonneg _)
    have he : Real.exp x ≤ (r+(1-r)*Real.exp x)*(1-r+r*Real.exp x) := by nlinarith
    exact mul_le_mul_of_nonneg_left he hη.le
  have hGlip (x y : ℝ) : |G x-G y| ≤ η*|x-y| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ (Set.univ : Set ℝ)) => (hGderiv z).hasDerivWithinAt)
        (fun z _ => by simpa only [Real.norm_eq_abs] using hGderiv_bound z)
        convex_univ (Set.mem_univ y) (Set.mem_univ x)
  have hGbound (x : ℝ) : |G x| ≤ B := by
    have hlo : r/(1-r) ≤ (r+(1-r)*Real.exp x)/(1-r+r*Real.exp x) := by
      apply (div_le_div_iff₀ hr1 (hden x)).2
      nlinarith [mul_pos hη (Real.exp_pos x)]
    have hhi : (r+(1-r)*Real.exp x)/(1-r+r*Real.exp x) ≤ (1-r)/r := by
      apply (div_le_div_iff₀ (hden x) hr).2
      dsimp [η] at hη
      nlinarith
    have hloglo := Real.log_le_log (div_pos hr hr1) hlo
    have hloghi := Real.log_le_log (div_pos (hnum x) (hden x)) hhi
    rw [Real.log_div (ne_of_gt (hnum x)) (ne_of_gt (hden x))] at hloglo hloghi
    have he : Real.log (r/(1-r)) = -B := by
      dsimp [B]
      rw [Real.log_div (ne_of_gt hr) (ne_of_gt hr1),
        Real.log_div (ne_of_gt hr1) (ne_of_gt hr)]
      ring
    rw [he] at hloglo
    exact abs_le.2 ⟨hloglo, hloghi⟩
  have hsiglip (x y : ℝ) : |Real.sigmoid x-Real.sigmoid y| ≤ (1/4 : ℝ)*|x-y| := by
    have hb (z : ℝ) : ‖Real.sigmoid z*(1-Real.sigmoid z)‖ ≤ (1/4 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sigmoid_nonneg z)
        (sub_nonneg.mpr (Real.sigmoid_le_one z)))]
      nlinarith [sq_nonneg (Real.sigmoid z-1/2)]
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ (Set.univ : Set ℝ)) => (Real.hasDerivAt_sigmoid z).hasDerivWithinAt)
        (fun z _ => hb z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  -- Relate the analytic coordinates to the unnormalized chronological transfer.
  let a (b : Bool) : ℝ := if b then 1-p else p
  let c (b : Bool) : ℝ := if b then p else 1-p
  have ha (b : Bool) : 0 < a b := by cases b <;> simp [a, hp, hp1]
  have hc (b : Bool) : 0 < c b := by cases b <;> simp [c, hp, hp1]
  let F (x : ℝ) (b : Bool) := G (x+Real.log (c b/a b))
  let ell (w : List Bool) := Real.log ((wordVector p r w).2/(wordVector p r w).1)
  have hvecStep (w : List Bool) (b : Bool) :
      wordVector p r (w++[b]) = transfer p r (wordVector p r w) b := by
    simp [wordVector]
  have hpos (w : List Bool) : 0 < (wordVector p r w).1 ∧ 0 < (wordVector p r w).2 := by
    induction w using List.reverseRecOn with
    | nil => norm_num [wordVector]
    | append_singleton w b ih =>
      rw [hvecStep]
      rcases ih with ⟨hleft, hright⟩
      cases b <;> dsimp [transfer]
      all_goals constructor <;> positivity
  have hmass (w : List Bool) : 0 < wordMass p r w := add_pos (hpos w).1 (hpos w).2
  have htransfer (v : ℝ × ℝ) (b : Bool) (hv0 : 0 < v.1) (hv1 : 0 < v.2) :
      Real.log ((transfer p r v b).2/(transfer p r v b).1) =
        F (Real.log (v.2/v.1)) b := by
    dsimp only [F, G]
    rw [← Real.log_div (ne_of_gt (hnum _)) (ne_of_gt (hden _))]
    congr 1
    rw [Real.exp_add, Real.exp_log (div_pos hv1 hv0), Real.exp_log (div_pos (hc b) (ha b))]
    cases b <;> dsimp [transfer, a, c]
    all_goals field_simp
  have hellStep (w : List Bool) (b : Bool) : ell (w++[b]) = F (ell w) b := by
    dsimp only [ell]
    rw [hvecStep]
    exact htransfer _ b (hpos w).1 (hpos w).2
  have hellNil : ell [] = 0 := by norm_num [ell, wordVector]
  have hellFold (w : List Bool) : ell w = w.foldl F 0 := by
    induction w using List.reverseRecOn with
    | nil => exact hellNil
    | append_singleton w b ih =>
      rw [hellStep, ih]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hellBound (w : List Bool) : |ell w| ≤ B := by
    induction w using List.reverseRecOn with
    | nil => rw [hellNil, abs_zero]; exact hB.le
    | append_singleton w b ih => rw [hellStep]; exact hGbound _
  have hcommon (u : List Bool) (x y : ℝ) :
      |u.foldl F x-u.foldl F y| ≤ η^u.length*|x-y| := by
    induction u generalizing x y with
    | nil => simp
    | cons b u ih =>
      simp only [List.foldl_cons, List.length_cons]
      calc
        |u.foldl F (F x b)-u.foldl F (F y b)| ≤ η^u.length*|F x b-F y b| := ih _ _
        _ ≤ η^u.length*(η*|x-y|) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hη.le _)
          simpa only [F, add_sub_add_right_eq_sub] using
            hGlip (x+Real.log (c b/a b)) (y+Real.log (c b/a b))
        _ = η^(u.length+1)*|x-y| := by rw [pow_succ]; ring
  have hprediction (w : List Bool) :
      prediction p r w = p+(1-2*p)*Real.sigmoid (ell w) := by
    have hv0 := (hpos w).1
    have hv1 := (hpos w).2
    have hv := add_pos hv0 hv1
    have hs : Real.sigmoid (ell w) = (wordVector p r w).2/wordMass p r w := by
      dsimp [ell, Real.sigmoid, wordMass]
      rw [Real.exp_neg, Real.exp_log (div_pos hv1 hv0)]
      field_simp
      ring
    rw [hs]
    unfold prediction wordMass
    rw [hvecStep]
    dsimp [transfer]
    field_simp
    ring
  have hmassSplit (w : List Bool) :
      wordMass p r (w++[false])+wordMass p r (w++[true]) = wordMass p r w := by
    unfold wordMass
    rw [hvecStep, hvecStep]
    dsimp [transfer]
    ring
  have hprob (w : List Bool) : prediction p r w ∈ Set.Icc 0 1 := by
    constructor
    · exact (div_pos (hmass (w++[false])) (hmass w)).le
    · apply (div_le_one (hmass w)).2
      linarith [hmassSplit w, hmass (w++[true])]
  have hsuffix (v u : List Bool) :
      |prediction p r (v++u)-prediction p r u| ≤ (1-2*p)*B/4*η^u.length := by
    rw [hprediction, hprediction]
    have heq : (p+(1-2*p)*Real.sigmoid (ell (v++u))) -
        (p+(1-2*p)*Real.sigmoid (ell u)) =
        (1-2*p)*(Real.sigmoid (ell (v++u))-Real.sigmoid (ell u)) := by ring
    rw [heq, abs_mul, abs_of_pos (by linarith : 0 < 1-2*p)]
    have hlog : |ell (v++u)-ell u| ≤ η^u.length*B := by
      rw [hellFold, List.foldl_append, hellFold, ← hellFold v]
      exact (hcommon u (ell v) 0).trans (by
        rw [sub_zero]
        exact mul_le_mul_of_nonneg_left (hellBound v) (pow_nonneg hη.le _))
    calc
      (1-2*p)*|Real.sigmoid (ell (v++u))-Real.sigmoid (ell u)| ≤
          (1-2*p)*((1/4)*|ell (v++u)-ell u|) :=
        mul_le_mul_of_nonneg_left (hsiglip _ _) (by linarith)
      _ ≤ (1-2*p)*((1/4)*(η^u.length*B)) := by
        gcongr
        linarith
      _ = (1-2*p)*B/4*η^u.length := by ring
  -- A bounded suffix stores its own startup length and has a fixed probability readout.
  let C := (1-2*p)*B/4
  have hC : 0 < C := div_pos (mul_pos (by linarith) hB) (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hη1
  have hkε : C*η^k ≤ ε := by
    have h := (lt_div_iff₀ hC).1 hk
    nlinarith
  have htruncate (n : ℕ) (w : List Bool) (b : Bool) :
      ((w.rtake n)++[b]).rtake n = (w++[b]).rtake n := by
    cases n with
    | zero => simp
    | succ n =>
      rw [List.rtake_concat_succ, List.rtake_concat_succ]
      congr 1
      simp [List.rtake_eq_reverse_take_reverse, List.take_take]
  let S := {w : List Bool // w.length ≤ k}
  let : Fintype S := (List.finite_length_le Bool k).fintype
  let state (w : List Bool) : S := ⟨w.rtake k, by simp only [List.rtake, List.length_drop]; omega⟩
  let T (b : Bool) (s : S) : S := state (s.val++[b])
  let t (s : S) : ℝ := prediction p r s.val
  have hrun (w : List Bool) : w.foldl (fun s b => T b s) (state []) = state w := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w b ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      apply Subtype.ext
      exact htruncate k w b
  refine ⟨hmass, S, inferInstance, state [], T false, T true, t, ?_, ?_⟩
  · intro s
    exact hprob s.val
  · intro w
    have htable : (fun s b => if b then T true s else T false s) = (fun s b => T b s) := by
      funext s b
      cases b <;> rfl
    rw [htable, hrun]
    change |prediction p r (w.rtake k)-prediction p r w| ≤ ε
    by_cases hw : w.length ≤ k
    · have he : w.rtake k = w := by simp [List.rtake, Nat.sub_eq_zero_of_le hw]
      rw [he, sub_self, abs_zero]
      exact hε.le
    · have hlen : (w.rtake k).length = k := by
        simp only [List.rtake, List.length_drop]
        omega
      have he : w.take (w.length-k)++w.rtake k = w := by
        exact List.take_append_drop _ w
      have h := hsuffix (w.take (w.length-k)) (w.rtake k)
      rw [he, hlen, abs_sub_comm] at h
      exact h.trans hkε

end D5.S3.ObserverMemory.Prediction.BinaryMixingFiniteObserver
