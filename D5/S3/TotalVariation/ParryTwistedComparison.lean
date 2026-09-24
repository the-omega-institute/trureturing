/- GID: D5/S3/TotalVariation/ParryTwistedComparison
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryTwistedComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform mixing and complete-prefix comparison for the actual signed Parry chain. -/

import D5.S3.TotalVariation.ParryResetEstimates
import D5.S3.TotalVariation.TwistedPrefixComparison
import D5.S3.TotalVariation.DataProcessing
import D5.S3.TotalVariation.Metric

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryResetEstimates
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.DataProcessing
open D5.S3.Divergence.ClassicalDPI
namespace D5.S3.TotalVariation.ParryTwistedComparison

/-- All relation bits of a complete state prefix, including both end transitions. -/
def prefixRelation {k R : ℕ} (v : Prefix k (R+1)) (i : Fin (R+1)) : Bool :=
  let w : Fin (R+2) → State k := Fin.cons v.1 v.2
  !(xor (w i.castSucc).1 (w i.succ).1)

/-- The defect at vertex R uses the same deterministic R-window table twice. -/
def prefixRuleDefect {k R : ℕ} (f : (Fin R → Bool) → Bool)
    (v : Prefix k (R+1)) : Bool :=
  xor (xor (f (fun i => prefixRelation v i.succ))
    (f (fun i => prefixRelation v i.castSucc))) (!(prefixRelation v (Fin.last R)))

/-- The source defect probability under the actual stationary signed Parry prefix. -/
noncomputable def stationaryDefect (k R : ℕ) (f : (Fin R → Bool) → Bool) : ℝ :=
  ∑ v : Prefix k (R+1) with prefixRuleDefect f v,
    referenceLaw k (parryParameter k) (R+1) (parryLaw k) v

/-- The probability of exactly the same rule event under the actual twisted prefix. -/
noncomputable def twistedDefect (k R G : ℕ) (f : (Fin R → Bool) → Bool) : ℝ :=
  ∑ v : Prefix k (R+1) with prefixRuleDefect f v,
    twistedLaw k (parryParameter k) (R+1) G v

/-- The actual stationary chain mixes uniformly in the forbidden-run length. The same
three-step contraction gives the numerical comparison of entire twisted prefixes. -/
theorem parry_mixing_and_complete_prefix (k : ℕ) (hk : 2 ≤ k) :
    (∀ (G : ℕ) (s : State k),
      totalVariation (fun t => (kernel k (parryParameter k)^G) s t) (parryLaw k) ≤
        (3/4:ℝ)^(G/3)) ∧
    (∀ (n G : ℕ), 2 ≤ n+G →
      totalVariation (twistedLaw k (parryParameter k) n G)
        (referenceLaw k (parryParameter k) n (parryLaw k)) ≤
        2 * (n+G:ℕ) * (3/4:ℝ)^(G/3) + Real.goldenRatio^(2-((n+G:ℕ):ℤ))) ∧
    (∀ (R G : ℕ), 1 ≤ R → 1 ≤ G → ∀ f : (Fin R → Bool) → Bool,
      |twistedDefect k R G f - stationaryDefect k R f| ≤
        2 * (R+1+G:ℕ) * (3/4:ℝ)^(G/3) +
          Real.goldenRatio^(2-((R+1+G:ℕ):ℤ))) := by
  classical
  let Q := kernel k (parryParameter k)
  let π := parryLaw k
  let z : Fin k := ⟨0,by omega⟩
  obtain ⟨hr, hb, hS, hQ, hrow, hπ, hπsum, hstat, hflip⟩ := parry_stationary_law k hk
  have hrows : ∀ (m : ℕ) (s : State k), ∑ t, (Q^m) s t = 1 := by
    intro m
    induction m with
    | zero => intro s; simp [Matrix.one_apply]
    | succ m ih =>
      intro s
      calc
        (∑ t, (Q^(m+1)) s t) = ∑ u, (Q^m) s u * ∑ t, Q u t := by
          simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_comm
        _ = ∑ u, (Q^m) s u := by
          apply Finset.sum_congr rfl
          intro u _
          rw [show (∑ t, Q u t) = 1 from hrow u, mul_one]
        _ = 1 := ih s
  have hstats : ∀ (m : ℕ) (t : State k), ∑ s, π s * (Q^m) s t = π t := by
    intro m
    induction m with
    | zero => intro t; simp [Matrix.one_apply]
    | succ m ih =>
      intro t
      rw [pow_succ]
      simp_rw [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, ih]
      exact hstat t
  let b : State k → ℝ := fun t =>
    (if t = (false,z) then 1/8 else 0) + (if t = (true,z) then 1/8 else 0)
  have hbtotal : ∑ t, b t = 1/4 := by
    simp [b, Finset.sum_add_distrib]
    <;> norm_num
  have hminor (s t : State k) : b t ≤ (Q^3) s t := by
    by_cases ht : t.2 = z
    · have h := parry_three_step_minorization k hk s t.1
      rcases t with ⟨a,j⟩
      dsimp at ht
      subst j
      cases a <;> simpa [b, Q, z] using h
    · have hf : t ≠ (false,z) := by intro he; exact ht (congrArg Prod.snd he)
      have ht' : t ≠ (true,z) := by intro he; exact ht (congrArg Prod.snd he)
      simpa [b,hf,ht'] using Matrix.pow_apply_nonneg hQ 3 s t
  let T : State k → State k → ℝ := fun s t => (4/3) * ((Q^3) s t - b t)
  have hTpos (s t) : 0 ≤ T s t := mul_nonneg (by norm_num) (sub_nonneg.mpr (hminor s t))
  have hTrow (s) : ∑ t, T s t = 1 := by
    simp only [T, ← Finset.mul_sum, Finset.sum_sub_distrib, hrows, hbtotal]
    norm_num
  have hcontract (u v : State k → ℝ) (huv : ∑ x, u x = ∑ x, v x) :
      totalVariation (channelOutput (fun x y => (Q^3) x y) u)
        (channelOutput (fun x y => (Q^3) x y) v) ≤ (3/4:ℝ) * totalVariation u v := by
    have hzero : ∑ x, (u x-v x) = 0 := by rw [Finset.sum_sub_distrib,huv,sub_self]
    have hd (y) : channelOutput (fun x y => (Q^3) x y) u y -
        channelOutput (fun x y => (Q^3) x y) v y =
        (3/4:ℝ) * (channelOutput T u y - channelOutput T v y) := by
      unfold channelOutput
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      calc
        _ = ∑ x, ((3/4:ℝ) * (u x*T x y-v x*T x y) + (u x-v x)*b y) := by
          apply Finset.sum_congr rfl
          intro x _
          dsimp [T]
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hzero,zero_mul,add_zero]
    calc
      _ = (3/4:ℝ)*totalVariation (channelOutput T u) (channelOutput T v) := by
        unfold totalVariation
        simp_rw [hd, abs_mul, show |(3/4:ℝ)| = 3/4 by norm_num]
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (total_variation_channel_le u v T ⟨hTpos,hTrow⟩) (by norm_num)
  have hmix (G : ℕ) (s : State k) :
      totalVariation (fun t => (Q^G) s t) π ≤ (3/4:ℝ)^(G/3) := by
    have hblocks : ∀ m : ℕ,
        totalVariation (fun t => (Q^(3*m)) s t) π ≤ (3/4:ℝ)^m := by
      intro m
      induction m with
      | zero =>
        simpa using total_variation_le_one (fun t => (Q^0) s t) π
          ⟨Matrix.pow_apply_nonneg hQ 0 s, hrows 0 s⟩ ⟨hπ,hπsum⟩
      | succ m ih =>
        have he : channelOutput (fun x y => (Q^3) x y) (fun t => (Q^(3*m)) s t) =
            fun t => (Q^(3*(m+1))) s t := by
          funext t
          rw [show 3*(m+1) = 3*m+3 by omega, pow_add, Matrix.mul_apply]
          rfl
        have hπe : channelOutput (fun x y => (Q^3) x y) π = π := by
          funext t
          exact hstats 3 t
        have hc := hcontract (fun t => (Q^(3*m)) s t) π ((hrows _ _).trans hπsum.symm)
        rw [he,hπe] at hc
        calc
          _ ≤ (3/4:ℝ)*totalVariation (fun t => (Q^(3*m)) s t) π := hc
          _ ≤ (3/4:ℝ)*(3/4:ℝ)^m := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = _ := by rw [pow_succ]; ring
    have he : channelOutput (fun x y => (Q^(G%3)) x y)
        (fun t => (Q^(3*(G/3))) s t) = fun t => (Q^G) s t := by
      funext t
      have hG : G = 3*(G/3)+G%3 := by omega
      conv_rhs => rw [hG, pow_add, Matrix.mul_apply]
      rfl
    have hπe : channelOutput (fun x y => (Q^(G%3)) x y) π = π := by
      funext t
      exact hstats _ _
    have hc := total_variation_channel_le (fun t => (Q^(3*(G/3))) s t) π
      (fun x y => (Q^(G%3)) x y) ⟨Matrix.pow_apply_nonneg hQ _, hrows _⟩
    rw [he,hπe] at hc
    exact hc.trans (hblocks (G/3))
  have hprefix : ∀ (n G : ℕ), 2 ≤ n+G →
      totalVariation (twistedLaw k (parryParameter k) n G)
        (referenceLaw k (parryParameter k) n π) ≤
        2 * (n+G:ℕ) * (3/4:ℝ)^(G/3) + Real.goldenRatio^(2-((n+G:ℕ):ℤ)) := by
    intro n G hL
    have hp : 0 < parryParameter k := by linarith [hr.1]
    have hpoint (s t : State k) : |(Q^G) s t - π t| ≤ (3/4:ℝ)^(G/3) := by
      have h := (total_variation_eq_sup_event_gap (fun t => (Q^G) s t) π
        ((hrows _ _).trans hπsum.symm)).2
        (Set.mem_range.mpr ⟨{t},rfl⟩)
      simp only [Finset.sum_singleton] at h
      exact h.trans (hmix G s)
    exact (complete_prefix_comparison_of_estimates k hk (parryParameter k) hp n G hL
      hrow π hπ hπsum hflip ((3/4:ℝ)^(G/3)) (by positivity) hpoint).trans
      (add_le_add le_rfl (parry_suffix_tail k hk (n+G)))
  refine ⟨hmix,hprefix,?_⟩
  intro R G hR hG f
  have hp : 0 < parryParameter k := by linarith [hr.1]
  have hL : 2 ≤ R+1+G := by omega
  have hpaths : ∀ (m : ℕ) (s : State k),
      (∑ v : Fin m → State k, pathWeight k (parryParameter k) m s v) = 1 := by
    intro m
    induction m with
    | zero => intro s; simp [pathWeight]
    | succ m ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m+1) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight,
        Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum,ih,mul_one]
      exact hrow s
  have href : (∑ v, referenceLaw k (parryParameter k) (R+1) π v) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [referenceLaw]
    simp_rw [← Finset.mul_sum,hpaths,mul_one]
    exact hπsum
  have htw : (∑ v, twistedLaw k (parryParameter k) (R+1) G v) = 1 := by
    simp only [twistedLaw, ← Finset.sum_div]
    rw [Fintype.sum_prod_type, twisted_prefix_total_mass]
    exact div_self (loop_mass_pos k hk (parryParameter k) hp (R+1+G) hL).ne'
  have hevent := (total_variation_eq_sup_event_gap
    (twistedLaw k (parryParameter k) (R+1) G)
    (referenceLaw k (parryParameter k) (R+1) π) (htw.trans href.symm)).2
    (Set.mem_range.mpr ⟨Finset.univ.filter (fun v => prefixRuleDefect f v),rfl⟩)
  exact hevent.trans (hprefix (R+1) G hL)

#print axioms parry_mixing_and_complete_prefix
end D5.S3.TotalVariation.ParryTwistedComparison
