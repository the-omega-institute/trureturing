/- GID: D5/S3/ObserverMemory/Prediction/BinaryMixingMemoryDivergence
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/BinaryMixingMemoryDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every bounded finite observer fails below the static error floor at sufficiently small positive mixing. -/

import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace D5.S3.ObserverMemory.Prediction.BinaryMixingMemoryDivergence

noncomputable section
universe u

/-- The old hidden bit emits first; the resulting weighted column then flips with probability r.
The two coordinates refer to hidden bits zero and one, and false denotes report zero. -/
def transfer (p r : ℝ) (v : ℝ × ℝ) (b : Bool) : ℝ × ℝ :=
  let a := if b then 1 - p else p
  let c := if b then p else 1 - p
  ((1-r)*a*v.1 + r*c*v.2, r*a*v.1 + (1-r)*c*v.2)

/-- Unnormalized hidden-state masses after a chronological word, from the uniform prior. -/
def wordVector (p r : ℝ) (w : List Bool) : ℝ × ℝ :=
  w.foldl (transfer p r) (1/2,1/2)

/-- The probability mass of a finite report history. -/
def wordMass (p r : ℝ) (w : List Bool) : ℝ :=
  (wordVector p r w).1 + (wordVector p r w).2

/-- The actual next-zero conditional probability is a ratio of report-history masses. -/
def prediction (p r : ℝ) (w : List Bool) : ℝ :=
  wordMass p r (w ++ [false]) / wordMass p r w

/-- Below the static half-range error, every fixed state bound is excluded throughout a positive
neighborhood of zero mixing. The neighborhood is uniform over all update tables and real readouts.
The natural bound may be zero; the nonempty case is supplied by the initial state. -/
theorem small_mixing_observer_obstruction
    (p ε : ℝ) (hp : 0 < p) (hp' : p < 1/2)
    (hε : 0 < ε) (hε' : ε < 1/2-p) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < min δ (1/2) →
      ∀ (S : Type u) [Fintype S] (s₀ : S) (T₀ T₁ : S → S) (t : S → ℝ),
        Fintype.card S ≤ N → ∃ w : List Bool,
          0 < wordMass p r w ∧ ε < |t (w.foldl (fun s b => if b then T₁ s else T₀ s) s₀) - prediction p r w| := by
  classical
  have prediction_formula (p r : ℝ) (w : List Bool) :
      prediction p r w =
        (p*(wordVector p r w).1+(1-p)*(wordVector p r w).2) /
          ((wordVector p r w).1+(wordVector p r w).2) := by
    unfold prediction wordMass wordVector
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, transfer,
      Bool.false_eq_true, ↓reduceIte]
    congr 1
    ring
  have continuous_prediction (p : ℝ) (hp : 0 < p) (hp' : p < 1/2) :
      ∀ w : List Bool, ContinuousAt (fun r : ℝ => prediction p r w) 0 := by
    have hc : ∀ w : List Bool, Continuous (fun r : ℝ => wordVector p r w) := by
      intro w
      induction w using List.reverseRecOn with
      | nil => exact continuous_const
      | append_singleton w b ih =>
        simp only [wordVector, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
        cases b <;> dsimp [transfer] <;> fun_prop
    have hpos : ∀ w : List Bool, 0 < (wordVector p 0 w).1 ∧ 0 < (wordVector p 0 w).2 := by
      intro w
      induction w using List.reverseRecOn with
      | nil => norm_num [wordVector]
      | append_singleton w b ih =>
        simp only [wordVector, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
        cases b <;> simp only [transfer, Bool.false_eq_true, ↓reduceIte, sub_zero,
          zero_mul, one_mul, add_zero, zero_add]
        · exact ⟨mul_pos hp ih.1, mul_pos (by linarith) ih.2⟩
        · exact ⟨mul_pos (by linarith) ih.1, mul_pos hp ih.2⟩
    intro w
    simp_rw [prediction_formula]
    have h1 : ContinuousAt (fun r : ℝ => (wordVector p r w).1) 0 := ((hc w).fst).continuousAt
    have h2 : ContinuousAt (fun r : ℝ => (wordVector p r w).2) 0 := ((hc w).snd).continuousAt
    exact ((continuousAt_const.mul h1).add (continuousAt_const.mul h2)).div
      (h1.add h2) (ne_of_gt (add_pos (hpos w).1 (hpos w).2))
  have static_vector (p : ℝ) (n k : ℕ) :
      wordVector p 0 (List.replicate n false ++ List.replicate k true) =
        (p^n*(1-p)^k/2, (1-p)^n*p^k/2) := by
    have hf : ∀ (n : ℕ) (b : Bool) (v : ℝ × ℝ),
        (List.replicate n b).foldl (transfer p 0) v =
          ((if b then 1-p else p)^n*v.1, (if b then p else 1-p)^n*v.2) := by
      intro n b v
      induction n generalizing v with
      | zero => simp
      | succ n ih =>
        simp only [List.replicate_succ, List.foldl_cons, ih, transfer]
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, zero_mul, one_mul, add_zero, zero_add]
        all_goals ext <;> dsimp <;> simp only [pow_succ] <;> ring
    simp only [wordVector, List.foldl_append, hf, Bool.false_eq_true, ↓reduceIte]
    ext <;> dsimp <;> ring
  have static_gap (p : ℝ) (hp : 0 < p) (hp' : p < 1/2) (n h : ℕ) :
    prediction p 0 (List.replicate (n+2*h) false ++ List.replicate (n+h) true) -
      prediction p 0 (List.replicate n false ++ List.replicate (n+h) true) =
        (1-2*p)*(1-(p/(1-p))^h)/(1+(p/(1-p))^h) := by
    have hp1 : 0 < 1-p := by linarith
    have ha : 0 < p^n*(1-p)^(n+h)/2+(1-p)^n*p^(n+h)/2 := by positivity
    have hb : 0 < p^(n+2*h)*(1-p)^(n+h)/2+(1-p)^(n+2*h)*p^(n+h)/2 := by positivity
    have hc : 0 < 1+(p/(1-p))^h := by positivity
    simp only [prediction_formula, static_vector]
    field_simp
    simp only [pow_add, show 2*h=h+h by omega, pow_add, div_pow]
    field_simp
    ring
  -- Fixed-word continuity and an exact static gap yield one common neighborhood.
  have hp1 : 0 < 1-p := by linarith
  let a := p/(1-p)
  have ha : 0 < a := div_pos hp hp1
  have ha1 : a < 1 := (div_lt_one hp1).2 (by linarith)
  have hthreshold : 0 < (1-2*p-2*ε)/(1-2*p+2*ε) := by
    apply div_pos <;> linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hthreshold ha1
  let minusWord (n l : ℕ) := List.replicate n false ++ List.replicate (n+m*l) true
  let plusWord (n l : ℕ) := List.replicate (n+2*(m*l)) false ++ List.replicate (n+m*l) true
  have hgap : ∀ n l : ℕ, 0 < l →
      2*ε < prediction p 0 (plusWord n l) - prediction p 0 (minusWord n l) := by
    intro n l hl
    dsimp only [plusWord, minusWord]
    rw [static_gap p hp hp' n (m*l)]
    have hpow : a^(m*l) < (1-2*p-2*ε)/(1-2*p+2*ε) :=
      lt_of_le_of_lt (pow_le_pow_of_le_one ha.le ha1.le (by nlinarith)) hm
    have hd : 0 < 1-2*p+2*ε := by linarith
    have hmul := (lt_div_iff₀ hd).1 hpow
    apply (lt_div_iff₀ (by positivity : 0 < 1+a^(m*l))).2
    nlinarith
  have hevent : ∀ᶠ r : ℝ in 𝓝 0, ∀ i : Fin (N+1) × Fin (N+1),
      0 < i.2.val → 2*ε < prediction p r (plusWord i.1.val i.2.val) -
        prediction p r (minusWord i.1.val i.2.val) := by
    apply Filter.eventually_all.2
    intro i
    by_cases hi : 0 < i.2.val
    · have hc := (continuous_prediction p hp hp' (plusWord i.1.val i.2.val)).sub
        (continuous_prediction p hp hp' (minusWord i.1.val i.2.val))
      exact (hc.tendsto.eventually_const_lt (hgap _ _ hi)).mono (fun r hr _ => hr)
    · exact Filter.Eventually.of_forall (fun r h => False.elim (hi h))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hevent
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ S _ s₀ T₀ T₁ t hcard
  have hmassPos : ∀ w : List Bool, 0 < wordMass p r w := by
    have hr1 : 0 < 1-r := by have := lt_of_lt_of_le hrδ (min_le_right _ _); linarith
    have hv : ∀ w : List Bool, 0 < (wordVector p r w).1 ∧ 0 < (wordVector p r w).2 := by
      intro w
      induction w using List.reverseRecOn with
      | nil => norm_num [wordVector]
      | append_singleton w b ih =>
        simp only [wordVector, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
        rcases ih with ⟨hleft, hright⟩
        cases b <;> dsimp [transfer]
        all_goals constructor <;> positivity
    intro w
    exact add_pos (hv w).1 (hv w).2
  have hdist : dist r 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact lt_of_lt_of_le hrδ (min_le_left _ _)
  -- Every observer supplies one of the finitely many preselected word pairs.
  obtain ⟨n, l, hl, hnl, hperiod⟩ :=
    D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic
      T₀ t s₀
  have hrepeat : ∀ k : ℕ, (T₀^[n+k*l]) s₀ = (T₀^[n]) s₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show n+(k+1)*l=(n+k*l)+l by ring]
      exact ((hperiod (n+k*l) (by omega)).1).trans ih
  have hzeros : ∀ k : ℕ, ∀ s : S,
      (List.replicate k false).foldl (fun s b => if b then T₁ s else T₀ s) s = (T₀^[k]) s := by
    intro k s
    induction k generalizing s with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, ih, Function.iterate_succ_apply]
  have heq : (plusWord n l).foldl (fun s b => if b then T₁ s else T₀ s) s₀ =
      (minusWord n l).foldl (fun s b => if b then T₁ s else T₀ s) s₀ := by
    dsimp only [plusWord, minusWord]
    simp only [List.foldl_append, hzeros]
    rw [show n+2*(m*l)=n+(2*m)*l by ring, hrepeat]
  have hg := hball hdist (⟨n, by omega⟩, ⟨l, by omega⟩) hl
  by_contra! hbad
  have hmerr := hbad (minusWord n l) (hmassPos _)
  have hperr := hbad (plusWord n l) (hmassPos _)
  rw [heq] at hperr
  have hplo := (abs_le.1 hperr).1
  have hmhi := (abs_le.1 hmerr).2
  dsimp only at hg
  linarith

end

end D5.S3.ObserverMemory.Prediction.BinaryMixingMemoryDivergence
