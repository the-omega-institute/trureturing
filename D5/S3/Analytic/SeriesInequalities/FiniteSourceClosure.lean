/- GID: D5/S3/Analytic/SeriesInequalities/FiniteSourceClosure
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/FiniteSourceClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual recursive images are norm closed; finite-source closures have vanishing tails. -/

import D5.S3.Analytic.SeriesInequalities.FiniteSourceCriticalTail
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Sequences

open scoped BigOperators ENNReal
open Filter Topology Finset

set_option autoImplicit false
set_option maxRecDepth 2000

namespace D5.S3.Analytic.SeriesInequalities.FiniteSourceClosure

open FiniteSourceCriticalTail

/-- Weighted coordinates identify the critical array space with bounded arrays. -/
abbrev WeightedArray (K : Type*) [NormedAddCommGroup K] := lp (fun _ : ℕ × ℕ => K) ∞

/-- Actual recursive outputs, represented in weighted coordinates. -/
def actualImage {K : Type*} [RCLike K] (A ρ : ℝ) : Set (WeightedArray K) :=
  {U | ∃ a : ℕ → K, (∀ n, ‖a n‖ ≤ A) ∧
    ∀ n k, U (n, k) = (ρ ^ (n + k)) • extension a n k}

/-- Finite sources are truncated boundaries, with their full recursive outputs retained. -/
def finiteSourceImage {K : Type*} [RCLike K] (A ρ : ℝ) : Set (WeightedArray K) :=
  {U | ∃ a : ℕ → K, (∀ n, ‖a n‖ ≤ A) ∧
    (∃ M : ℕ, ∀ n, M < n → a n = 0) ∧
    ∀ n k, U (n, k) = (ρ ^ (n + k)) • extension a n k}

/-- The supremum of the norms of weighted coordinates on an antidiagonal tail. -/
noncomputable def tail {K : Type*} [NormedAddCommGroup K]
    (U : WeightedArray K) (L : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ‖U (n, k)‖}

/-- Weighted arrays whose antidiagonal tail suprema converge to zero. -/
def vanishingTails {K : Type*} [NormedAddCommGroup K] : Set (WeightedArray K) :=
  {U | Tendsto (tail U) atTop (𝓝 0)}

/-- At the critical weight every bounded source has a bounded weighted output.
The full actual image is norm closed, and the norm closure of finite-source
outputs belongs to that image and has vanishing antidiagonal tails. -/
theorem critical_recursive_image_closure {K : Type*} [RCLike K]
    (A ρ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hcrit : A * ρ = (1 - ρ) ^ 2) :
    (∀ a : ℕ → K, (∀ n, ‖a n‖ ≤ A) →
      ∃ U : WeightedArray K, ‖U‖ ≤ A ∧
        ∀ n k, U (n, k) = (ρ ^ (n + k)) • extension a n k) ∧
    IsClosed (actualImage (K := K) A ρ) ∧
    closure (finiteSourceImage (K := K) A ρ) ⊆
      actualImage A ρ ∩ vanishingTails := by
  classical
  have hρpow (j : ℕ) : 0 < ρ ^ j := pow_pos hρ j
  have hnorm (t : K) (j : ℕ) : ‖(ρ ^ j) • t‖ = ρ ^ j * ‖t‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hρpow j).le]
  have hbound (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ A) :
      ∀ k n, ‖extension a n k‖ * ρ ^ k ≤ A := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n
      cases k with
      | zero => simpa [extension] using ha n
      | succ k =>
        have hmass : ρ + A * ∑ i ∈ range (k + 1), ρ ^ (i + 1) ≤ 1 := by
          have hs : (∑ i ∈ range (k + 1), ρ ^ (i + 1)) =
              ρ * ∑ i ∈ range (k + 1), ρ ^ i := by
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            rw [pow_succ, mul_comm]
          rw [hs, ← mul_assoc, hcrit]
          have hg := geom_sum_mul_neg ρ (k + 1)
          nlinarith [mul_nonneg (sub_pos.mpr hρ1).le (hρpow (k + 1)).le]
        have hterm (j : Fin (k + 1)) :
            ‖extension a n j * a (k - j)‖ * ρ ^ (k + 1) ≤
              A * (A * ρ ^ (k - j + 1)) := by
          have hexp : ρ ^ (k + 1) = ρ ^ (j : ℕ) * ρ ^ (k - j + 1) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            ‖extension a n j * a (k - j)‖ * ρ ^ (k + 1) ≤
                (‖extension a n j‖ * ‖a (k - j)‖) * ρ ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (hρpow _).le
            _ = (‖extension a n j‖ * ρ ^ (j : ℕ)) *
                (‖a (k - j)‖ * ρ ^ (k - j + 1)) := by rw [hexp]; ring
            _ ≤ A * (A * ρ ^ (k - j + 1)) := by
              gcongr
              · exact ih j j.isLt n
              · exact ha _
        have hsum : (∑ j : Fin (k + 1), ρ ^ (k - j + 1)) =
            ∑ i ∈ range (k + 1), ρ ^ (i + 1) := by
          rw [Fin.sum_univ_eq_sum_range (fun j => ρ ^ (k - j + 1)) (k + 1)]
          simpa using sum_range_reflect (fun i => ρ ^ (i + 1)) (k + 1)
        calc
          ‖extension a n (k + 1)‖ * ρ ^ (k + 1) ≤
              (‖extension a (n + 1) k‖ +
                ∑ j : Fin (k + 1), ‖extension a n j * a (k - j)‖) * ρ ^ (k + 1) := by
            rw [extension]
            apply mul_le_mul_of_nonneg_right _ (hρpow _).le
            exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
          _ = (‖extension a (n + 1) k‖ * ρ ^ k) * ρ +
              ∑ j : Fin (k + 1), ‖extension a n j * a (k - j)‖ * ρ ^ (k + 1) := by
            rw [add_mul, sum_mul, pow_succ]
            ring
          _ ≤ A * ρ + ∑ j : Fin (k + 1), A * (A * ρ ^ (k - j + 1)) := by
            exact add_le_add (mul_le_mul_of_nonneg_right (ih k (by omega) (n + 1)) hρ.le)
              (sum_le_sum fun j hj => hterm j)
          _ = A * (ρ + A * ∑ i ∈ range (k + 1), ρ ^ (i + 1)) := by
            rw [← mul_sum, ← mul_sum, hsum, mul_add]
          _ ≤ A := by nlinarith [hmass]
  have hrepresentation : ∀ a : ℕ → K, (∀ n, ‖a n‖ ≤ A) →
      ∃ U : WeightedArray K, ‖U‖ ≤ A ∧
        ∀ n k, U (n, k) = (ρ ^ (n + k)) • extension a n k := by
    intro a ha
    let f : ℕ × ℕ → K := fun p => (ρ ^ (p.1 + p.2)) • extension a p.1 p.2
    have hf (p : ℕ × ℕ) : ‖f p‖ ≤ A := by
      dsimp [f]
      rw [hnorm, pow_add]
      calc
        ρ ^ p.1 * ρ ^ p.2 * ‖extension a p.1 p.2‖ =
            ρ ^ p.1 * (‖extension a p.1 p.2‖ * ρ ^ p.2) := by ring
        _ ≤ ρ ^ p.1 * A := mul_le_mul_of_nonneg_left (hbound a ha p.2 p.1) (hρpow _).le
        _ ≤ A := by nlinarith [pow_le_one₀ (n := p.1) hρ.le hρ1.le]
    let U : WeightedArray K := ⟨f, memℓp_infty ⟨A, by rintro x ⟨p, rfl⟩; exact hf p⟩⟩
    exact ⟨U, lp.norm_le_of_forall_le hA.le hf, fun _ _ => rfl⟩
  have hcoord (n k : ℕ) : Continuous (fun a : ℕ → K => extension a n k) := by
    induction k using Nat.strong_induction_on generalizing n with
    | h k ih =>
      cases k with
      | zero => simpa [extension] using (continuous_apply n : Continuous (fun a : ℕ → K => a n))
      | succ k =>
        simp only [extension]
        exact (ih k (by omega) (n + 1)).sub
          (continuous_finsetSum _ fun j hj =>
            (ih j j.isLt n).mul (continuous_apply (k - j)))
  let recover : WeightedArray K → ℕ → K := fun U n => (ρ ^ n)⁻¹ • U (n, 0)
  have heval (n k : ℕ) : Continuous (fun U : WeightedArray K => U (n, k)) :=
    (lp.lipschitzWith_one_eval ∞ (n, k)).continuous
  have hrecc : Continuous recover := continuous_pi fun n =>
    (heval n 0).const_smul _
  have hrecovery (a : ℕ → K) (U : WeightedArray K)
      (hU : ∀ n k, U (n, k) = (ρ ^ (n + k)) • extension a n k) : recover U = a := by
    funext n
    dsimp [recover]
    rw [hU]
    simp [extension, smul_smul, (hρpow n).ne']
  have himage : actualImage (K := K) A ρ =
      {U | (∀ n, ‖recover U n‖ ≤ A) ∧
        ∀ n k, U (n, k) = (ρ ^ (n + k)) • extension (recover U) n k} := by
    ext U
    constructor
    · rintro ⟨a, ha, hU⟩
      change (∀ n, ‖recover U n‖ ≤ A) ∧ _
      rw [hrecovery a U hU]
      exact ⟨ha, hU⟩
    · rintro ⟨ha, hU⟩
      exact ⟨recover U, ha, hU⟩
  have hclosed : IsClosed (actualImage (K := K) A ρ) := by
    rw [himage]
    apply IsClosed.inter
    · change IsClosed {U : WeightedArray K | ∀ n, ‖recover U n‖ ≤ A}
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun n => isClosed_le
        ((continuous_apply n).comp hrecc).norm continuous_const
    · change IsClosed {U : WeightedArray K | ∀ n k,
        U (n, k) = (ρ ^ (n + k)) • extension (recover U) n k}
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun n => isClosed_iInter fun k =>
        isClosed_eq (heval n k) (((hcoord n k).comp hrecc).const_smul (ρ ^ (n + k)))
  have htailbdd (U : WeightedArray K) (L : ℕ) : BddAbove
      {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ‖U (n, k)‖} := by
    refine ⟨‖U‖, ?_⟩
    rintro x ⟨n, k, hn, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero U (n, k)
  have htailne (U : WeightedArray K) (L : ℕ) : Set.Nonempty
      {x : ℝ | ∃ n k : ℕ, L ≤ n + k ∧ x = ‖U (n, k)‖} :=
    ⟨‖U (L, 0)‖, L, 0, by omega, rfl⟩
  have htailnonneg (U : WeightedArray K) (L : ℕ) : 0 ≤ tail U L :=
    le_csSup_of_le (htailbdd U L) ⟨L, 0, by omega, rfl⟩ (norm_nonneg _)
  have htailentry (U : WeightedArray K) (L n k : ℕ) (hL : L ≤ n + k) :
      ‖U (n, k)‖ ≤ tail U L := le_csSup (htailbdd U L) ⟨n, k, hL, rfl⟩
  have htailapprox (U V : WeightedArray K) (L : ℕ) :
      tail U L ≤ ‖U - V‖ + tail V L := by
    apply csSup_le (htailne U L)
    rintro x ⟨n, k, hL, rfl⟩
    calc
      ‖U (n, k)‖ ≤ ‖U (n, k) - V (n, k)‖ + ‖V (n, k)‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖U - V‖ + tail V L := add_le_add
        (lp.norm_apply_le_norm ENNReal.top_ne_zero (U - V) (n, k)) (htailentry V L n k hL)
  have htailclosed : IsClosed (vanishingTails (K := K)) := by
    rw [← closure_subset_iff_isClosed]
    intro U hU
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨V, hV, hUV⟩ := Metric.mem_closure_iff.mp hU (ε / 2) (half_pos hε)
    obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp hV (ε / 2) (half_pos hε)
    refine ⟨L, fun l hl => ?_⟩
    have hVl := hL l hl
    rw [dist_eq_norm] at hUV
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (htailnonneg V l)] at hVl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (htailnonneg U l)]
    linarith [htailapprox U V l]
  refine ⟨hrepresentation, hclosed, ?_⟩
  apply closure_minimal _ (hclosed.inter htailclosed)
  rintro U ⟨a, ha, ⟨M, hM⟩, hU⟩
  refine ⟨⟨a, ha, hU⟩, ?_⟩
  have htail : tail U = antidiagonalTail ρ (extension a) := by
    funext L
    unfold tail antidiagonalTail
    congr 1
    ext x
    simp only [hU, hnorm]
  rw [vanishingTails, Set.mem_ofPred_eq, htail]
  exact (finite_source_critical_tail A ρ hA hρ hρ1 hcrit M a ha hM).choose_spec.2.2.2.2

#print axioms critical_recursive_image_closure
end D5.S3.Analytic.SeriesInequalities.FiniteSourceClosure
