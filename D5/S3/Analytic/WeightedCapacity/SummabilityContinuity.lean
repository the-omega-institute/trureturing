/- GID: D5/S3/Analytic/WeightedCapacity/SummabilityContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/SummabilityContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of finite-support dyadic readout at zero forces finite total capacity. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Constructions
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.SummabilityContinuity

open Set Filter
open scoped Topology BigOperators
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- The finite-support state with every coordinate zero. -/
def zeroState (A : ℕ → ℕ) : B A :=
  ⟨fun n => ⟨0, Nat.zero_lt_succ _⟩, by simp [Function.support]⟩

/-- Finite total capacity is equivalent to continuity of the finite-state readout at zero,
everywhere, and to existence of a continuous real extension to the full product. -/
theorem summable_iff_continuous (A : ℕ → ℕ) :
    (M A ≠ ⊤ ↔ ContinuousAt (readout (A := A)) (zeroState A)) ∧
    (M A ≠ ⊤ ↔ Continuous (readout (A := A))) ∧
    (M A ≠ ⊤ ↔ ∃ F : X A → ℝ, Continuous F ∧ ∀ u : B A, F u.val = readout u) := by
  classical
  let mass : ℕ → ℝ := fun n => (A n : ℝ) / 2 ^ n
  let term : ℕ → X A → ℝ := fun n x => ((x n : ℕ) : ℝ) / 2 ^ n
  have hm0 (n : ℕ) : 0 ≤ mass n := by dsimp [mass]; positivity
  have ht0 (n : ℕ) (x : X A) : 0 ≤ term n x := by dsimp [term]; positivity
  have htbound (n : ℕ) (x : X A) : term n x ≤ mass n := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.le_of_lt_succ (x n).isLt
  have hseries (x : X A) : S x = ∑' n, ENNReal.ofReal (term n x) := by
    rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)]
    unfold S P prefixSum
    congr 1
    funext N
    exact ENNReal.ofReal_sum_of_nonneg (fun n _ => ht0 n x)
  have hread (u : B A) : (∑' n, term n u.val) = readout u := by
    apply tsum_eq_sum
    intro n hn
    have hz : (u.val n : ℕ) = 0 := by simpa using hn
    simp [term, hz]
  have hforward (hM : M A ≠ ⊤) :
      Continuous (fun x : X A => (S x).toReal) ∧
      ∀ u : B A, (S u.val).toReal = readout u := by
    have hms : Summable mass := by
      apply summable_of_sum_range_le hm0 (c := (M A).toReal)
      intro k
      cases k with
      | zero => simpa using ENNReal.toReal_nonneg
      | succ k =>
        apply (ENNReal.ofReal_le_iff_le_toReal hM).mp
        exact le_iSup (fun N => ENNReal.ofReal (P N (fun n =>
          ⟨A n, Nat.lt_succ_self _⟩))) k
    have hts (x : X A) : Summable (fun n => term n x) :=
      Summable.of_nonneg_of_le (fun n => ht0 n x) (fun n => htbound n x) hms
    have hreal (x : X A) : (S x).toReal = ∑' n, term n x := by
      rw [hseries, ← ENNReal.ofReal_tsum_of_nonneg (fun n => ht0 n x) (hts x),
        ENNReal.toReal_ofReal (tsum_nonneg (fun n => ht0 n x))]
    constructor
    · simp_rw [hreal]
      apply continuous_tsum _ hms
      · intro n
        exact ((continuous_of_discreteTopology : Continuous (fun z : Fin (A n + 1) =>
          ((z : ℕ) : ℝ))).comp (continuous_apply n)).div_const _
      · intro n x
        rw [Real.norm_eq_abs, abs_of_nonneg (ht0 n x)]
        exact htbound n x
    · intro u
      rw [hreal, hread]
  have hconverse (hcont : ContinuousAt (readout (A := A)) (zeroState A)) : M A ≠ ⊤ := by
    intro hM
    have htail (I : Finset ℕ) : ∃ F : Finset ℕ, (∀ n ∈ F, n ∉ I) ∧
        1 ≤ ∑ n ∈ F, (A n : ℝ) / 2 ^ n := by
      have hunbounded (R : ℝ) : ∃ k, R < prefixSum k A := by
        by_contra hn
        push Not at hn
        have hh : M A ≤ ENNReal.ofReal R := by
          unfold M
          apply iSup_le
          intro N
          apply ENNReal.ofReal_le_ofReal
          exact hn (N + 1)
        rw [hM] at hh
        exact (ne_of_lt ENNReal.ofReal_lt_top) (top_le_iff.mp hh)
      let mass : ℕ → ℝ := fun n => (A n : ℝ) / 2 ^ n
      obtain ⟨k, hk⟩ := hunbounded (1 + ∑ n ∈ I, mass n)
      let F := (Finset.range k).filter (fun n => n ∉ I)
      refine ⟨F, ?_, ?_⟩
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
      · have hsplit :
        (∑ n ∈ Finset.range k, mass n) =
              (∑ n ∈ F, mass n) + (∑ n ∈ (Finset.range k).filter (fun n => n ∈ I), mass n) := by
          have hs := Finset.sum_filter_add_sum_filter_not (Finset.range k) (fun n => n ∈ I) mass
          simpa [F, add_comm] using hs.symm
        have hinter :
            (∑ n ∈ (Finset.range k).filter (fun n => n ∈ I), mass n) ≤ ∑ n ∈ I, mass n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            exact (Finset.mem_filter.mp hn).2
          · intro n _ _
            dsimp [mass]
            positivity
        have hsum : 1 + ∑ n ∈ I, mass n < ∑ n ∈ Finset.range k, mass n := by
          simpa [prefixSum, mass] using hk
        rw [hsplit] at hsum
        linarith
    have hz : readout (zeroState A) = 0 := by simp [readout, zeroState, Function.support]
    have hn : {u : B A | readout u < 1} ∈ 𝓝 (zeroState A) :=
      hcont (gt_mem_nhds (by simpa [hz] using (zero_lt_one : (0 : ℝ) < 1)))
    obtain ⟨o, ho, hsub⟩ := (mem_nhds_subtype _ _ _).mp hn
    rw [nhds_pi, Filter.mem_pi'] at ho
    obtain ⟨I, t, ht, hto⟩ := ho
    obtain ⟨F, hFI, hF⟩ := htail I
    let v : X A := fun n => if n ∈ F then ⟨A n, Nat.lt_succ_self _⟩
      else ⟨0, Nat.zero_lt_succ _⟩
    have hvfin : (Function.support (fun n => (v n : ℕ))).Finite := by
      apply F.finite_toSet.subset
      intro n hn
      by_contra h
      exact hn (by simp [v, h])
    let u : B A := ⟨v, hvfin⟩
    have hu : u.val ∈ o := by
      apply hto
      intro n hn
      have hnF : n ∉ F := fun hh => hFI n hh hn
      have heq : v n = (zeroState A).val n := by simp [v, hnF, zeroState]
      change v n ∈ t n
      rw [heq]
      exact mem_of_mem_nhds (ht n)
    have hsum : readout u = ∑ n ∈ F, (A n : ℝ) / 2 ^ n := by
      rw [← hread]
      rw [tsum_eq_sum (s := F) (fun n hn => by simp [term, u, v, hn])]
      apply Finset.sum_congr rfl
      intro n hn
      simp [term, u, v, hn]
    have hlt : readout u < 1 := hsub hu
    rw [hsum] at hlt
    exact (not_lt_of_ge hF) hlt
  have hextcont (F : X A → ℝ) (hF : Continuous F)
      (heq : ∀ u : B A, F u.val = readout u) : Continuous (readout (A := A)) := by
    have hh := hF.comp continuous_subtype_val
    exact hh.congr heq
  refine ⟨⟨fun h => ?_, hconverse⟩, ⟨fun h => ?_, fun h => hconverse h.continuousAt⟩,
    ⟨fun h => ?_, ?_⟩⟩
  · exact (hextcont _ (hforward h).1 (hforward h).2).continuousAt
  · exact hextcont _ (hforward h).1 (hforward h).2
  · exact ⟨_, (hforward h).1, (hforward h).2⟩
  · rintro ⟨F, hF, heq⟩
    exact hconverse (hextcont F hF heq).continuousAt

#print axioms summable_iff_continuous

end D5.S3.Analytic.WeightedCapacity.SummabilityContinuity
