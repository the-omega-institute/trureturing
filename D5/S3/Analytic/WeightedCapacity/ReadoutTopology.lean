/- GID: D5/S3/Analytic/WeightedCapacity/ReadoutTopology
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/ReadoutTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite total capacity characterizes continuity and unique real extension of the dyadic readout in the rational probe topology. -/
import D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences
import Mathlib.Topology.Sequences
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
namespace D5.S3.Analytic.WeightedCapacity.ReadoutTopology
open Set Filter
open scoped BigOperators Topology
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
open D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences

/-- The finite state whose every coordinate is zero. -/
noncomputable def zeroState (A : ℕ → ℕ) : B A :=
  ⟨fun n => ⟨0, Nat.zero_lt_succ _⟩, by simpa [Function.support] using Set.finite_empty⟩

/-- Finite total capacity characterizes continuity and a unique continuous real extension;
infinite mass gives discontinuity everywhere, and infinitely many active coordinates exclude isolated points. -/
set_option maxHeartbeats 1600000 in
theorem result (A : ℕ → ℕ) :
  (((M A < ⊤) ↔ @ContinuousAt (B A) ℝ (tauPlus A) inferInstance readout (zeroState A)) ∧
    ((M A < ⊤) ↔ @Continuous (B A) ℝ (tauPlus A) inferInstance readout) ∧
    ((M A < ⊤) ↔ ∃ F : X A → ℝ, Continuous F ∧ ∀ u : B A, F u.val = readout u) ∧
    ((M A < ⊤) → Continuous (fun x : X A => (S x).toReal) ∧
      (∀ u : B A, (S u.val).toReal = readout u) ∧
      (∀ F : X A → ℝ, Continuous F → (∀ u : B A, F u.val = readout u) →
        F = fun x => (S x).toReal)) ∧
    ((M A = ⊤) → ∀ u : B A, ¬ @ContinuousAt (B A) ℝ (tauPlus A) inferInstance readout u)) ∧
  (∀ (_ : {n | 0 < A n}.Infinite) (u : B A) (U : Set (B A)),
    U ∈ @nhds _ (tauPlus A) u → ∃ w ∈ U, w ≠ u) := by
  classical
  let fill (A : ℕ → ℕ) (s : Finset ℕ) : B A := by
    classical
    refine ⟨fun n => if n ∈ s then ⟨A n, Nat.lt_succ_self _⟩ else ⟨0, Nat.zero_lt_succ _⟩, ?_⟩
    apply s.finite_toSet.subset
    intro n hn
    by_contra h
    change n ∉ s at h
    exact hn (by simp [h])

  let realSum {A : ℕ → ℕ} (x : X A) : ℝ :=
    ∑' n, ((x n : ℕ) : ℝ) / 2 ^ n

  let truncate {A : ℕ → ℕ} (x : X A) (K : ℕ) : B A := by
    classical
    refine ⟨fun n => if n < K then x n else ⟨0, Nat.zero_lt_succ _⟩, ?_⟩
    apply (Finset.range K).finite_toSet.subset
    intro n hn
    apply Finset.mem_range.mpr
    by_contra h
    exact hn (by simp [h])

  let paste {A : ℕ → ℕ} (u v : B A) (N : ℕ) : B A := by
    classical
    refine ⟨fun n => if n < N then u.val n else v.val n, ?_⟩
    apply (u.property.union v.property).subset
    intro n hn
    by_cases h : n < N
    · left; simpa [h] using hn
    · right; simpa [h] using hn

  have readout_fill (A : ℕ → ℕ) (s : Finset ℕ) :
      readout (fill A s) = ∑ n ∈ s, (A n : ℝ) / 2 ^ n := by
    classical
    have hs : (fill A s).property.toFinset ⊆ s := by
      intro n hn
      by_contra h
      have hne : ((fill A s).val n : ℕ) ≠ 0 := by simpa using hn
      exact hne (by simp [fill, h])
    unfold readout
    rw [Finset.sum_subset hs (by
      intro n hn hnot
      have hz : ((fill A s).val n : ℕ) = 0 := by simpa using hnot
      simp [hz])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [fill, hn]

  have chi_fill (A : ℕ → ℕ) (s : Finset ℕ) (r : ℕ → ℚ) :
      chi r (fill A s) = (((∑ n ∈ s, r n * (A n : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
    classical
    have hs : (fill A s).property.toFinset ⊆ s := by
      intro n hn
      by_contra h
      have hne : ((fill A s).val n : ℕ) ≠ 0 := by simpa using hn
      exact hne (by simp [fill, h])
    unfold chi
    congr 2
    rw [Finset.sum_subset hs (by
      intro n hn hnot
      have hz : ((fill A s).val n : ℕ) = 0 := by simpa using hnot
      simp [hz])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [fill, hn]

  have large_invisible_tail (A : ℕ → ℕ) (hM : M A = ⊤)
      (N m : ℕ) (r : Fin m → ℕ → ℚ) (ε : ℝ) (hε : 0 < ε) :
      ∃ v : B A, (∀ n < N, (v.val n : ℕ) = 0) ∧ 1 ≤ readout v ∧
        ∀ a, dist (chi (r a) v) 0 < ε := by
    classical
    have hmono : Monotone (fun k => prefixSum k A) := by
      intro i j hij
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) (by intros; positivity)
    have hunbounded (R : ℝ) : ∃ k, R < prefixSum k A := by
      by_contra h
      push Not at h
      have hb : M A ≤ ENNReal.ofReal R :=
        iSup_le fun k => ENNReal.ofReal_le_ofReal (h (k + 1))
      rw [hM] at hb
      exact (ne_of_lt ENNReal.ofReal_lt_top) (top_le_iff.mp hb)
    have hnext (k : ℕ) : ∃ l, k < l ∧ prefixSum k A + 1 < prefixSum l A := by
      obtain ⟨l, hl⟩ := hunbounded (prefixSum k A + 1)
      refine ⟨l, ?_, hl⟩
      by_contra h
      have hh := hmono (show l ≤ k by omega)
      linarith
    choose next hnext using hnext
    let f : ℕ → ℕ := fun j => next^[j] N
    have hfs (j : ℕ) : f (j + 1) = next (f j) := Function.iterate_succ_apply' _ _ _
    have hfm : StrictMono f := strictMono_nat_of_lt_succ (fun j => by
      rw [hfs]; exact (hnext _).1)
    have hfN (j : ℕ) : N ≤ f j := by
      have := hfm.monotone (Nat.zero_le j)
      simpa [f] using this
    have hgap (i j : ℕ) (hij : i < j) : 1 ≤ prefixSum (f j) A - prefixSum (f i) A := by
      have hstep := (hnext (f i)).2
      rw [← hfs] at hstep
      have hh := hmono (hfm.monotone (show i + 1 ≤ j by omega))
      linarith
    let t : ℕ → Fin m → AddCircle (1 : ℝ) :=
      fun j a => chi (r a) (fill A (Finset.range (f j)))
    obtain ⟨z, g, hgm, hlim⟩ := CompactSpace.tendsto_subseq t
    have hall : ∀ᶠ k in atTop, ∀ a : Fin m, dist (t (g k) a) (z a) < ε / 2 := by
      apply Filter.eventually_all.mpr
      intro a
      have ha : Tendsto (fun k => t (g k) a) atTop (𝓝 (z a)) :=
        (tendsto_pi_nhds.mp hlim) a
      exact ha (Metric.ball_mem_nhds _ (by linarith))
    obtain ⟨K, hK⟩ := hall.exists_forall_of_atTop
    let i := g K
    let j := g (K + 1)
    have hij : i < j := hgm (Nat.lt_succ_self _)
    have hfi : f i ≤ f j := (hfm hij).le
    let v := fill A (Finset.Ico (f i) (f j))
    refine ⟨v, ?_, ?_, ?_⟩
    · intro n hn
      have hnot : n ∉ Finset.Ico (f i) (f j) := by
        simp only [Finset.mem_Ico, not_and]
        intro hni
        have := hfN i
        omega
      simp only [v, fill, if_neg hnot]
    · rw [readout_fill, Finset.sum_Ico_eq_sub _ hfi]
      exact hgap i j hij
    · intro a
      have hchar : chi (r a) v = t j a - t i a := by
        rw [chi_fill, Finset.sum_Ico_eq_sub _ hfi]
        dsimp [t]
        rw [chi_fill, chi_fill, Rat.cast_sub, AddCircle.coe_sub]
      rw [hchar]
      have hleft := hK K (le_refl _) a
      have hright := hK (K + 1) (by omega) a
      have hdist := dist_triangle (t j a) (z a) (t i a)
      rw [dist_comm (z a) (t i a)] at hdist
      rw [dist_eq_norm, sub_zero, ← dist_eq_norm]
      dsimp [i, j] at *
      linarith

  have summable_capacity (A : ℕ → ℕ) (hM : M A < ⊤) :
      Summable (fun n => (A n : ℝ) / 2 ^ n) := by
    apply summable_of_sum_range_le (fun _ => by positivity) (c := (M A).toReal)
    intro k
    have hb : ENNReal.ofReal (prefixSum k A) ≤ M A := by
      cases k with
      | zero => simp [prefixSum]
      | succ k => exact le_iSup (fun N => ENNReal.ofReal (P N (fun n => ⟨A n, Nat.lt_succ_self _⟩))) k
    have ht := ENNReal.toReal_mono hM.ne hb
    rw [ENNReal.toReal_ofReal (show 0 ≤ prefixSum k A by
      unfold prefixSum; positivity)] at ht
    exact ht

  have continuous_realSum (A : ℕ → ℕ) (hM : M A < ⊤) :
      Continuous (@realSum A) := by
    apply continuous_tsum
    · intro n
      exact ((continuous_of_discreteTopology : Continuous (fun z : Fin (A n + 1) =>
        ((z : ℕ) : ℝ))).comp (continuous_apply n)).div_const _
    · exact summable_capacity A hM
    · intro n x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (Nat.le_of_lt_succ (x n).isLt)

  have realSum_readout (A : ℕ → ℕ) (u : B A) : realSum u.val = readout u := by
    classical
    apply tsum_eq_sum
    intro n hn
    have hz : (u.val n : ℕ) = 0 := by simpa using hn
    simp [hz]

  have finite_states_dense (A : ℕ → ℕ) : DenseRange (Subtype.val : B A → X A) := by
    intro x
    have hlim : Tendsto (fun K => (truncate x K).val) atTop (𝓝 x) := by
      apply tendsto_pi_nhds.mpr
      intro n
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_ge_atTop (n + 1)] with K hK
      simp [truncate, show n < K by omega]
    apply mem_closure_of_tendsto hlim
    exact Filter.Eventually.of_forall (fun K => ⟨truncate x K, rfl⟩)

  have S_eq_realSum (A : ℕ → ℕ) (hM : M A < ⊤) (x : X A) :
      S x = ENNReal.ofReal (realSum x) := by
    have hsum : Summable (fun n => ((x n : ℕ) : ℝ) / 2 ^ n) := by
      apply (summable_capacity A hM).of_nonneg_of_le (fun _ => by positivity)
      intro n
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.le_of_lt_succ (x n).isLt
    rw [realSum, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum,
      ENNReal.tsum_eq_iSup_nat]
    apply le_antisymm
    · apply iSup_le
      intro N
      have he : ENNReal.ofReal (P N x) =
          ∑ n ∈ Finset.range (N + 1), ENNReal.ofReal (((x n : ℕ) : ℝ) / 2 ^ n) :=
        by
          unfold P prefixSum
          exact ENNReal.ofReal_sum_of_nonneg (by intros; positivity)
      rw [he]
      exact le_iSup (fun i => ∑ n ∈ Finset.range i,
        ENNReal.ofReal (((x n : ℕ) : ℝ) / 2 ^ n)) (N + 1)
    · apply iSup_le
      intro N
      cases N with
      | zero => simp
      | succ N =>
        rw [← ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
        exact le_iSup (fun N => ENNReal.ofReal (P N x)) N

  have finite_extension (A : ℕ → ℕ) (hM : M A < ⊤) :
      Continuous (fun x : X A => (S x).toReal) ∧
      (∀ u : B A, (S u.val).toReal = readout u) ∧
      (∀ F : X A → ℝ, Continuous F → (∀ u : B A, F u.val = readout u) →
        F = fun x => (S x).toReal) := by
    have heq : (fun x : X A => (S x).toReal) = realSum := by
      funext x
      rw [S_eq_realSum A hM x, ENNReal.toReal_ofReal (by unfold realSum; positivity)]
    have hpoint (x : X A) : (S x).toReal = realSum x := congrFun heq x
    simp only [hpoint]
    refine ⟨continuous_realSum A hM, realSum_readout A, ?_⟩
    intro F hF hread
    apply (finite_states_dense A).equalizer hF (continuous_realSum A hM)
    funext u
    exact (hread u).trans (realSum_readout A u).symm

  have paste_evaluation (A : ℕ → ℕ) (u v : B A) (N : ℕ)
      (hu : ∀ n, N ≤ n → (u.val n : ℕ) = 0)
      (hv : ∀ n < N, (v.val n : ℕ) = 0) :
      readout (paste u v N) = readout u + readout v ∧
      ∀ r : ℕ → ℚ, chi r (paste u v N) = chi r u + chi r v := by
    classical
    let s := u.property.toFinset ∪ v.property.toFinset
    have hcoords (n : ℕ) : ((paste u v N).val n : ℕ) = (u.val n : ℕ) + (v.val n : ℕ) := by
      by_cases h : n < N
      · simp [paste, h, hv n h]
      · simp [paste, h, hu n (by omega)]
    have hs (w : B A) (hw : ∀ n, (w.val n : ℕ) ≠ 0 → n ∈ s) :
        w.property.toFinset ⊆ s := by intro n hn; exact hw n (by simpa using hn)
    have huS : u.property.toFinset ⊆ s := Finset.subset_union_left
    have hvS : v.property.toFinset ⊆ s := Finset.subset_union_right
    have hwS : (paste u v N).property.toFinset ⊆ s := by
      apply hs
      intro n hn
      by_cases h : (u.val n : ℕ) = 0
      · apply hvS
        have hvn : (v.val n : ℕ) ≠ 0 := by rw [hcoords, h, zero_add] at hn; exact hn
        simpa using hvn
      · apply huS; simpa using h
    have hevalR (w : B A) (hw : w.property.toFinset ⊆ s) :
        readout w = ∑ n ∈ s, ((w.val n : ℕ) : ℝ) / 2 ^ n := by
      apply Finset.sum_subset hw
      intro n _ hn
      have hz : (w.val n : ℕ) = 0 := by simpa using hn
      simp [hz]
    have hevalQ (w : B A) (hw : w.property.toFinset ⊆ s) (r : ℕ → ℚ) :
        chi r w = (((∑ n ∈ s, r n * ((w.val n : ℕ) : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
      unfold chi
      congr 2
      apply Finset.sum_subset hw
      intro n _ hn
      have hz : (w.val n : ℕ) = 0 := by simpa using hn
      simp [hz]
    constructor
    · rw [hevalR _ hwS, hevalR _ huS, hevalR _ hvS, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [hcoords, Nat.cast_add, add_div]
    · intro r
      rw [hevalQ _ hwS, hevalQ _ huS, hevalQ _ hvS, ← AddCircle.coe_add, ← Rat.cast_add,
        ← Finset.sum_add_distrib]
      congr 2
      apply Finset.sum_congr rfl
      intro n _
      rw [hcoords, Nat.cast_add, mul_add]

  have every_finite_observation_neighborhood (A : ℕ → ℕ) (hM : M A = ⊤)
      (u : B A) (I : Finset ℕ) (m : ℕ) (r : Fin m → ℕ → ℚ)
      (ε : ℝ) (hε : 0 < ε) :
      ∃ w : B A, (∀ n ∈ I, w.val n = u.val n) ∧
        1 ≤ readout w - readout u ∧
        ∀ a, dist (chi (r a) w) (chi (r a) u) < ε := by
    classical
    let N := max (I.sup id + 1) (u.property.toFinset.sup id + 1)
    have hu (n : ℕ) (hn : N ≤ n) : (u.val n : ℕ) = 0 := by
      by_contra h
      have hm : n ∈ u.property.toFinset := by simpa using h
      have hb := Finset.le_sup (f := id) hm
      dsimp only [id] at hb
      dsimp [N] at hn
      omega
    obtain ⟨v, hv, hread, hchar⟩ := large_invisible_tail A hM N m r ε hε
    let w := paste u v N
    have he := paste_evaluation A u v N hu hv
    refine ⟨w, ?_, ?_, ?_⟩
    · intro n hn
      have hb := Finset.le_sup (f := id) hn
      dsimp only [id] at hb
      have hnN : n < N := by dsimp [N]; omega
      simp [w, paste, hnN]
    · change 1 ≤ readout (paste u v N) - readout u
      rw [he.1]
      linarith
    · intro a
      change dist (chi (r a) (paste u v N)) (chi (r a) u) < ε
      rw [he.2, dist_eq_norm, add_sub_cancel_left]
      simpa [dist_eq_norm] using hchar a

  have neighborhood_basis (A : ℕ → ℕ) (u : B A) (s : Set (B A))
      (hs : s ∈ @nhds _ (tauPlus A) u) :
      ∃ (I : Finset ℕ) (m : ℕ) (r : Fin m → ℕ → ℚ) (ε : ℝ), 0 < ε ∧
        ∀ w : B A, (∀ n ∈ I, w.val n = u.val n) →
          (∀ a, dist (chi (r a) w) (chi (r a) u) < ε) → w ∈ s := by
    classical
    unfold tauPlus at hs
    rw [@nhds_inf (B A) (TopologicalSpace.induced (@psi A) inferInstance)
      (⨅ r : ℕ → ℚ, TopologicalSpace.induced (@chi A r) inferInstance) u] at hs
    obtain ⟨s₁, hs₁, s₂, hs₂, hsub⟩ := Filter.mem_inf_iff_superset.mp hs
    rw [nhds_induced (@psi A) u] at hs₁
    obtain ⟨o, ho, hos⟩ := Filter.mem_comap.mp hs₁
    rw [nhds_pi, Filter.mem_pi'] at ho
    obtain ⟨I, t, ht, hto⟩ := ho
    rw [@nhds_iInf (B A) (ℕ → ℚ)
      (fun r => TopologicalSpace.induced (@chi A r) inferInstance) u] at hs₂
    obtain ⟨R, hR⟩ := (Filter.mem_iInf_finite s₂).mp hs₂
    obtain ⟨sets, hsets, heq⟩ := Filter.mem_iInf_finset.mp hR
    have hr (a : R) : ∃ δ : ℝ, 0 < δ ∧
        ∀ w : B A, dist (chi a.val w) (chi a.val u) < δ → w ∈ sets a.val := by
      have ha := hsets a.val a.property
      rw [nhds_induced (@chi A a.val) u] at ha
      obtain ⟨o, ho, hos⟩ := Filter.mem_comap.mp ha
      obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp ho
      exact ⟨δ, hδ, fun w hw => hos (hb hw)⟩
    choose δ hδpos hδ using hr
    let ds : Finset ℝ := insert 1 (Finset.univ.image δ)
    have hds : ds.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
    let ε := ds.min' hds
    have hε : 0 < ε := by
      change 0 < ds.min' hds
      have hm := Finset.min'_mem ds hds
      rcases Finset.mem_insert.mp hm with h | h
      · rw [h]; norm_num
      · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
        rw [← ha]
        exact hδpos a
    have hεδ (a : R) : ε ≤ δ a :=
      Finset.min'_le ds _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
    let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
    refine ⟨I, Fintype.card R, fun a => (e a).val, ε, hε, ?_⟩
    intro w hw hchars
    apply hsub
    constructor
    · apply hos
      apply hto
      intro n hn
      have hp : psi w n = psi u n := by simp [psi, hw n hn]
      rw [hp]
      exact mem_of_mem_nhds (ht n)
    · rw [heq]
      simp only [Set.mem_iInter]
      intro r hrR
      let a : R := ⟨r, hrR⟩
      apply hδ a w
      have hc := hchars (e.symm a)
      simpa using lt_of_lt_of_le hc (hεδ a)

  have infinite_mass_nowhere_continuous (A : ℕ → ℕ) (hM : M A = ⊤) (u : B A) :
      ¬ @ContinuousAt (B A) ℝ (tauPlus A) inferInstance readout u := by
    intro h
    have hs : {w : B A | dist (readout w) (readout u) < (1 / 2 : ℝ)} ∈
        @nhds _ (tauPlus A) u := h (Metric.ball_mem_nhds _ (by norm_num))
    obtain ⟨I, m, r, ε, hε, hb⟩ := neighborhood_basis A u _ hs
    obtain ⟨w, hw, hread, hchars⟩ :=
      every_finite_observation_neighborhood A hM u I m r ε hε
    have hh := hb w hw hchars
    change dist (readout w) (readout u) < (1 / 2 : ℝ) at hh
    rw [Real.dist_eq, abs_of_nonneg (by linarith)] at hh
    linarith

  have continuous_coordinates (A : ℕ → ℕ) :
      @Continuous (B A) (X A) (tauPlus A) inferInstance Subtype.val := by
    letI : TopologicalSpace (B A) := tauPlus A
    apply continuous_pi
    intro n
    let r : ℕ → ℚ := fun m => if m = n then 1 / ((A n : ℚ) + 1) else 0
    let e : Fin (A n + 1) → AddCircle (1 : ℝ) :=
      fun m => ((m : ℝ) / ((A n : ℝ) + 1) : ℝ)
    have he (w : B A) : chi r w = e (w.val n) := by
      have hsum : (∑ m ∈ w.property.toFinset, r m * ((w.val m : ℕ) : ℚ)) =
          ((w.val n : ℕ) : ℚ) / ((A n : ℚ) + 1) := by
        by_cases hn : n ∈ w.property.toFinset
        · rw [Finset.sum_eq_single n]
          · simp [r, div_eq_mul_inv, mul_comm]
          · intro m hm hmn; simp [r, hmn]
          · exact fun h => (h hn).elim
        · have hz : (w.val n : ℕ) = 0 := by simpa using hn
          simp [r, hz, hn]
      simp only [chi, hsum, e]
      push_cast
      rfl
    have hei : Function.Injective e := by
      intro a b hab
      have hpos : (0 : ℝ) < (A n : ℝ) + 1 := by positivity
      have hin (m : Fin (A n + 1)) :
          (m : ℝ) / ((A n : ℝ) + 1) ∈ Ico (0 : ℝ) (0 + 1) := by
        constructor
        · positivity
        · rw [div_lt_iff₀ hpos]
          have hm : (m : ℝ) < (A n : ℝ) + 1 := by exact_mod_cast m.isLt
          simpa using hm
      have hab' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hin a) (hin b)).mp hab
      have hv : (a : ℝ) = (b : ℝ) := (div_left_inj' (ne_of_gt hpos)).mp hab'
      apply Fin.ext
      exact_mod_cast hv
    have hemb : Topology.IsEmbedding e :=
      (continuous_of_discreteTopology.isClosedEmbedding hei).isEmbedding
    apply hemb.continuous_iff.mpr
    have hc : Continuous (chi r : B A → AddCircle (1 : ℝ)) :=
      continuous_iff_le_induced.mpr (inf_le_right.trans (iInf_le _ r))
    exact hc.congr he

  have readout_dichotomy (A : ℕ → ℕ) :
      ((M A < ⊤) ↔ @ContinuousAt (B A) ℝ (tauPlus A) inferInstance readout (zeroState A)) ∧
      ((M A < ⊤) ↔ @Continuous (B A) ℝ (tauPlus A) inferInstance readout) ∧
      ((M A < ⊤) ↔ ∃ F : X A → ℝ, Continuous F ∧ ∀ u : B A, F u.val = readout u) ∧
      ((M A < ⊤) → Continuous (fun x : X A => (S x).toReal) ∧
        (∀ u : B A, (S u.val).toReal = readout u) ∧
        (∀ F : X A → ℝ, Continuous F → (∀ u : B A, F u.val = readout u) →
          F = fun x => (S x).toReal)) ∧
      ((M A = ⊤) → ∀ u : B A, ¬ @ContinuousAt (B A) ℝ (tauPlus A) inferInstance readout u) := by
    letI : TopologicalSpace (B A) := tauPlus A
    have hcont (hM : M A < ⊤) : @Continuous (B A) ℝ (tauPlus A) inferInstance readout := by
      have h := (continuous_realSum A hM).comp (continuous_coordinates A)
      exact h.congr (realSum_readout A)
    have hfinite (u : B A) (h : @ContinuousAt (B A) ℝ (tauPlus A) inferInstance readout u) :
        M A < ⊤ := by
      by_contra hn
      have hM : M A = ⊤ := top_le_iff.mp (le_of_not_gt hn)
      exact infinite_mass_nowhere_continuous A hM u h
    refine ⟨⟨fun h => (hcont h).continuousAt, hfinite _⟩,
      ⟨hcont, fun h => hfinite (zeroState A) h.continuousAt⟩, ?_, finite_extension A,
      fun hM u => infinite_mass_nowhere_continuous A hM u⟩
    constructor
    · intro hM
      exact ⟨realSum, continuous_realSum A hM, realSum_readout A⟩
    · rintro ⟨F, hF, hFread⟩
      have hc := hF.comp (continuous_coordinates A)
      have hc' : @Continuous (B A) ℝ (tauPlus A) inferInstance readout := hc.congr hFread
      exact hfinite (zeroState A) hc'.continuousAt

  have nonzero_invisible_tail (A : ℕ → ℕ) (hA : {n | 0 < A n}.Infinite)
      (N m : ℕ) (r : Fin m → ℕ → ℚ) (ε : ℝ) (hε : 0 < ε) :
      ∃ (v : B A) (n : ℕ), N ≤ n ∧ 0 < (v.val n : ℕ) ∧
        (∀ k < N, (v.val k : ℕ) = 0) ∧ ∀ a, dist (chi (r a) v) 0 < ε := by
    classical
    have hnext (k : ℕ) : ∃ l, k < l ∧ 0 < A l := by
      obtain ⟨l, hl, hkl⟩ := hA.exists_gt k
      exact ⟨l, hkl, hl⟩
    choose next hnext using hnext
    let f : ℕ → ℕ := fun j => next^[j] (next N)
    have hfs (j : ℕ) : f (j + 1) = next (f j) := Function.iterate_succ_apply' _ _ _
    have hfm : StrictMono f := strictMono_nat_of_lt_succ (fun j => by
      rw [hfs]; exact (hnext _).1)
    have hfN (j : ℕ) : N ≤ f j := by
      have hh := hfm.monotone (Nat.zero_le j)
      have hn := (hnext N).1
      change next N ≤ f j at hh
      omega
    have hfA (j : ℕ) : 0 < A (f j) := by
      cases j with
      | zero => exact (hnext N).2
      | succ j => rw [hfs]; exact (hnext _).2
    let t : ℕ → Fin m → AddCircle (1 : ℝ) :=
      fun j a => chi (r a) (fill A (Finset.range (f j)))
    obtain ⟨z, g, hgm, hlim⟩ := CompactSpace.tendsto_subseq t
    have hall : ∀ᶠ k in atTop, ∀ a : Fin m, dist (t (g k) a) (z a) < ε / 2 := by
      apply Filter.eventually_all.mpr
      intro a
      have ha : Tendsto (fun k => t (g k) a) atTop (𝓝 (z a)) :=
        (tendsto_pi_nhds.mp hlim) a
      exact ha (Metric.ball_mem_nhds _ (by linarith))
    obtain ⟨K, hK⟩ := hall.exists_forall_of_atTop
    let i := g K
    let j := g (K + 1)
    have hij : i < j := hgm (Nat.lt_succ_self _)
    have hfi : f i < f j := hfm hij
    let v := fill A (Finset.Ico (f i) (f j))
    refine ⟨v, f i, hfN i, ?_, ?_, ?_⟩
    · have hm : f i ∈ Finset.Ico (f i) (f j) := Finset.mem_Ico.mpr ⟨le_refl _, hfi⟩
      simpa only [v, fill, if_pos hm] using hfA i
    · intro n hn
      have hnot : n ∉ Finset.Ico (f i) (f j) := by
        simp only [Finset.mem_Ico, not_and]
        intro hni
        have := hfN i
        omega
      simp only [v, fill, if_neg hnot]
    · intro a
      have hchar : chi (r a) v = t j a - t i a := by
        rw [chi_fill, Finset.sum_Ico_eq_sub _ hfi.le]
        dsimp [t]
        rw [chi_fill, chi_fill, Rat.cast_sub, AddCircle.coe_sub]
      rw [hchar]
      have hleft := hK K (le_refl _) a
      have hright := hK (K + 1) (by omega) a
      have hdist := dist_triangle (t j a) (z a) (t i a)
      rw [dist_comm (z a) (t i a)] at hdist
      rw [dist_eq_norm, sub_zero, ← dist_eq_norm]
      dsimp [i, j] at *
      linarith

  have infinite_active_nonisolated (A : ℕ → ℕ) (hA : {n | 0 < A n}.Infinite)
      (u : B A) (U : Set (B A)) (hU : U ∈ @nhds _ (tauPlus A) u) :
      ∃ w ∈ U, w ≠ u := by
    classical
    obtain ⟨I, m, r, ε, hε, hb⟩ := neighborhood_basis A u U hU
    let N := max (I.sup id + 1) (u.property.toFinset.sup id + 1)
    have hu (n : ℕ) (hn : N ≤ n) : (u.val n : ℕ) = 0 := by
      by_contra h
      have hm : n ∈ u.property.toFinset := by simpa using h
      have hh : n ≤ u.property.toFinset.sup id := Finset.le_sup (f := id) hm
      dsimp [N] at hn
      omega
    obtain ⟨v, n, hn, hvn, hv, hchars⟩ := nonzero_invisible_tail A hA N m r ε hε
    let w := paste u v N
    have he := paste_evaluation A u v N hu hv
    refine ⟨w, hb w ?_ ?_, ?_⟩
    · intro k hk
      have hh : k ≤ I.sup id := Finset.le_sup (f := id) hk
      have hkN : k < N := by dsimp [N]; omega
      simp [w, paste, hkN]
    · intro a
      change dist (chi (r a) (paste u v N)) (chi (r a) u) < ε
      rw [he.2, dist_eq_norm, add_sub_cancel_left]
      simpa [dist_eq_norm] using hchars a
    · intro hw
      have hh := congrArg (fun z : B A => (z.val n : ℕ)) hw
      have hnN : ¬ n < N := by omega
      have hpaste : w.val n = v.val n := by simp [w, paste, hnN]
      change (w.val n : ℕ) = (u.val n : ℕ) at hh
      rw [hpaste, hu n hn] at hh
      exact (Nat.ne_of_gt hvn) hh
  exact ⟨readout_dichotomy A, infinite_active_nonisolated A⟩

end D5.S3.Analytic.WeightedCapacity.ReadoutTopology
