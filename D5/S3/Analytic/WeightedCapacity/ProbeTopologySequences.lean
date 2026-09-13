/- GID: D5/S3/Analytic/WeightedCapacity/ProbeTopologySequences
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/ProbeTopologySequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sequences of finite capacity states converge in the rational probe topology exactly when eventually equal to their limit. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Finsupp.BigOperators

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences

open DyadicTailFilling Set Filter
open scoped Topology BigOperators

/-- The circle character associated with a total rational coefficient sequence. -/
noncomputable def chi {A : ℕ → ℕ} (r : ℕ → ℚ) (u : B A) : AddCircle (1 : ℝ) :=
  ((∑ n ∈ u.property.toFinset, r n * ((u.val n : ℕ) : ℚ) : ℚ) : ℝ)

/-- The coordinate phases with golden ratio frequency. -/
noncomputable def psi {A : ℕ → ℕ} (u : B A) : ℕ → AddCircle (1 : ℝ) :=
  fun n => (Real.goldenRatio * ((u.val n : ℕ) : ℝ) : ℝ)

/-- The initial topology of the golden phases and all rational characters. -/
@[instance_reducible] noncomputable def tauPlus (A : ℕ → ℕ) : TopologicalSpace (B A) :=
  TopologicalSpace.induced psi inferInstance ⊓
    ⨅ r : ℕ → ℚ, TopologicalSpace.induced (chi r) inferInstance

/-- Convergence for finite capacity states is equivalent to eventual equality with the limit. -/
theorem tendsto_tauPlus_iff_eventually_eq (A : ℕ → ℕ) (u : B A) (s : ℕ → B A) :
    Tendsto s atTop (@nhds _ (tauPlus A) u) ↔ ∃ K, ∀ k ≥ K, s k = u := by
  classical
  constructor
  · intro hs
    have hchars (r : ℕ → ℚ) : Tendsto (fun k => chi r (s k)) atTop (𝓝 (chi r u)) := by
      have hle : tauPlus A ≤ TopologicalSpace.induced (chi r) inferInstance :=
        inf_le_right.trans (iInf_le _ r)
      have hr := hs.mono_right (nhds_mono hle)
      rwa [nhds_induced, tendsto_comap_iff] at hr
    have hcoord (n : ℕ) : ∀ᶠ k in atTop, (s k).val n = u.val n := by
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
      have ht : Tendsto (fun k => e ((s k).val n)) atTop (𝓝 (e (u.val n))) := by
        simpa only [he] using hchars r
      have hall : ∀ m : Fin (A n + 1),
          ∀ᶠ k in atTop, m ≠ u.val n → (s k).val n ≠ m := by
        intro m
        by_cases hm : m = u.val n
        · exact Filter.Eventually.of_forall (fun _ h => (h hm).elim)
        · filter_upwards [ht.eventually_ne (fun h => hm (hei h.symm))] with k hk _
          exact fun h => hk (congrArg e h)
      filter_upwards [Filter.eventually_all.mpr hall] with k hk
      by_contra h
      exact hk ((s k).val n) h rfl
    let v (w : B A) : ℕ →₀ ℤ := Finsupp.ofSupportFinite
      (fun n => ((w.val n : ℕ) : ℤ)) (by
        apply w.property.subset
        intro n hn
        change ((w.val n : ℕ) : ℤ) ≠ 0 at hn
        change (w.val n : ℕ) ≠ 0
        intro h
        exact hn (by rw [h]; rfl))
    let d (k : ℕ) : ℕ →₀ ℤ := v (s k) - v u
    have hv (w : B A) (n : ℕ) : v w n = ((w.val n : ℕ) : ℤ) := rfl
    have hvs (w : B A) : (v w).support = w.property.toFinset := by
      ext n
      simp [Finsupp.mem_support_iff, hv]
    have hdeq (k : ℕ) : d k = 0 ↔ s k = u := by
      constructor
      · intro hk
        apply Subtype.ext
        funext n
        apply Fin.ext
        have hn := DFunLike.congr_fun hk n
        change ((s k).val n : ℤ) - (u.val n : ℤ) = 0 at hn
        exact_mod_cast sub_eq_zero.mp hn
      · intro hk; simp [d, hk]
    have hdz (n : ℕ) : ∀ᶠ k in atTop, d k n = 0 := by
      filter_upwards [hcoord n] with k hk
      simp [d, hv, hk]
    let ev (r : ℕ → ℚ) (z : ℕ →₀ ℤ) : ℚ := z.sum (fun n a => r n * (a : ℚ))
    have hev (r : ℕ → ℚ) (w : B A) : chi r w = ((ev r (v w) : ℚ) : ℝ) := by
      unfold chi
      congr 2
      dsimp [ev, Finsupp.sum]
      rw [hvs]
      simp [hv]
    have hsub (r : ℕ → ℚ) (k : ℕ) :
        chi r (s k) - chi r u = ((ev r (d k) : ℚ) : ℝ) := by
      rw [hev, hev, ← AddCircle.coe_sub]
      congr 1
      dsimp [ev, d]
      rw [Finsupp.sum_sub_index (by intros; push_cast; ring)]
      push_cast
      rfl
    by_contra hn
    push Not at hn
    have hlate (K : ℕ) : ∃ k ≥ K, d k ≠ 0 := by
      obtain ⟨k, hk, hne⟩ := hn K
      exact ⟨k, hk, fun h => hne ((hdeq k).mp h)⟩
    let bound (k : ℕ) := (d k).support.sup id
    have hnext (k : ℕ) : ∃ l, k < l ∧ d l ≠ 0 ∧ ∀ n ≤ bound k, d l n = 0 := by
      have hall : ∀ᶠ l in atTop, ∀ n ∈ Finset.range (bound k + 1), d l n = 0 :=
        (Finset.eventually_all _).mpr (fun n _ => hdz n)
      obtain ⟨K, hK⟩ := hall.exists_forall_of_atTop
      obtain ⟨l, hl, hne⟩ := hlate (max K (k + 1))
      refine ⟨l, by omega, hne, ?_⟩
      intro n hn
      exact hK l (by omega) n (Finset.mem_range.mpr (by omega))
    choose next hnext using hnext
    obtain ⟨k₀, _, hk₀⟩ := hlate 0
    let f : ℕ → ℕ := fun j => next^[j] k₀
    have hfs (j : ℕ) : f (j + 1) = next (f j) := Function.iterate_succ_apply' _ _ _
    have hfne (j : ℕ) : d (f j) ≠ 0 := by
      cases j with
      | zero => exact hk₀
      | succ j => rw [hfs]; exact (hnext (f j)).2.1
    have hfm : StrictMono f := strictMono_nat_of_lt_succ (fun j => by
      rw [hfs]; exact (hnext (f j)).1)
    have hp : ∀ j, ∃ n, d (f j) n ≠ 0 := by
      intro j
      by_contra h
      push Not at h
      exact hfne j (Finsupp.ext h)
    choose p hp using hp
    have hpm (j : ℕ) : p j ∈ (d (f j)).support := Finsupp.mem_support_iff.mpr (hp j)
    have hbm : StrictMono (fun j => bound (f j)) := by
      apply strictMono_nat_of_lt_succ
      intro j
      have hle : p (j + 1) ≤ bound (f (j + 1)) := Finset.le_sup (f := id) (hpm _)
      have hgt : bound (f j) < p (j + 1) := by
        by_contra h
        have hz := (hnext (f j)).2.2 (p (j + 1)) (by omega)
        rw [← hfs] at hz
        exact hp (j + 1) hz
      omega
    have hsep (i j : ℕ) (hij : i < j) (n : ℕ)
        (hni : n ∈ (d (f i)).support) : d (f j) n = 0 := by
      cases j with
      | zero => omega
      | succ j =>
        have hle : n ≤ bound (f i) := Finset.le_sup (f := id) hni
        have hle' := hbm.monotone (show i ≤ j by omega)
        rw [hfs]
        exact (hnext (f j)).2.2 n (hle.trans hle')
    have hdisj (i j : ℕ) (hij : i ≠ j) :
        Disjoint (d (f i)).support (d (f j)).support := by
      apply Finset.disjoint_left.mpr
      intro n hni hnj
      rcases lt_or_gt_of_ne hij with h | h
      · exact (Finsupp.mem_support_iff.mp hnj) (hsep i j h n hni)
      · exact (Finsupp.mem_support_iff.mp hni) (hsep j i h n hnj)
    have hpi : Function.Injective p := by
      intro i j hij
      by_contra h
      exact Finset.disjoint_left.mp (hdisj i j h) (hpm i) (hij ▸ hpm j)
    let r : ℕ → ℚ := fun n => if h : ∃ j, p j = n then
      1 / (2 * (d (f h.choose) n : ℚ)) else 0
    have hrp (j : ℕ) : r (p j) = 1 / (2 * (d (f j) (p j) : ℚ)) := by
      have hex : ∃ i, p i = p j := ⟨j, rfl⟩
      have hi : hex.choose = j := hpi hex.choose_spec
      simp only [r, dif_pos hex, hi]
    have hrz (j n : ℕ) (hn : n ∈ (d (f j)).support) (hne : n ≠ p j) : r n = 0 := by
      have hnot : ¬ ∃ i, p i = n := by
        rintro ⟨i, rfl⟩
        have hij : i ≠ j := fun h => hne (congrArg p h)
        exact Finset.disjoint_left.mp (hdisj i j hij) (hpm i) hn
      simp only [r, dif_neg hnot]
    have hhalf (j : ℕ) : ev r (d (f j)) = 1 / 2 := by
      dsimp [ev, Finsupp.sum]
      rw [Finset.sum_eq_single (p j)]
      · rw [hrp]
        have hnonzero : (d (f j) (p j) : ℚ) ≠ 0 := by exact_mod_cast hp j
        field_simp
      · intro n hn hne; rw [hrz j n hn hne, zero_mul]
      · exact fun h => (h (hpm j)).elim
    have ht : Tendsto (fun j => chi r (s (f j)) - chi r u) atTop (𝓝 0) := by
      simpa using ((hchars r).comp hfm.tendsto_atTop).sub_const (chi r u)
    have heq (j : ℕ) :
        chi r (s (f j)) - chi r u = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [hsub, hhalf]
      congr 1
      push_cast
      rfl
    have hnonzero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
      intro h
      have hz : (1 / 2 : ℝ) = 0 :=
        (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ))
          (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp h
      norm_num at hz
    have hzero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds (ht.congr heq)
    exact hnonzero hzero
  · rintro ⟨K, hK⟩
    let : TopologicalSpace (B A) := tauPlus A
    exact tendsto_nhds_of_eventually_eq (eventually_atTop.mpr ⟨K, hK⟩)

#print axioms tendsto_tauPlus_iff_eventually_eq

end D5.S3.Analytic.WeightedCapacity.ProbeTopologySequences
