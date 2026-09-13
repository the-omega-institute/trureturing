/- GID: D5/S3/Analytic/WeightedCapacity/DyadicTailFilling
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/DyadicTailFilling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divergent dyadic capacities give exact sublevel closures of finite state levels. -/
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

namespace D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

open Set Filter
open scoped Topology BigOperators

/-- The product of the discrete natural coordinate intervals bounded by the capacities. -/
abbrev X (A : ℕ → ℕ) := ∀ n, Fin (A n + 1)

/-- The sum of the first k dyadically weighted natural coordinates. -/
noncomputable def prefixSum (k : ℕ) (x : ℕ → ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, (x n : ℝ) / 2 ^ n

/-- The inclusive partial sum through coordinate N. -/
noncomputable def P {A : ℕ → ℕ} (N : ℕ) (x : X A) : ℝ :=
  prefixSum (N + 1) (fun n => (x n : ℕ))

/-- The supremum of the nonnegative inclusive partial sums in the extended nonnegative reals. -/
noncomputable def S {A : ℕ → ℕ} (x : X A) : ENNReal :=
  ⨆ N, ENNReal.ofReal (P N x)

/-- The extended total mass of the capacity corner. -/
noncomputable def M (A : ℕ → ℕ) : ENNReal :=
  S (fun n => ⟨A n, Nat.lt_succ_self _⟩)

/-- States with finite support, equipped with the topology inherited from the full product. -/
abbrev B (A : ℕ → ℕ) := {x : X A // (Function.support (fun n => (x n : ℕ))).Finite}

/-- The real dyadic sum over the finite support of a state. -/
noncomputable def readout {A : ℕ → ℕ} (u : B A) : ℝ :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℝ) / 2 ^ n

/-- Nonnegative dyadic rational real numbers. -/
def Dpos : Set ℝ := {c | ∃ a q : ℕ, c = (a : ℝ) / 2 ^ q}

/-- A finite-state level set in its relative carrier. -/
def L (A : ℕ → ℕ) (c : ℝ) : Set (B A) := {u | readout u = c}

/-- The image of a finite-state level in the full product. -/
def ambientLevel (A : ℕ → ℕ) (c : ℝ) : Set (X A) := Subtype.val '' L A c

/-- Under divergent total capacity, a nonnegative dyadic finite-state level has precisely the
corresponding sublevel as its closure in both the full product and the finite-state carrier. -/
theorem closure_level_eq_sublevel (A : ℕ → ℕ) (c : ℝ) (hM : M A = ⊤)
    (hc : c ∈ Dpos) :
    closure (ambientLevel A c) = {x | S x ≤ ENNReal.ofReal c} ∧
      closure (L A c) = {u | readout u ≤ c} := by
  classical
  obtain ⟨a, q, hc⟩ := hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hpmono (f : ℕ → ℕ) : Monotone (fun k => prefixSum k f) := by
    intro i j hij
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    intros; positivity
  have hscale (f : ℕ → ℕ) (k : ℕ) :
      prefixSum k f * (2 : ℝ) ^ k =
        ((∑ n ∈ Finset.range k, f n * 2 ^ (k - n) : ℕ) : ℝ) := by
    unfold prefixSum
    rw [Finset.sum_mul]
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_sub₀ (2 : ℝ) (by norm_num) (Nat.le_of_lt (Finset.mem_range.mp hn))]
    ring
  have hread (u : B A) (k : ℕ) (hk : ∀ n, k ≤ n → (u.val n : ℕ) = 0) :
      prefixSum k (fun n => (u.val n : ℕ)) = readout u := by
    unfold prefixSum readout
    symm
    apply Finset.sum_subset
    · intro n hn
      have hne : (u.val n : ℕ) ≠ 0 := by simpa using hn
      exact Finset.mem_range.mpr (by by_contra h; exact hne (hk n (by omega)))
    · intro n _ hn
      have hz : (u.val n : ℕ) = 0 := by simpa using hn
      simp [hz]
  have hreadbound (u : B A) (k : ℕ) :
      prefixSum k (fun n => (u.val n : ℕ)) ≤ readout u := by
    let t := u.property.toFinset
    let j := max k (t.sup id + 1)
    have hz (n : ℕ) (hn : j ≤ n) : (u.val n : ℕ) = 0 := by
      by_contra h
      have hnt : n ∈ t := by simpa [t] using h
      have hns : n ≤ t.sup id := Finset.le_sup (f := id) hnt
      dsimp [j] at hn
      omega
    rw [← hread u j hz]
    exact hpmono _ (le_max_left _ _)
  have hsub (x : X A) : S x ≤ ENNReal.ofReal c ↔
      ∀ k, prefixSum k (fun n => (x n : ℕ)) ≤ c := by
    constructor
    · intro hx k
      cases k with
      | zero => simpa [prefixSum] using hc0
      | succ k =>
        exact (ENNReal.ofReal_le_ofReal_iff hc0).mp
          ((le_iSup (fun N => ENNReal.ofReal (P N x)) k).trans hx)
    · intro hx
      exact iSup_le fun N => ENNReal.ofReal_le_ofReal (hx (N + 1))
  have hunbounded (R : ℝ) : ∃ k, R < prefixSum k A := by
    by_contra hn
    push Not at hn
    have hh : M A ≤ ENNReal.ofReal R :=
      iSup_le fun N => ENNReal.ofReal_le_ofReal (hn (N + 1))
    rw [hM] at hh
    exact (ne_of_lt ENNReal.ofReal_lt_top) (top_le_iff.mp hh)
  have hclosed : IsClosed {x : X A | S x ≤ ENNReal.ofReal c} := by
    have heq : {x : X A | S x ≤ ENNReal.ofReal c} =
        ⋂ k : ℕ, {x | prefixSum k (fun n => (x n : ℕ)) ≤ c} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, hsub]
    rw [heq]
    apply isClosed_iInter
    intro k
    apply isClosed_le _ continuous_const
    unfold prefixSum
    apply continuous_finsetSum
    intro n _
    exact ((continuous_of_discreteTopology : Continuous (fun z : Fin (A n + 1) =>
      ((z : ℕ) : ℝ))).comp (continuous_apply n)).div_const _
  have hambient : closure (ambientLevel A c) = {x | S x ≤ ENNReal.ofReal c} := by
    apply subset_antisymm
    · apply closure_minimal _ hclosed
      rintro x ⟨u, hu, rfl⟩
      apply (hsub _).mpr
      intro k
      exact (hreadbound u k).trans_eq hu
    · intro x hx
      apply mem_closure_iff.mpr
      intro o ho hxo
      have hon := ho.mem_nhds hxo
      rw [nhds_pi, Filter.mem_pi'] at hon
      obtain ⟨I, t, ht, hto⟩ := hon
      let K := max q (I.sup id + 1)
      have hqK : q ≤ K := le_max_left _ _
      have hIK (n : ℕ) (hn : n ∈ I) : n < K := by
        have hns : n ≤ I.sup id := Finset.le_sup (f := id) hn
        dsimp [K]
        omega
      let y : ℕ → ℕ := fun n => if n < K then (x n : ℕ) else A n
      have hyK : prefixSum K y = prefixSum K (fun n => (x n : ℕ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [y, Finset.mem_range.mp hn]
      have hKy : prefixSum K y ≤ c := by rw [hyK]; exact (hsub x).mp hx K
      have hybound (j : ℕ) : prefixSum j A ≤ prefixSum j y + prefixSum K A := by
        unfold prefixSum
        calc
          _ ≤ (∑ n ∈ Finset.range j, (y n : ℝ) / 2 ^ n) +
              ∑ n ∈ Finset.range j, if n < K then (A n : ℝ) / 2 ^ n else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_le_sum
            intro n _
            dsimp [y]
            by_cases hn : n < K
            · simp only [if_pos hn]
              exact le_add_of_nonneg_left (by positivity)
            · simp [hn]
          _ ≤ _ := by
            apply add_le_add le_rfl
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
            · intros; positivity
      have hex : ∃ m, K ≤ m ∧ c ≤ prefixSum (m + 1) y := by
        obtain ⟨j, hj⟩ := hunbounded (c + prefixSum K A)
        refine ⟨max K j, le_max_left _ _, ?_⟩
        have hbj := hybound j
        exact (show c ≤ prefixSum j y by linarith).trans
          (hpmono y (by omega))
      let m := Nat.find hex
      have hmK : K ≤ m := (Nat.find_spec hex).1
      have hmc : c ≤ prefixSum (m + 1) y := (Nat.find_spec hex).2
      have hprev : prefixSum m y ≤ c := by
        rcases eq_or_lt_of_le hmK with h | h
        · simpa [← h] using hKy
        · have hh := Nat.find_min hex (show m - 1 < m by omega)
          have hm1 : K ≤ m - 1 := by omega
          have he : m - 1 + 1 = m := by omega
          exact le_of_lt (lt_of_not_ge (fun hh' => hh ⟨hm1, by simpa [he] using hh'⟩))
      let v : ℕ := a * 2 ^ (m - q)
      let w : ℕ := ∑ n ∈ Finset.range m, y n * 2 ^ (m - n)
      have hvc : (v : ℝ) = c * 2 ^ m := by
        dsimp [v]
        push_cast
        rw [hc, pow_sub₀ (2 : ℝ) (by norm_num) (hqK.trans hmK)]
        ring
      have hwc : (w : ℝ) = prefixSum m y * 2 ^ m := (hscale y m).symm
      have hwv : w ≤ v := by
        exact_mod_cast (show (w : ℝ) ≤ v by
          rw [hvc, hwc]
          exact mul_le_mul_of_nonneg_right hprev (by positivity))
      let b := v - w
      have hbc : (b : ℝ) = (c - prefixSum m y) * 2 ^ m := by
        dsimp [b]
        rw [Nat.cast_sub hwv, hvc, hwc]
        ring
      have hy_m : y m = A m := by simp [y, Nat.not_lt.mpr hmK]
      have hbA : b ≤ A m := by
        have hstep : prefixSum (m + 1) y = prefixSum m y + (A m : ℝ) / 2 ^ m := by
          simp [prefixSum, Finset.sum_range_succ, hy_m]
        have h2 : (0 : ℝ) < 2 ^ m := by positivity
        have hbc' : (b : ℝ) ≤ A m := by
          rw [hbc]
          apply (le_div_iff₀ h2).mp
          linarith [hmc, hstep]
        exact_mod_cast hbc'
      let u : X A := fun n =>
        if hn : n < m then
          ⟨y n, by
            dsimp [y]
            split_ifs
            · exact (x n).isLt
            · exact Nat.lt_succ_self _⟩
        else if hn : n = m then ⟨b, by subst n; omega⟩
        else ⟨0, Nat.zero_lt_succ _⟩
      have hu_before (n : ℕ) (hn : n < m) : (u n : ℕ) = y n := by simp [u, hn]
      have hu_at : (u m : ℕ) = b := by simp [u]
      have hu_after (n : ℕ) (hn : m + 1 ≤ n) : (u n : ℕ) = 0 := by
        simp [u, show ¬ n < m by omega, show n ≠ m by omega]
      have hu_fin : (Function.support (fun n => (u n : ℕ))).Finite := by
        apply (Finset.range (m + 1)).finite_toSet.subset
        intro n hn
        apply Finset.mem_range.mpr
        by_contra h
        exact hn (hu_after n (by omega))
      let ub : B A := ⟨u, hu_fin⟩
      have hu_eq : readout ub = c := by
        rw [← hread ub (m + 1) hu_after]
        change prefixSum (m + 1) (fun n => (u n : ℕ)) = c
        have hpm : prefixSum m (fun n => (u n : ℕ)) = prefixSum m y := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [hu_before n (Finset.mem_range.mp hn)]
        have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
        rw [show prefixSum (m + 1) (fun n => (u n : ℕ)) =
            prefixSum m (fun n => (u n : ℕ)) + (b : ℝ) / 2 ^ m by
          simp [prefixSum, Finset.sum_range_succ, hu_at]]
        rw [hpm, hbc, mul_div_cancel_right₀ _ h2]
        ring
      refine ⟨u, hto ?_, ⟨ub, hu_eq, rfl⟩⟩
      intro n hn
      have hnK := hIK n hn
      have hun : u n = x n := by
        apply Fin.ext
        rw [hu_before n (lt_of_lt_of_le hnK hmK)]
        simp [y, hnK]
      rw [hun]
      exact mem_of_mem_nhds (ht n)
  refine ⟨hambient, ?_⟩
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change Subtype.val ⁻¹' closure (ambientLevel A c) = _
  rw [hambient]
  ext u
  change S u.val ≤ ENNReal.ofReal c ↔ readout u ≤ c
  rw [hsub]
  constructor
  · intro hu
    let k := u.property.toFinset.sup id + 1
    have hz (n : ℕ) (hn : k ≤ n) : (u.val n : ℕ) = 0 := by
      by_contra h
      have hnt : n ∈ u.property.toFinset := by simpa using h
      have hns : n ≤ u.property.toFinset.sup id := Finset.le_sup (f := id) hnt
      dsimp [k] at hn
      omega
    rw [← hread u k hz]
    exact hu k
  · intro hu k
    exact (hreadbound u k).trans hu

#print axioms closure_level_eq_sublevel

end D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
