/- GID: D5/S1/Dynamics/Shadowing/PointwiseNorthSouth
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/PointwiseNorthSouth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Sequences, mathlib/module/Mathlib.Topology.Compactness.Compact]
   utility: none
   digest: Stability and compact uniform attraction derived from literal two-sided pointwise north-south dynamics. -/

import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Compactness converts the literal pointwise assumptions into stable uniform dynamics. -/

noncomputable section
open Set Filter Topology

namespace D5.S1.Dynamics.Shadowing.PointwiseNorthSouth

variable {M : Type*} [MetricSpace M]

/-- Literal pointwise north-south dynamics, with no stability or uniformity premise. -/
structure Pointwise (f : M ≃ₜ M) (N S : M) : Prop where
  distinct : N ≠ S
  north_fixed : f N = N
  south_fixed : f S = S
  forward : ∀ p, p ≠ N → p ≠ S →
    Tendsto (fun n : ℕ => (f ^ n) p) atTop (𝓝 S)
  backward : ∀ p, p ≠ N → p ≠ S →
    Tendsto (fun n : ℕ => (f.symm ^ n) p) atTop (𝓝 N)

/-- Stability includes all nonnegative times and all points in one neighborhood. -/
def Stable (f : M ≃ₜ M) (p : M) : Prop :=
  ∀ O ∈ 𝓝 p, ∃ V ∈ 𝓝 p, ∀ n : ℕ, (f ^ n) '' V ⊆ O

private theorem pow_fixed (f : M ≃ₜ M) {p : M} (hp : f p = p) (n : ℕ) :
    (f ^ n) p = p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Homeomorph.mul_apply, ih, hp]

private theorem inverse_pow_cancel (f : M ≃ₜ M) (p : M) {m n : ℕ} (hm : m ≤ n) :
    (f.symm ^ m) ((f ^ n) p) = (f ^ (n - m)) p := by
  have he : (f ^ n) p = (f ^ m) ((f ^ (n - m)) p) := by
    rw [← Homeomorph.mul_apply, ← pow_add, Nat.add_sub_of_le hm]
  have hi : f.symm ^ m = (f ^ m).symm := by
    change (f⁻¹) ^ m = (f ^ m)⁻¹
    exact inv_pow f m
  rw [he, hi, Homeomorph.symm_apply_apply]

private theorem inverse_dynamics {f : M ≃ₜ M} {N S : M} (h : Pointwise f N S) :
    Pointwise f.symm S N where
  distinct := h.distinct.symm
  north_fixed := f.injective (by rw [f.apply_symm_apply, h.south_fixed])
  south_fixed := f.injective (by rw [f.apply_symm_apply, h.north_fixed])
  forward p hpS hpN := h.backward p hpN hpS
  backward p hpS hpN := by simpa using h.forward p hpN hpS

/-- The first-exit limit uses every strictly negative iterate, rather than
incorrectly placing the exit point itself inside the trapping closure. -/
private theorem stable_south [CompactSpace M] {f : M ≃ₜ M} {N S : M}
    (h : Pointwise f N S) : Stable f S := by
  classical
  intro O hO
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp hO
  let a : ℝ := min r (dist N S) / 2
  have hNS : 0 < dist N S := dist_pos.mpr h.distinct
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r := by dsimp [a]; linarith [min_le_left r (dist N S)]
  have haNS : a < dist N S := by dsimp [a]; linarith [min_le_right r (dist N S)]
  let U := Metric.ball S a
  have hUS : S ∈ U := Metric.mem_ball_self ha
  have hUO : U ⊆ O := (Metric.ball_subset_ball har.le).trans hrO
  suffices hh : ∃ V ∈ 𝓝 S, ∀ n : ℕ, (f ^ n) '' V ⊆ U by
    obtain ⟨V, hV, hv⟩ := hh
    exact ⟨V, hV, fun n => (hv n).trans hUO⟩
  by_contra hn
  have bad (l : ℕ) : ∃ x : M, dist x S < 1 / ((l : ℝ) + 1) ∧
      ∃ n : ℕ, (f ^ n) x ∉ U := by
    by_contra hb
    push Not at hb
    apply hn
    refine ⟨Metric.ball S (1 / ((l : ℝ) + 1)), Metric.ball_mem_nhds S (by positivity), ?_⟩
    intro n z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hb x hx n
  choose x hx he using bad
  let e (l : ℕ) : ℕ := Nat.find (he l)
  have hexit (l : ℕ) : (f ^ e l) (x l) ∉ U := Nat.find_spec (he l)
  have hbefore (l j : ℕ) (hj : j < e l) : (f ^ j) (x l) ∈ U := by
    exact of_not_not (Nat.find_min (he l) hj)
  have hxS : Tendsto x atTop (𝓝 S) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε))
    filter_upwards [hh] with l hl
    exact (hx l).trans hl
  have he_large (T : ℕ) : ∀ᶠ l in atTop, T < e l := by
    have hfinite : ∀ᶠ l in atTop, ∀ j ∈ Finset.range (T + 1), (f ^ j) (x l) ∈ U := by
      apply (Finset.eventually_all _).mpr
      intro j hj
      have hjS : Tendsto (fun l => (f ^ j) (x l)) atTop (𝓝 S) := by
        simpa only [Function.comp_def, pow_fixed f h.south_fixed] using (f ^ j).continuous.continuousAt.tendsto.comp hxS
      exact hjS.eventually (Metric.ball_mem_nhds S ha)
    filter_upwards [hfinite] with l hl
    by_contra hh
    exact hexit l (hl (e l) (Finset.mem_range.mpr (by omega)))
  let y (l : ℕ) := (f ^ e l) (x l)
  obtain ⟨z, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq y
  have hzout : z ∉ U := by
    exact (Metric.isOpen_ball.isClosed_compl).mem_of_tendsto hz
      (Eventually.of_forall fun l => hexit (φ l))
  have hzS : z ≠ S := fun hh => hzout (hh ▸ hUS)
  have hback (m : ℕ) (hm : 0 < m) : (f.symm ^ m) z ∈ closure U := by
    apply isClosed_closure.mem_of_tendsto ((f.symm ^ m).continuous.continuousAt.tendsto.comp hz)
    have heφ : ∀ᶠ l in atTop, m < e (φ l) := hφ.tendsto_atTop.eventually (he_large m)
    filter_upwards [heφ] with l hl
    apply subset_closure
    change (f.symm ^ m) ((f ^ e (φ l)) (x (φ l))) ∈ U
    rw [inverse_pow_cancel f _ hl.le]
    exact hbefore (φ l) (e (φ l) - m) (by omega)
  have hNout : N ∉ closure U := by
    intro hh
    have hb := Metric.closure_ball_subset_closedBall hh
    exact (not_le_of_gt haNS) hb
  have hzN : z ≠ N := by
    intro hh
    have hb := hback 1 (by omega)
    rw [hh, pow_one] at hb
    have hfix : f.symm N = N := f.injective (by rw [f.apply_symm_apply, h.north_fixed])
    exact hNout (hfix ▸ hb)
  have hb := h.backward z hzN hzS
  have hlim : N ∈ closure U := isClosed_closure.mem_of_tendsto hb (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact hback m (by omega))
  exact hNout hlim

private theorem uniform_of_stable [CompactSpace M] {f : M ≃ₜ M} {N S : M}
    (h : Pointwise f N S) (hs : Stable f S) {C : Set M} (hC : IsCompact C) (hCN : N ∉ C)
    {O : Set M} (hO : O ∈ 𝓝 S) :
    ∃ T : ℕ, ∀ n ≥ T, (f ^ n) '' C ⊆ O := by
  classical
  obtain ⟨V, hV, hVO⟩ := hs O hO
  obtain ⟨A, hAV, hAo, hSA⟩ := mem_nhds_iff.mp hV
  have hit (p : C) : ∃ n : ℕ, (f ^ n) p.1 ∈ A := by
    by_cases hpS : p.1 = S
    · exact ⟨0, by simpa [hpS] using hSA⟩
    have hpN : p.1 ≠ N := fun hh => hCN (hh ▸ p.2)
    exact (h.forward p.1 hpN hpS).eventually (hAo.mem_nhds hSA) |>.exists
  choose k hk using hit
  let B (p : C) := (f ^ k p) ⁻¹' A
  obtain ⟨s, hsCover⟩ := hC.elim_finite_subcover B
    (fun p => hAo.preimage (f ^ k p).continuous) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hk ⟨p, hp⟩⟩)
  refine ⟨s.sup k, fun n hn z hz => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hz
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hsCover hp)
  have hkn : k q ≤ n := (Finset.le_sup hq).trans hn
  have he : (f ^ n) p = (f ^ (n - k q)) ((f ^ k q) p) := by
    rw [← Homeomorph.mul_apply, ← pow_add, Nat.sub_add_cancel hkn]
  rw [he]
  exact hVO (n - k q) ⟨(f ^ k q) p, hAV hpq, rfl⟩

/-- Literal pointwise north-south dynamics implies both stable poles and
uniform attraction on every compact set avoiding the opposite pole. -/
theorem stability_and_compact_uniformity [CompactSpace M] {f : M ≃ₜ M} {N S : M}
    (h : Pointwise f N S) :
    Stable f S ∧ Stable f.symm N ∧
    (∀ C : Set M, IsCompact C → N ∉ C → ∀ O ∈ 𝓝 S,
      ∃ T : ℕ, ∀ n ≥ T, (f ^ n) '' C ⊆ O) ∧
    (∀ C : Set M, IsCompact C → S ∉ C → ∀ O ∈ 𝓝 N,
      ∃ T : ℕ, ∀ n ≥ T, (f.symm ^ n) '' C ⊆ O) := by
  have hs := stable_south h
  have hi := inverse_dynamics h
  have hn := stable_south hi
  exact ⟨hs, hn, fun _ hC hCN _ hO => uniform_of_stable h hs hC hCN hO,
    fun _ hC hCS _ hO => uniform_of_stable hi hn hC hCS hO⟩

#print axioms stability_and_compact_uniformity

end D5.S1.Dynamics.Shadowing.PointwiseNorthSouth
