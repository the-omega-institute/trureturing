/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/CoconnectedOpening
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/CoconnectedOpening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small open sets with connected compact complement from actual paths. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.ProperExpansion
import Mathlib.Topology.MetricSpace.Bounded

/-! The finite-cover construction for small co-connected openings. -/

open Set Function TopologicalSpace
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X] [CompactSpace X]

private theorem opening_chain
    (paths : ∀ c y : X, ∃ α : ℝ → X, ContinuousOn α (Icc (0 : ℝ) 1) ∧
      α 0 = c ∧ α 1 = y)
    (r : X) (hr : ({r} : Set X) ≠ univ)
    (H : ℕ → Set X) (hH : ∀ n, IsOpen (H n)) :
    ∃ C W : ℕ → Set X, C 0 = {r} ∧
      (∀ n, IsCompact (C n) ∧ IsConnected (C n) ∧ C n ≠ univ ∧ r ∈ C n) ∧
      (∀ n, C n ⊆ interior (C (n + 1))) ∧
      (∀ n, IsOpen (W n) ∧ (W n).Nonempty ∧
        C (n + 1) = connectedComponentIn (W n)ᶜ r ∧
        (W n ⊆ H n ∨ H n ⊆ C (n + 1))) := by
  classical
  let Stage := {C : Set X // IsCompact C ∧ IsConnected C ∧ C ≠ univ ∧ r ∈ C}
  have step_exists (n : ℕ) (s : Stage) : ∃ (D : Stage) (W : Set X),
      s.1 ⊆ interior D.1 ∧ IsOpen W ∧ W.Nonempty ∧
      D.1 = connectedComponentIn Wᶜ r ∧ (W ⊆ H n ∨ H n ⊆ D.1) := by
    have hex : ∃ B W : Set X, IsCompact B ∧ IsConnected B ∧ B ≠ univ ∧
        s.1 ⊆ interior B ∧ IsOpen W ∧ W.Nonempty ∧ Disjoint B W ∧
        (W ⊆ H n ∨ H n ⊆ B) := by
      by_cases h : ∃ B : Set X, IsCompact B ∧ IsConnected B ∧ B ≠ univ ∧
          s.1 ⊆ interior B ∧ (H n \ B).Nonempty
      · obtain ⟨B, hc, hcon, hp, hi, hne⟩ := h
        exact ⟨B, H n \ B, hc, hcon, hp, hi, (hH n).sdiff hc.isClosed,
          hne, disjoint_sdiff_right, Or.inl sdiff_subset⟩
      · obtain ⟨B, hc, hcon, hp, hi⟩ := proper_continuum_expansion paths
          s.2.1 s.2.2.1 s.2.2.2.1
        have hsub : H n ⊆ B := by
          intro x hx
          by_contra hxb
          exact h ⟨B, hc, hcon, hp, hi, x, hx, hxb⟩
        exact ⟨B, Bᶜ, hc, hcon, hp, hi, hc.isClosed.isOpen_compl,
          Set.nonempty_compl.mpr hp, disjoint_compl_right, Or.inr hsub⟩
    obtain ⟨B, W, hc, hcon, hp, hi, hWo, hWne, hBW, hchoice⟩ := hex
    have hBsub : B ⊆ Wᶜ := fun x hx hw => Set.disjoint_left.mp hBW hx hw
    have hrB : r ∈ B := interior_subset (hi s.2.2.2.2)
    have hrW : r ∈ Wᶜ := hBsub hrB
    let D := connectedComponentIn Wᶜ r
    have hBD : B ⊆ D := hcon.isPreconnected.subset_connectedComponentIn hrB hBsub
    have hDc : IsCompact D := compact_component hWo.isClosed_compl.isCompact hrW
    have hDcon : IsConnected D := isConnected_connectedComponentIn_iff.mpr hrW
    have hDp : D ≠ univ := by
      intro heq
      obtain ⟨w, hw⟩ := hWne
      exact (connectedComponentIn_subset Wᶜ r
        (show w ∈ D by rw [heq]; trivial)) hw
    refine ⟨⟨D, hDc, hDcon, hDp, mem_connectedComponentIn hrW⟩, W,
      hi.trans (interior_mono hBD), hWo, hWne, rfl, ?_⟩
    exact hchoice.imp_right (fun h => h.trans hBD)
  choose next W hnext using step_exists
  let s₀ : Stage := ⟨{r}, isCompact_singleton, isConnected_singleton, hr, rfl⟩
  let s : ℕ → Stage := Nat.rec s₀ (fun n t => next n t)
  refine ⟨fun n => (s n).1, fun n => W n (s n), rfl, fun n => (s n).2,
    fun n => (hnext n (s n)).1, ?_⟩
  intro n
  exact (hnext n (s n)).2

private theorem chain_union_absorbs {C : ℕ → Set X}
    (hstep : ∀ n, C n ⊆ interior (C (n + 1)))
    {S : Set X} (hS : IsCompact S) (hsub : S ⊆ ⋃ n, C n) :
    ∃ N, S ⊆ C N := by
  have hmono : Monotone C := monotone_nat_of_le_succ
    (fun n => (hstep n).trans interior_subset)
  have hcover : S ⊆ ⋃ n, interior (C n) := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hsub hx)
    exact mem_iUnion.mpr ⟨n + 1, hstep n hn⟩
  obtain ⟨N, hN⟩ := hS.elim_directed_cover (fun n => interior (C n))
    (fun _ => isOpen_interior) hcover
    (fun n m => ⟨max n m, interior_mono (hmono (le_max_left _ _)),
      interior_mono (hmono (le_max_right _ _))⟩)
  exact ⟨N, hN.trans interior_subset⟩

private theorem first_closed_hit {α : ℝ → X}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1)) {K : Set X} (hK : IsClosed K)
    (h0 : α 0 ∉ K) (h1 : α 1 ∈ K) :
    ∃ τ ∈ Ioc (0 : ℝ) 1, α τ ∈ K ∧ ∀ t ∈ Ico (0 : ℝ) τ, α t ∉ K := by
  let S := Icc (0 : ℝ) 1 ∩ α ⁻¹' K
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hα.preimage_isClosed_of_isClosed isClosed_Icc hK) inter_subset_left
  obtain ⟨τ, hτ, hmin⟩ := hSc.exists_isMinOn
    (show S.Nonempty from ⟨1, by norm_num, h1⟩) continuous_id.continuousOn
  have hpos : 0 < τ := lt_of_le_of_ne hτ.1.1 (by
    intro heq
    exact h0 (heq ▸ hτ.2))
  refine ⟨τ, ⟨hpos, hτ.1.2⟩, hτ.2, ?_⟩
  intro t ht htk
  have := hmin (show t ∈ S from ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, htk⟩)
  exact (not_le_of_gt ht.2) this

private theorem terminal_segment_avoids {α : ℝ → X}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1)) {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1)
    {V : Set X} (he : α τ ∉ closure V) :
    ∃ t₀ ∈ Ico (0 : ℝ) τ, ∀ t ∈ Icc t₀ τ, α t ∉ V := by
  have hmem : α ⁻¹' (closure V)ᶜ ∈ nhdsWithin τ (Icc (0 : ℝ) 1) :=
    hα τ ⟨hτ.1.le, hτ.2⟩ |>.preimage_mem_nhdsWithin
      (isClosed_closure.isOpen_compl.mem_nhds he)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hmem
  let t₀ := max 0 (τ - δ / 2)
  have ht₀ : t₀ ∈ Ico (0 : ℝ) τ := ⟨le_max_left _ _,
    max_lt hτ.1 (by dsimp [t₀]; linarith)⟩
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht hv
  have hd : dist t τ < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    have := le_max_right (0 : ℝ) (τ - δ / 2)
    dsimp [t₀] at ht
    linarith
  exact hball ⟨hd, ht₀.1.trans ht.1, ht.2.trans hτ.2⟩ (subset_closure hv)

end D5.S1.Dynamics.Shadowing.DendriteObstruction
