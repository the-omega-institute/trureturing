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

omit [CompactSpace X] in
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

omit [CompactSpace X] in
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

omit [CompactSpace X] in
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
    max_lt hτ.1 (by linarith)⟩
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht hv
  have hd : dist t τ < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    have htbound : τ - δ / 2 ≤ t := (le_max_right (0 : ℝ) (τ - δ / 2)).trans ht.1
    linarith
  exact hball ⟨hd, ht₀.1.trans ht.1, ht.2.trans hτ.2⟩ (subset_closure hv)

/-- In a nondegenerate compact path-connected metric space there are arbitrarily
small nonempty open sets whose complements are nonempty subcontinua. -/
theorem compact_path_small_opening
    (paths : ∀ c y : X, ∃ α : ℝ → X, ContinuousOn α (Icc (0 : ℝ) 1) ∧
      α 0 = c ∧ α 1 = y)
    (hnt : (univ : Set X).Nontrivial) {η : ℝ} (hη : 0 < η) :
    ∃ Q : Set X, IsCompact Q ∧ IsConnected Q ∧ Q ≠ univ ∧ Metric.diam Qᶜ < η := by
  classical
  obtain ⟨r, _, q, _, hrq⟩ := hnt
  have hr : ({r} : Set X) ≠ univ := by
    intro h
    have : q ∈ ({r} : Set X) := by rw [h]; trivial
    exact hrq this.symm
  obtain ⟨S, hScover⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => Metric.ball x (η / 8)) (fun _ => Metric.isOpen_ball)
    (fun x _ => mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by positivity)⟩)
  have hSn : S.Nonempty := by
    obtain ⟨x, hx, _⟩ := mem_iUnion₂.mp (hScover (mem_univ r))
    exact ⟨x, hx⟩
  let I := {x // x ∈ S}
  let : Nonempty I := by obtain ⟨x, hx⟩ := hSn; exact ⟨⟨x, hx⟩⟩
  let k := Fintype.card I
  have hk : 0 < k := Fintype.card_pos
  let enum := (Fintype.equivFin I).symm
  let V : I → Set X := fun i => Metric.ball i.1 (η / 8)
  let H : ℕ → Set X := fun n => V (enum ⟨n % k, Nat.mod_lt n hk⟩)
  have hrepeat (i : I) (N : ℕ) : ∃ n ≥ N, H n = V i := by
    let j := Fintype.equivFin I i
    let n := (N + 1) * k + j.1
    have hn : N ≤ n := by dsimp [n]; nlinarith
    refine ⟨n, hn, ?_⟩
    have hmod : n % k = j.1 := by
      simp [n, Nat.add_mod]
      exact Nat.mod_eq_of_lt (show j.1 < k from j.2)
    change V (enum ⟨n % k, Nat.mod_lt n hk⟩) = V i
    have hfin : (⟨n % k, Nat.mod_lt n hk⟩ : Fin k) = j := Fin.ext hmod
    rw [hfin]
    exact congrArg V ((Fintype.equivFin I).symm_apply_apply i)
  obtain ⟨C, W, hC0, hC, hstep, hW⟩ := opening_chain paths r hr H
    (fun _ => Metric.isOpen_ball)
  have hmono : Monotone C := monotone_nat_of_le_succ
    (fun n => (hstep n).trans interior_subset)
  let G := ⋃ n, C n
  have hGopen : IsOpen G := by
    have heq : G = ⋃ n, interior (C n) := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨n + 1, hstep n hn⟩
      · exact iUnion_mono (fun _ => interior_subset)
    rw [heq]
    exact isOpen_iUnion (fun _ => isOpen_interior)
  have hGp : G ≠ univ := by
    intro heq
    obtain ⟨N, hN⟩ := chain_union_absorbs hstep isCompact_univ
      (show (univ : Set X) ⊆ ⋃ n, C n from by rw [← heq])
    exact (hC N).2.2.1 (eq_univ_of_univ_subset hN)
  let K := Gᶜ
  have hKc : IsClosed K := hGopen.isClosed_compl
  obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hGp
  have hrG : r ∈ G := mem_iUnion.mpr ⟨0, hC0.symm ▸ (show r ∈ ({r} : Set X) from rfl)⟩
  obtain ⟨α, hα, hα0, hα1⟩ := paths r x
  obtain ⟨τ, hτ, hτK, hbefore⟩ := first_closed_hit hα hKc
    (by simpa [hα0, K] using hrG) (by simpa [hα1, K] using hx)
  let e := α τ
  have hV (i : I) (hi : (V i ∩ K).Nonempty) : e ∈ closure (V i) := by
    by_contra hbad
    obtain ⟨t₀, ht₀, htail⟩ := terminal_segment_avoids hα hτ hbad
    have hprefix : α '' Icc (0 : ℝ) t₀ ⊆ G := by
      rintro z ⟨t, ht, rfl⟩
      exact not_not.mp (hbefore t ⟨ht.1, ht.2.trans_lt ht₀.2⟩)
    have hpcompact : IsCompact (α '' Icc (0 : ℝ) t₀) :=
      isCompact_Icc.image_of_continuousOn
        (hα.mono (Icc_subset_Icc le_rfl (ht₀.2.le.trans hτ.2)))
    obtain ⟨N, hN⟩ := chain_union_absorbs hstep hpcompact hprefix
    obtain ⟨n, hn, hni⟩ := hrepeat i N
    have hWsub : W n ⊆ V i := by
      rcases (hW n).2.2.2 with h | h
      · exact hni ▸ h
      · obtain ⟨z, hzV, hzK⟩ := hi
        have hzG : z ∈ G := mem_iUnion.mpr ⟨n + 1, h (hni.symm ▸ hzV)⟩
        exact False.elim (hzK hzG)
    have hpathsub : α '' Icc (0 : ℝ) τ ⊆ (W n)ᶜ := by
      rintro z ⟨t, ht, rfl⟩ hw
      by_cases htpre : t ≤ t₀
      · have htc : α t ∈ C n := hmono hn (hN (mem_image_of_mem _ ⟨ht.1, htpre⟩))
        have htcomp : α t ∈ connectedComponentIn (W n)ᶜ r := by
          rw [← (hW n).2.2.1]
          exact interior_subset (hstep n htc)
        exact (connectedComponentIn_subset (W n)ᶜ r htcomp) hw
      · exact htail t ⟨(not_le.mp htpre).le, ht.2⟩ (hWsub hw)
    have hprecon : IsPreconnected (α '' Icc (0 : ℝ) τ) :=
      isPreconnected_Icc.image α (hα.mono (Icc_subset_Icc le_rfl hτ.2))
    have hrpath : r ∈ α '' Icc (0 : ℝ) τ :=
      ⟨0, ⟨le_rfl, hτ.1.le⟩, hα0⟩
    have hsub := hprecon.subset_connectedComponentIn hrpath hpathsub
    have heC : e ∈ C (n + 1) := by
      rw [(hW n).2.2.1]
      exact hsub (mem_image_of_mem _ ⟨hτ.1.le, le_rfl⟩)
    exact hτK (mem_iUnion.mpr ⟨n + 1, heC⟩)
  have hKball : K ⊆ Metric.ball e (η / 3) := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hScover (mem_univ z))
    let i : I := ⟨c, hc⟩
    have hecl := hV i ⟨z, hzc, hz⟩
    have hedist : dist e c ≤ η / 8 :=
      Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hecl)
    have hzdist : dist z c < η / 8 := Metric.mem_ball.mp hzc
    have := dist_triangle_right z e c
    rw [Metric.mem_ball]
    linarith
  have hFsub : (Metric.ball e (η / 3))ᶜ ⊆ G := by
    intro z hz
    by_contra hzg
    exact hz (hKball hzg)
  obtain ⟨N, hN⟩ := chain_union_absorbs hstep
    Metric.isOpen_ball.isClosed_compl.isCompact hFsub
  have hsmall : (C N)ᶜ ⊆ Metric.ball e (η / 3) := by
    intro z hz
    by_contra hzb
    exact hz (hN hzb)
  refine ⟨C N, (hC N).1, (hC N).2.1, (hC N).2.2.1, ?_⟩
  apply lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (by positivity : 0 ≤ 2 * (η / 3)) ?_)
    (by linarith : 2 * (η / 3) < η)
  intro a ha b hb
  have ha' := Metric.mem_ball.mp (hsmall ha)
  have hb' := Metric.mem_ball.mp (hsmall hb)
  exact (dist_triangle_right a b e).trans (by linarith)

end D5.S1.Dynamics.Shadowing.DendriteObstruction
