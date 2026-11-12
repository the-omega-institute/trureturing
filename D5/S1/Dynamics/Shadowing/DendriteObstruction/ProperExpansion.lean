/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proper continuum neighbourhoods in compact path connected metric spaces. -/

import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic
import D5.S1.Dynamics.Shadowing.DendriteObstruction.TentObstruction

/-! Proper continuum neighbourhoods and their folding obstruction. -/

open Set Function Filter TopologicalSpace
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X]

theorem compact_component {F : Set X} (hF : IsCompact F) {c : X} (hc : c ∈ F) :
    IsCompact (connectedComponentIn F c) := by
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  rw [connectedComponentIn_eq_image hc]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

private theorem component_separation {F : Set X} (hF : IsCompact F)
    {c e : X} (hc : c ∈ F) (he : e ∈ F) (hne : e ∉ connectedComponentIn F c) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ A ∪ B = F ∧ Disjoint A B ∧
      connectedComponentIn F c ⊆ A ∧ e ∈ B := by
  classical
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  have hn : (⟨e, he⟩ : F) ∉ connectedComponent (⟨c, hc⟩ : F) := by
    intro h
    apply hne
    rw [connectedComponentIn_eq_image hc]
    exact mem_image_of_mem _ h
  rw [connectedComponent_eq_iInter_isClopen] at hn
  simp only [mem_iInter, not_forall] at hn
  obtain ⟨S, hS⟩ := hn
  let A := Subtype.val '' (S : Set F)
  let B := Subtype.val '' (S : Set F)ᶜ
  have hAc : IsClosed A := (S.2.1.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hBc : IsClosed B := (S.2.1.isOpen.isClosed_compl.isCompact.image
    continuous_subtype_val).isClosed
  refine ⟨A, B, hAc, hBc, ?_, ?_, ?_, ⟨⟨e, he⟩, hS, rfl⟩⟩
  · change Subtype.val '' (S : Set F) ∪ Subtype.val '' (S : Set F)ᶜ = F
    rw [← image_union, union_compl_self, image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
  · exact Set.disjoint_image_of_injective Subtype.val_injective disjoint_compl_right
  · rw [connectedComponentIn_eq_image hc]
    exact image_mono (isPreconnected_connectedComponent.subset_isClopen S.2.1 ⟨⟨c, hc⟩, mem_connectedComponent, S.2.2⟩)

private theorem fold_successor [CompactSpace X] {C : Set X}
    (hC : IsConnected C)
    (hfail : ∀ B : Set X, IsCompact B → IsConnected B → B ≠ univ → ¬ C ⊆ interior B)
    {f : X → ℝ} (hf : Continuous f) (hr : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hzero : C ⊆ interior (f ⁻¹' {0})) (hone : (interior (f ⁻¹' {1})).Nonempty) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      C ⊆ interior (g ⁻¹' {0}) ∧ (interior (g ⁻¹' {1})).Nonempty ∧
      ∀ x, continuumTent (g x) = f x := by
  classical
  obtain ⟨c, hc⟩ := hC.nonempty
  let F := (interior (f ⁻¹' {1}))ᶜ
  have hFc : IsCompact F := isOpen_interior.isClosed_compl.isCompact
  have zeroF : f ⁻¹' {0} ⊆ F := by
    intro x hx h1
    have := interior_subset h1
    simp only [mem_preimage, mem_singleton_iff] at hx this
    linarith
  have hCF : C ⊆ F := hzero.trans (interior_subset.trans zeroF)
  let J := connectedComponentIn F c
  have hCJ : C ⊆ J := hC.isPreconnected.subset_connectedComponentIn hc hCF
  have hJc : IsCompact J := compact_component hFc (hCF hc)
  have hJcon : IsConnected J := isConnected_connectedComponentIn_iff.mpr (hCF hc)
  have hJp : J ≠ univ := by
    intro h
    obtain ⟨z, hz⟩ := hone
    exact (connectedComponentIn_subset F c (show z ∈ J by rw [h]; trivial)) hz
  have hbad := hfail J hJc hJcon hJp
  obtain ⟨c', hc', hc'J⟩ := Set.not_subset.mp hbad
  have hnot : ¬ interior (f ⁻¹' {0}) ⊆ J := by
    intro hh
    exact hc'J ((interior_maximal hh isOpen_interior) (hzero hc'))
  obtain ⟨e, he0, heJ⟩ := Set.not_subset.mp hnot
  obtain ⟨A, B, hA, hB, hAB, hd, hJA, heB⟩ :=
    component_separation hFc (hCF hc) (zeroF (interior_subset he0)) heJ
  have hCA : C ⊆ A := hCJ.trans hJA
  let P := A ∪ f ⁻¹' {1}
  let Q := B ∪ f ⁻¹' {1}
  have h1c : IsClosed (f ⁻¹' {1}) := isClosed_singleton.preimage hf
  have hcover : P ∪ Q = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases h : x ∈ F
    · have hx : x ∈ A ∪ B := hAB.symm ▸ h
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
    · exact Or.inl (Or.inr (interior_subset (not_not.mp h)))
  let g : X → ℝ := fun x => if x ∈ B then 1 - f x / 2 else f x / 2
  have hgP : EqOn g (fun x => f x / 2) P := by
    intro x hx
    dsimp [g]
    split_ifs with hb
    · have hx1 : f x = 1 := by
        rcases hx with ha | ha
        · exact False.elim (Set.disjoint_left.mp hd ha hb)
        · exact ha
      rw [hx1]
      norm_num
    · rfl
  have hgQ : EqOn g (fun x => 1 - f x / 2) Q := by
    intro x hx
    dsimp [g]
    split_ifs with hb
    · rfl
    · have hx1 : f x = 1 := by
        rcases hx with hx | hx
        · exact False.elim (hb hx)
        · exact hx
      rw [hx1]
      norm_num
  have hgc : Continuous g := by
    rw [← continuousOn_univ, ← hcover]
    exact ((hf.div_const 2).continuousOn.congr hgP).union_of_isClosed
      ((continuous_const.sub (hf.div_const 2)).continuousOn.congr hgQ)
      (hA.union h1c) (hB.union h1c)
  have hgz : interior (f ⁻¹' {0}) \ B ⊆ g ⁻¹' {0} := by
    intro x hx
    have hx0 : f x = 0 := show x ∈ f ⁻¹' {0} from interior_subset hx.1
    simp [g, hx.2, hx0]
  have hgo : interior (f ⁻¹' {0}) \ A ⊆ g ⁻¹' {1} := by
    intro x hx
    have hx0 : f x = 0 := show x ∈ f ⁻¹' {0} from interior_subset hx.1
    have hxB : x ∈ B := by
      have := hAB.symm ▸ zeroF (interior_subset hx.1)
      exact this.resolve_left hx.2
    simp [g, hxB, hx0]
  refine ⟨g, hgc, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp [g]
    split_ifs <;> constructor <;> linarith [(hr x).1, (hr x).2]
  · have hCB : C ⊆ interior (f ⁻¹' {0}) \ B := by
      intro x hx
      exact ⟨hzero hx, fun hb => Set.disjoint_left.mp hd (hCA hx) hb⟩
    exact hCB.trans (interior_maximal hgz (isOpen_interior.sdiff hB))
  · refine ⟨e, interior_maximal hgo (isOpen_interior.sdiff hA) ⟨he0, ?_⟩⟩
    exact fun heA => Set.disjoint_left.mp hd heA heB
  · intro x
    dsimp [g]
    split_ifs
    · exact (continuumTent_half (hr x)).2
    · exact (continuumTent_half (hr x)).1

private theorem initial_fold [CompactSpace X] {C : Set X} (hC : IsCompact C)
    (hproper : C ≠ univ) :
    ∃ f : X → ℝ, Continuous f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      C ⊆ interior (f ⁻¹' {0}) ∧ (interior (f ⁻¹' {1})).Nonempty := by
  classical
  obtain ⟨z, hz⟩ := Set.nonempty_compl.mpr hproper
  obtain ⟨A, _, hA, hCA, hAz⟩ := exists_compact_closed_between hC
    (isClosed_singleton (x := z)).isOpen_compl
    (show C ⊆ ({z} : Set X)ᶜ from fun x hx he => hz (he ▸ hx))
  have hzA : z ∉ A := fun h => hAz h rfl
  obtain ⟨B, _, hB, hzB, hBA⟩ := exists_compact_closed_between isCompact_singleton
    hA.isOpen_compl (singleton_subset_iff.mpr hzA)
  obtain ⟨f, hf0, hf1, hfr⟩ := exists_continuous_zero_one_of_isClosed hA hB
    (Set.disjoint_left.mpr (fun x hxA hxB => hBA hxB hxA))
  refine ⟨f, f.continuous, hfr, hCA.trans (interior_mono hf0),
    z, interior_mono hf1 (hzB rfl)⟩

/-- Every proper subcontinuum of a compact path-connected metric space has a
proper compact connected neighbourhood. The path hypothesis refers to actual
continuous maps of the closed real unit interval. -/
theorem proper_continuum_expansion [CompactSpace X]
    (paths : ∀ c y : X, ∃ α : ℝ → X, ContinuousOn α (Icc (0 : ℝ) 1) ∧
      α 0 = c ∧ α 1 = y)
    {C : Set X} (hCc : IsCompact C) (hC : IsConnected C) (hproper : C ≠ univ) :
    ∃ B : Set X, IsCompact B ∧ IsConnected B ∧ B ≠ univ ∧ C ⊆ interior B := by
  classical
  by_contra hn
  have hfail : ∀ B : Set X, IsCompact B → IsConnected B → B ≠ univ →
      ¬ C ⊆ interior B := by
    intro B hb hc hp hi
    exact hn ⟨B, hb, hc, hp, hi⟩
  let Stage := {f : C(X, ℝ) // (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
    C ⊆ interior (f ⁻¹' {0}) ∧ (interior (f ⁻¹' {1})).Nonempty}
  obtain ⟨f₀, hf₀, hr₀, hz₀, ho₀⟩ := initial_fold hCc hproper
  let s₀ : Stage := ⟨⟨f₀, hf₀⟩, hr₀, hz₀, ho₀⟩
  have step_exists (s : Stage) : ∃ t : Stage,
      ∀ x, continuumTent (t.1 x) = s.1 x := by
    obtain ⟨g, hg, hr, hz, ho, ht⟩ := fold_successor hC hfail
      s.1.continuous s.2.1 s.2.2.1 s.2.2.2
    exact ⟨⟨⟨g, hg⟩, hr, hz, ho⟩, ht⟩
  choose step hstep using step_exists
  let s : ℕ → Stage := fun n => step^[n] s₀
  let f : ℕ → X → ℝ := fun n => (s n).1
  have hf (n : ℕ) : Continuous (f n) := (s n).1.continuous
  have hz (n : ℕ) : C ⊆ interior ((f n) ⁻¹' {0}) := (s n).2.2.1
  have ho (n : ℕ) : (interior ((f n) ⁻¹' {1})).Nonempty := (s n).2.2.2
  have hcompat (n : ℕ) (x : X) : continuumTent (f (n + 1) x) = f n x := by
    change continuumTent ((step^[n + 1] s₀).1 x) = (step^[n] s₀).1 x
    rw [iterate_succ_apply']
    exact hstep _ x
  obtain ⟨c, hc⟩ := hC.nonempty
  have hc0 (n : ℕ) : f n c = 0 := show c ∈ (f n) ⁻¹' {0} from interior_subset (hz n hc)
  let K : ℕ → Set X := fun n => (f n) ⁻¹' {2 / 3}
  have hKclosed (n : ℕ) : IsClosed (K n) := isClosed_singleton.preimage (hf n)
  have hKne (n : ℕ) : (K n).Nonempty := by
    obtain ⟨z, hz⟩ := ho n
    have hz1 : f n z = 1 := show z ∈ (f n) ⁻¹' {1} from interior_subset hz
    obtain ⟨α, hα, hα0, hα1⟩ := paths c z
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((hf n).comp_continuousOn hα)
      (show (2 / 3 : ℝ) ∈ Icc (f n (α 0)) (f n (α 1)) from by
        rw [hα0, hα1, hc0, hz1]; norm_num)
    exact ⟨α t, ht⟩
  have hKnest (n : ℕ) : K (n + 1) ⊆ K n := by
    intro x hx
    change f (n + 1) x = 2 / 3 at hx
    change f n x = 2 / 3
    rw [← hcompat, hx]
    norm_num [continuumTent]
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hKnest hKne (hKclosed 0).isCompact hKclosed
  have hyf (n : ℕ) : f n y = 2 / 3 := mem_iInter.mp hy n
  have hiter (m n : ℕ) (x : X) : continuumTent^[m] (f (n + m) x) = f n x := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [iterate_succ_apply, ← Nat.add_assoc, hcompat, ih]
  obtain ⟨α, hα, hα0, hα1⟩ := paths c y
  apply no_unbounded_tent_lifts ((hf 0).comp_continuousOn hα)
  intro m
  refine ⟨fun t => f m (α t), (hf m).comp_continuousOn hα, ?_, ?_, ?_⟩
  · change f m (α 0) = 0
    rw [hα0, hc0]
  · change f m (α 1) = 2 / 3
    rw [hα1, hyf]
  · intro t _
    simpa using (hiter m 0 (α t)).symm

end D5.S1.Dynamics.Shadowing.DendriteObstruction
