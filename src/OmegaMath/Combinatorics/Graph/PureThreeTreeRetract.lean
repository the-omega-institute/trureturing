import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.PureThreeTreeBanach

compile_only_with_mathlib

/-! Any prefix-closed selection of the replicated histories, including the root,
is a simplicial retract. -/

namespace Omega.PureThreeTree
open SimpleGraph Omega.RollingCliques

noncomputable section
variable {n k : ℕ}

private def deepest (S : Set (History n k)) (h₀ : History.initial ∈ S) (b : History n k) :
    History n k := by
  classical
  let candidates := Finset.univ.filter fun a : History n k => a ∈ S ∧ a.IsPrefix b
  have hs : candidates.Nonempty :=
    ⟨History.initial, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₀, History.initial_prefix _⟩⟩
  exact (Finset.exists_max_image candidates (fun a => a.stage.val) hs).choose

private theorem deepest_spec (S : Set (History n k)) (h₀ : History.initial ∈ S) (b : History n k) :
    deepest S h₀ b ∈ S ∧ (deepest S h₀ b).IsPrefix b ∧
      ∀ a ∈ S, a.IsPrefix b → a.stage ≤ (deepest S h₀ b).stage := by
  classical
  let candidates := Finset.univ.filter fun a : History n k => a ∈ S ∧ a.IsPrefix b
  have hs : candidates.Nonempty :=
    ⟨History.initial, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₀, History.initial_prefix _⟩⟩
  have hh := (Finset.exists_max_image candidates (fun a => a.stage.val) hs).choose_spec
  have he : (Finset.exists_max_image candidates (fun a => a.stage.val) hs).choose =
      deepest S h₀ b := by unfold deepest; rfl
  rw [he] at hh
  have hm := (Finset.mem_filter.mp hh.1).2
  exact ⟨hm.1, hm.2, fun a ha hb => hh.2 a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hb⟩)⟩

private theorem prefix_of_stage_le {a b c : History n k} (ha : a.IsPrefix c) (hb : b.IsPrefix c)
    (hab : a.stage ≤ b.stage) : a.IsPrefix b := by
  exact ⟨hab, fun i hi => (ha.2 i hi).trans (hb.2 i (hi.trans hab)).symm⟩

private def prefixRetraction (S : Set (History n k)) (h₀ : History.initial ∈ S)
    (v : Vertex n k) : Vertex n k := by
  classical
  exact if v.val.1 ∈ S then v else birth (deepest S h₀ v.val.1)

/-- The induced subgraph on any prefix-closed set of histories containing the root
has a vertex retraction carrying each edge to an edge or to a point. -/
theorem exists_prefix_closed_retraction (S : Set (History n k)) (h₀ : History.initial ∈ S)
    (hS : ∀ {a b}, a.IsPrefix b → b ∈ S → a ∈ S) :
    ∃ ρ : Vertex n k → Vertex n k,
      (∀ v, (ρ v).val.1 ∈ S) ∧ (∀ v, v.val.1 ∈ S → ρ v = v) ∧
      ∀ u v, (graph n k).Adj u v → ρ u = ρ v ∨ (graph n k).Adj (ρ u) (ρ v) := by
  classical
  let ρ := prefixRetraction S h₀
  have hfix (v : Vertex n k) (hv : v.val.1 ∈ S) : ρ v = v :=
    ite_eq_left hv
  have hmove (v : Vertex n k) (hv : v.val.1 ∉ S) : ρ v = birth (deepest S h₀ v.val.1) :=
    ite_eq_right hv
  refine ⟨ρ, fun v => ?_, hfix, ?_⟩
  · by_cases hv : v.val.1 ∈ S
    · rwa [hfix v hv]
    · rw [hmove v hv]
      exact (deepest_spec S h₀ v.val.1).1
  · have forward (u v : Vertex n k) (huv : (graph n k).Adj u v) (hd : depth u ≤ depth v) :
        ρ u = ρ v ∨ (graph n k).Adj (ρ u) (ρ v) := by
      have hp := (rolling_earlier data huv hd).1
      by_cases hv : v.val.1 ∈ S
      · rw [hfix v hv, hfix u (hS hp hv)]
        exact Or.inr huv
      rw [hmove v hv]
      let w := deepest S h₀ v.val.1
      have hw := deepest_spec S h₀ v.val.1
      by_cases hu : u.val.1 ∈ S
      · rw [hfix u hu]
        by_cases he : u = birth w
        · exact Or.inl he
        right
        refine ⟨fun h => he (Subtype.ext h), ?_⟩
        by_cases hh : u.val.1 = w
        · exact Or.inl hh
        have huw : u.val.1.IsPrefix w :=
          prefix_of_stage_le hp hw.2.1 (hw.2.2 u.val.1 hu hp)
        have hne : u.val.1 ≠ v.val.1 := fun hh => hv (hh ▸ hu)
        have hret := (rolling_earlier data huv hd).2.resolve_left hne
        exact Or.inr (Or.inl ⟨huw, data.nested hw.2.1 hret⟩)
      · rw [hmove u hu]
        left
        let w' := deepest S h₀ u.val.1
        have hw' := deepest_spec S h₀ u.val.1
        have hwu : w.IsPrefix u.val.1 := by
          rcases data.comparable hw.2.1 hp with h | h
          · exact h
          · exact (hu (hS h hw.1)).elim
        have hww' : w.IsPrefix w' := prefix_of_stage_le hwu hw'.2.1 (hw'.2.2 w hw.1 hwu)
        have he : w'.stage = w.stage :=
          le_antisymm (hw.2.2 w' hw'.1 (data.trans hw'.2.1 hp)) hww'.1
        exact congrArg birth ((History.IsPrefix.eq_of_stage_eq hww' he.symm).symm)
    intro u v huv
    rcases le_total (depth u) (depth v) with hd | hd
    · exact forward u v huv hd
    · exact (forward v u huv.symm hd).imp Eq.symm Adj.symm

universe u

/-- A prefix-closed induced copy inherits the universal Banach budget of the
replicated history graph through its simplicial retraction. -/
theorem banach_of_prefix_closed_embedding {X : Type*} {J : SimpleGraph X}
    {S : Set (History n k)} (h₀ : History.initial ∈ S)
    (hS : ∀ {a b}, a.IsPrefix b → b ∈ S → a ∈ S)
    (f : X ↪ Vertex n k)
    (hf : ∀ x y, (graph n k).Adj (f x) (f y) ↔ J.Adj x y)
    (himage : Set.range f = {v | v.val.1 ∈ S})
    {R : ℝ} (h : BanachFeasible.{u} n k R)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : X → X → E) (hg : ∀ x y, g y x = -g x y)
    (ht : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z →
      ‖g x y + g y z - g x z‖ ≤ 1) :
    ∃ p : X → E, ∀ x y, J.Adj x y → ‖g x y - (p y - p x)‖ ≤ R := by
  classical
  obtain ⟨ρ, hm, hfix, hadj⟩ := exists_prefix_closed_retraction S h₀ hS
  have hpre (v : Vertex n k) : ∃ x, f x = ρ v := by
    rw [← Set.mem_range, himage]
    exact hm v
  let ρ' (v : Vertex n k) := (hpre v).choose
  have hid (v : Vertex n k) : f (ρ' v) = ρ v := (hpre v).choose_spec
  have hfix' (x : X) : ρ' (f x) = x := by
    apply f.injective
    rw [hid, hfix]
    have hmem : f x ∈ Set.range f := ⟨x, rfl⟩
    rwa [himage] at hmem
  have hadj' (a b : Vertex n k) (ha : (graph n k).Adj a b) :
      ρ' a = ρ' b ∨ J.Adj (ρ' a) (ρ' b) := by
    rcases hadj a b ha with he | hn
    · exact Or.inl (f.injective ((hid a).trans (he.trans (hid b).symm)))
    · exact Or.inr ((hf _ _).1 ((hid a).symm ▸ (hid b).symm ▸ hn))
  have diag (x : X) : g x x = 0 := by
    have hh : (2 : ℝ) • g x x = 0 := by
      rw [two_smul]
      exact (congrArg (fun y => y + g x x) (hg x x)).trans (neg_add_cancel _)
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  let g' (a b : Vertex n k) := g (ρ' a) (ρ' b)
  have htri (a b c : Vertex n k) (hab : (graph n k).Adj a b)
      (hbc : (graph n k).Adj b c) (hac : (graph n k).Adj a c) :
      ‖g' a b + g' b c - g' a c‖ ≤ 1 := by
    unfold g'
    rcases hadj' a b hab with e | e
    · simp [e, diag]
    rcases hadj' b c hbc with d | d
    · simp [d, diag]
    rcases hadj' a c hac with t | t
    · rw [t, hg (ρ' b) (ρ' c), diag, neg_add_cancel, sub_zero, norm_zero]
      norm_num
    exact ht _ _ _ e d t
  obtain ⟨p, hp⟩ := h E g' (fun a b => hg _ _) htri
  exact ⟨fun a => p (f a), fun a b e => by
    simpa [g', hfix'] using hp (f a) (f b) ((hf a b).2 e)⟩

end
end Omega.PureThreeTree
