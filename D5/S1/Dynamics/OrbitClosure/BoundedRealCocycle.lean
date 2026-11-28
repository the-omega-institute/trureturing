/- GID: D5/S1/Dynamics/OrbitClosure/BoundedRealCocycle
   generality: G
   mirror-B: D5/B/S1/Dynamics/OrbitClosure/BoundedRealCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded real cocycles admit unique continuous normalized transfers. -/

module

public import Mathlib.Order.Zorn
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import OmegaBuild.Commands

/-! Continuous real transfers reconstructed from a bounded skew orbit. -/

compile_only_with_mathlib

open Set Function

namespace D5.S1.Dynamics.OrbitClosure.BoundedRealCocycle

universe u v

private theorem minimal_compact_invariant
    {G Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (F : G → Y → Y) (B : Set Y) (hBc : IsCompact B) (hBn : B.Nonempty)
    (hBi : ∀ g, MapsTo (F g) B B) :
    ∃ K : Set Y, K ⊆ B ∧ Minimal
      (fun K : Set Y => IsCompact K ∧ K.Nonempty ∧ ∀ g, MapsTo (F g) K K) K := by
  classical
  apply zorn_superset_nonempty
    {K : Set Y | IsCompact K ∧ K.Nonempty ∧ ∀ g, MapsTo (F g) K K}
    ?_ B ⟨hBc, hBn, hBi⟩
  intro c hc hchain hne
  let : Nonempty c := hne.to_subtype
  have hdir : Directed (· ⊇ ·) (fun s : c => (s.1 : Set Y)) := by
    intro s t
    rcases hchain.total s.2 t.2 with hst | hts
    · exact ⟨s, Subset.rfl, hst⟩
    · exact ⟨t, hts, Subset.rfl⟩
  have hnon := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun s : c => (s.1 : Set Y)) hdir (fun s => (hc s.2).2.1)
    (fun s => (hc s.2).1) (fun s => (hc s.2).1.isClosed)
  have hne' : (⋂₀ c).Nonempty := by simpa only [sInter_eq_iInter] using hnon
  obtain ⟨s, hs⟩ := hne
  refine ⟨⋂₀ c, ⟨?_, hne', ?_⟩, fun t ht => sInter_subset_of_mem ht⟩
  · exact (hc hs).1.of_isClosed_subset
      (isClosed_sInter fun t ht => (hc ht).1.isClosed) (sInter_subset_of_mem hs)
  · intro g y hy
    exact mem_sInter.mpr fun t ht => (hc ht).2.2 g (mem_sInter.mp hy t ht)

/-- A bound at one point reconstructs a unique continuous normalized transfer,
with the identical bound on the whole compact Hausdorff base. Only the supplied
multiplication and composition equations are required. -/
public theorem bounded_iff_existsUnique_transfer
    {Γ : Type u} {X : Type v} [Mul Γ]
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (a : Γ → X → X) (ha : ∀ g, Continuous (a g))
    (hmul : ∀ g h x, a (g * h) x = a g (a h x))
    (hdense : ∀ x, DenseRange (fun g => a g x))
    (c : Γ → X → ℝ) (hc : ∀ g, Continuous (c g))
    (hcoc : ∀ g h x, c (g * h) x = c g (a h x) + c h x)
    (x0 : X) (C : ℝ) :
    (∀ g, |c g x0| ≤ C) ↔
      ∃! φ : X → ℝ, Continuous φ ∧ φ x0 = 0 ∧
        (∀ g x, φ (a g x) - φ x = c g x) ∧ (∀ x, |φ x| ≤ C) := by
  classical
  constructor
  · intro hbound
    have hΓ : Nonempty Γ := by
      by_contra h
      have : IsEmpty Γ := not_nonempty_iff.mp h
      have hx := hdense x0 x0
      simp only [Set.range_eq_empty, closure_empty, mem_empty_iff_false] at hx
    let g0 : Γ := Classical.choice hΓ
    let F : Γ → X × ℝ → X × ℝ := fun g p => (a g p.1, p.2 + c g p.1)
    have hF (g : Γ) : Continuous (F g) :=
      (ha g |>.comp continuous_fst).prodMk
        (continuous_snd.add ((hc g).comp continuous_fst))
    let O : Set (X × ℝ) := range (fun g => (a g x0, c g x0))
    have hOc : IsCompact (closure O) := by
      apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-C) C))).of_isClosed_subset
        isClosed_closure
      apply closure_minimal ?_ (isClosed_univ.prod isClosed_Icc)
      rintro p ⟨g, rfl⟩
      exact ⟨mem_univ _, (abs_le.mp (hbound g))⟩
    have hOn : (closure O).Nonempty :=
      ⟨(a g0 x0, c g0 x0), subset_closure (mem_range_self g0)⟩
    have hOi (g : Γ) : MapsTo (F g) (closure O) (closure O) := by
      apply Set.MapsTo.closure ?_ (hF g)
      rintro p ⟨h, rfl⟩
      refine ⟨g * h, ?_⟩
      simp only [F, hmul, hcoc]
      congr 1
      exact add_comm _ _
    obtain ⟨K, _, hmin⟩ := minimal_compact_invariant F (closure O) hOc hOn hOi
    have hKc := hmin.prop.1
    have hKn := hmin.prop.2.1
    have hKi := hmin.prop.2.2
    have hsurj : ∀ x : X, ∃ t : ℝ, (x, t) ∈ K := by
      obtain ⟨p, hp⟩ := hKn
      have hcl : IsClosed (Prod.fst '' K) := (hKc.image continuous_fst).isClosed
      have hsub : range (fun g => a g p.1) ⊆ Prod.fst '' K := by
        rintro _ ⟨g, rfl⟩
        exact ⟨F g p, hKi g hp, rfl⟩
      intro x
      obtain ⟨q, hq, hqx⟩ := closure_minimal hsub hcl (hdense p.1 x)
      exact ⟨q.2, hqx ▸ hq⟩
    have hsingle : ∀ x v w, (x, v) ∈ K → (x, w) ∈ K → v = w := by
      intro x v w hv hw
      let d := w - v
      let T : X × ℝ → X × ℝ := fun p => (p.1, p.2 - d)
      have hT : Continuous T := continuous_fst.prodMk (continuous_snd.sub continuous_const)
      let Q : Set (X × ℝ) := K ∩ T ⁻¹' K
      have hQc : IsCompact Q := hKc.inter_right (hKc.isClosed.preimage hT)
      have hQn : Q.Nonempty := by
        refine ⟨(x, w), hw, ?_⟩
        change (x, w - (w - v)) ∈ K
        have he : w - (w - v) = v := by linarith
        rw [he]
        exact hv
      have hQi : ∀ g, MapsTo (F g) Q Q := by
        intro g p hp
        refine ⟨hKi g hp.1, ?_⟩
        have hh := hKi g hp.2
        change (a g p.1, p.2 - d + c g p.1) ∈ K at hh
        change (a g p.1, p.2 + c g p.1 - d) ∈ K
        have he : p.2 + c g p.1 - d = p.2 - d + c g p.1 := by linarith
        rw [he]
        exact hh
      have hKQ : K ⊆ Q := hmin.2 ⟨hQc, hQn, hQi⟩ inter_subset_left
      obtain ⟨p, hp, hlow⟩ := hKc.exists_isMinOn hKn continuous_snd.continuousOn
      obtain ⟨q, hq, hhigh⟩ := hKc.exists_isMaxOn hKn continuous_snd.continuousOn
      have hl := hlow (hKQ hp).2
      have hh := hhigh (hKQ hq).2
      change p.2 ≤ p.2 - (w - v) at hl
      change q.2 - (w - v) ≤ q.2 at hh
      linarith
    let π : K → X := fun p => p.1.1
    have hπc : Continuous π := continuous_fst.comp continuous_subtype_val
    have hπbij : Bijective π := by
      constructor
      · intro p q he
        change p.1.1 = q.1.1 at he
        apply Subtype.ext
        apply Prod.ext he
        apply hsingle p.1.1 p.1.2 q.1.2 p.2
        rw [he]
        exact q.2
      · intro x
        obtain ⟨t, ht⟩ := hsurj x
        exact ⟨⟨(x, t), ht⟩, rfl⟩
    let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    let e : K ≃ X := Equiv.ofBijective π hπbij
    let H : K ≃ₜ X := hπc.homeoOfEquivCompactToT2 (f := e)
    let ψ : X → ℝ := fun x => (H.symm x).1.2
    have hψc : Continuous ψ := continuous_snd.comp
      (continuous_subtype_val.comp H.symm.continuous)
    have hψK (x : X) : (x, ψ x) ∈ K := by
      have he : (H.symm x).1.1 = x := H.apply_symm_apply x
      have hp : (x, ψ x) = (H.symm x).1 := Prod.ext he.symm rfl
      rw [hp]
      exact (H.symm x).2
    have hψeq (g : Γ) (x : X) : ψ (a g x) - ψ x = c g x := by
      have hh := hsingle (a g x) (ψ (a g x)) (ψ x + c g x)
        (hψK (a g x)) (hKi g (hψK x))
      linarith
    let φ : X → ℝ := fun x => ψ x - ψ x0
    have hφc : Continuous φ := hψc.sub continuous_const
    have hφ0 : φ x0 = 0 := sub_self _
    have hφeq (g : Γ) (x : X) : φ (a g x) - φ x = c g x := by
      dsimp [φ]
      linarith [hψeq g x]
    have hφbound : ∀ x, |φ x| ≤ C := by
      intro x
      apply (hdense x0).induction_on (p := fun y : X => |φ y| ≤ C)
        x (isClosed_le hφc.abs continuous_const)
      intro g
      have he : φ (a g x0) = c g x0 := by linarith [hφeq g x0]
      rw [he]
      exact hbound g
    refine ⟨φ, ⟨hφc, hφ0, hφeq, hφbound⟩, ?_⟩
    rintro θ ⟨hθc, hθ0, hθeq, _⟩
    apply (hdense x0).equalizer hθc hφc
    funext g
    dsimp only [comp_apply]
    linarith [hθeq g x0, hφeq g x0]
  · rintro ⟨φ, ⟨_, h0, heq, hb⟩, _⟩ g
    have hh := heq g x0
    rw [h0, sub_zero] at hh
    rw [← hh]
    exact hb _

end D5.S1.Dynamics.OrbitClosure.BoundedRealCocycle
