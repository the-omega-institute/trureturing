/- GID: D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A full centerless socle has simple independent actual factors. -/

import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Order.Minimal

set_option autoImplicit false

/-!
Elementary structure suppliers for Nikolov--Segal (2011), Proposition 3, Case 1.
These proofs use normal-subgroup minimality and finite internal products, not CFSG.
-/
namespace NikolovSegal
universe u v
variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- Actual minimal nontrivial normal subgroups, not composition-factor labels. -/
abbrev MinimalNormalFactor (G : Type u) [Group G] :=
  {M : Subgroup G // Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) M}

/-- The join of the minimal nontrivial normal subgroups. -/
def minimalNormalSocle (G : Type u) [Group G] : Subgroup G :=
  ⨆ M : MinimalNormalFactor G, M.val

/-- Automorphisms transport minimal normal subgroups, with all minimality retained. -/
theorem minimal_normal_map_equiv {M : Subgroup G}
    (hM : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) M) (e : G ≃* Q) :
    Minimal (fun K : Subgroup Q => K.Normal ∧ K ≠ ⊥) (M.map e.toMonoidHom) := by
  refine ⟨⟨hM.prop.1.map e.toMonoidHom e.surjective, ?_⟩, ?_⟩
  · intro h
    apply hM.prop.2
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using h
  · intro K hK hle
    have hc : (K.comap e.toMonoidHom).Normal := hK.1.comap e.toMonoidHom
    have hcb : K.comap e.toMonoidHom ≠ ⊥ := by
      intro h
      apply hK.2
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective K,
        h, Subgroup.map_bot]
    have hcm : K.comap e.toMonoidHom ≤ M := by
      intro x hx
      obtain ⟨y, hy, he⟩ := hle hx
      exact e.injective he ▸ hy
    have heq := hM.eq_of_le ⟨hc, hcb⟩ hcm
    rw [← heq, Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]

/-- The socle is characteristic; the proof transports its actual factors. -/
theorem minimalNormalSocle_characteristic : (minimalNormalSocle G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  rw [minimalNormalSocle, Subgroup.map_iSup]
  apply iSup_le
  intro M
  exact le_iSup_of_le ⟨M.val.map e.toMonoidHom, minimal_normal_map_equiv M.property e⟩ le_rfl

/-- Distinct minimal normal subgroups commute element by element. -/
theorem minimal_normal_factors_commute :
    Pairwise fun M L : MinimalNormalFactor G =>
      ∀ x y : G, x ∈ M.val → y ∈ L.val → Commute x y := by
  intro M L hne
  have hM : M.val.Normal := M.property.prop.1
  have hL : L.val.Normal := L.property.prop.1
  let := hM
  let := hL
  have hi : M.val ⊓ L.val = ⊥ := by
    by_contra h
    have hm := M.property.eq_of_le ⟨inferInstance, h⟩ inf_le_left
    have hl := L.property.eq_of_le ⟨inferInstance, h⟩ inf_le_right
    exact hne (Subtype.ext (hm.symm.trans hl))
  have hc : ⁅M.val, L.val⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_le_inf M.val L.val).trans_eq hi)
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  intro x y hx hy
  exact (hcen hx y hy).symm

/-- If the socle fills the group, every minimal normal factor is simple.
A subgroup normal in one factor is normalized by that factor and centralized by all
other factors, so is normal in the whole group. This is the nontrivial normality
step that cannot be replaced by falsely asserting normality is transitive. -/
theorem simple_minimal_normal_factor_of_socle_eq_top
    (hs : minimalNormalSocle G = ⊤) (M : MinimalNormalFactor G) :
    IsSimpleGroup M.val := by
  apply Subgroup.isSimpleGroup_iff.mpr
  refine ⟨M.property.prop.2, ?_⟩
  intro K hKM hKn
  have hn : M.val ≤ Subgroup.normalizer K :=
    Subgroup.normal_subgroupOf_iff_le_normalizer hKM |>.mp hKn
  have hfull : (⊤ : Subgroup G) ≤ Subgroup.normalizer K := by
    rw [← hs, minimalNormalSocle]
    apply iSup_le
    intro L
    by_cases hLM : L = M
    · simpa [hLM] using hn
    · apply Subgroup.le_normalizer_iff.mpr
      intro l hl k hk
      have hc := minimal_normal_factors_commute hLM l k hl (hKM hk)
      simpa [hc.eq, mul_assoc] using hk
  have hnormal : K.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hfull)
  by_cases hKb : K = ⊥
  · exact Or.inl hKb
  · exact Or.inr (M.property.eq_of_le ⟨hnormal, hKb⟩ hKM)

/-- Centerlessness upgrades pairwise disjointness to full independence.
Pairwise disjoint subgroups alone would not justify an internal direct product. -/
theorem minimal_normal_factors_independent (hs : minimalNormalSocle G = ⊤)
    (hz : Subgroup.center G = ⊥) :
    iSupIndep (fun M : MinimalNormalFactor G => M.val) := by
  intro M
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hr : (⨆ L : MinimalNormalFactor G, ⨆ (_ : L ≠ M), L.val) ≤
      Subgroup.centralizer (M.val : Set G) := by
    apply iSup₂_le
    intro L hLM l hl m hm
    exact (minimal_normal_factors_commute hLM l m hl hm).symm.eq
  have hc : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← hs, minimalNormalSocle]
    apply iSup_le
    intro L y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz'
    have he : z = x := Set.mem_singleton_iff.mp hz'
    subst z
    by_cases hLM : L = M
    · subst L
      exact (hr hx.2 y hy).symm
    · exact (minimal_normal_factors_commute hLM y x hy hx.1).symm.eq
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hc (Subgroup.mem_top y) x (Set.mem_singleton x)).symm
  rwa [hz] at hxc

/-- In a centerless group filled by its socle every factor is nonabelian. -/
theorem noncommutative_minimal_normal_factor_of_socle_eq_top
    (hs : minimalNormalSocle G = ⊤) (hz : Subgroup.center G = ⊥)
    (M : MinimalNormalFactor G) : ¬IsMulCommutative M.val := by
  intro hm
  let := hm
  have hc : M.val ≤ Subgroup.center G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have ht : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hs, minimalNormalSocle]
      apply iSup_le
      intro L z hz'
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have he : w = x := Set.mem_singleton_iff.mp hw
      subst w
      by_cases hLM : L = M
      · subst L
        exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : M.val) ⟨z, hz'⟩)
      · exact (minimal_normal_factors_commute hLM z x hz' hx).symm.eq
    exact (ht (Subgroup.mem_top y) x (Set.mem_singleton x)).symm
  exact M.property.prop.2 (le_bot_iff.mp (hc.trans_eq hz))

end NikolovSegal
