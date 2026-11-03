/- GID: D5/S3/GraphInvariants/FiniteGraphDominationCollapse
   generality: G
   mirror-B: D5/B/S3/GraphInvariants/FiniteGraphDominationCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Domination constructs finite elementary free-pair collapses. -/
import D5.S3.Geometry.FiniteGraphVertexSubstitution
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation

/-!
# Finite domination collapses

The classical free-face deletion argument is performed on nonempty faces,
keeping the original vertex carrier. No realization or matching-to-collapse
principle is assumed. Elementary simplicial collapse is classical; the
path argument in C-28.8 motivates the cardinality order but is not used as
a general domination theorem.
-/

noncomputable section

namespace D5.S3.GraphInvariants

namespace FiniteSimplicialCollapse
universe u
variable {V : Type u} [DecidableEq V]

/-- Delete a nonempty face and its unique proper coface, which adds one vertex. -/
def ElementaryCollapse (K L : PreAbstractSimplicialComplex V) : Prop :=
  ∃ (σ : Finset V) (a : V), σ.Nonempty ∧ σ ∈ K ∧ a ∉ σ ∧
    insert a σ ∈ K ∧
    (∀ τ ∈ K, σ ⊂ τ → τ = insert a σ) ∧
    ∀ τ, τ ∈ L ↔ τ ∈ K ∧ τ ≠ σ ∧ τ ≠ insert a σ

/-- A finite, possibly empty sequence of elementary collapses. -/
def Collapses : PreAbstractSimplicialComplex V → PreAbstractSimplicialComplex V → Prop :=
  Relation.ReflTransGen ElementaryCollapse

private def deletePair (K : PreAbstractSimplicialComplex V) (σ : Finset V) (a : V)
    (ha : a ∉ σ) (hfree : ∀ τ ∈ K, σ ⊂ τ → τ = insert a σ) :
    PreAbstractSimplicialComplex V where
  faces := {τ | τ ∈ K ∧ τ ≠ σ ∧ τ ≠ insert a σ}
  isRelLowerSet_faces := by
    rintro τ ⟨hτ, hnσ, hnu⟩
    refine ⟨(K.isRelLowerSet_faces hτ).1, ?_⟩
    intro ρ hρτ hρ
    refine ⟨(K.isRelLowerSet_faces hτ).2 hρτ hρ, ?_, ?_⟩
    · intro he
      subst ρ
      exact hnu (hfree τ hτ (Finset.ssubset_iff_subset_ne.mpr ⟨hρτ, Ne.symm hnσ⟩))
    · intro he
      have hs : σ ⊆ τ := (Finset.subset_insert a σ).trans (he ▸ hρτ)
      have hast : a ∈ τ := hρτ (he.symm ▸ Finset.mem_insert_self a σ)
      have hst : σ ⊂ τ := Finset.ssubset_iff_subset_ne.mpr
        ⟨hs, fun eq => ha (eq.symm ▸ hast)⟩
      exact hnu (hfree τ hτ hst)

private theorem insert_injective_off (a : V) {σ τ : Finset V}
    (hσ : a ∉ σ) (hτ : a ∉ τ) (h : insert a σ = insert a τ) : σ = τ := by
  simpa only [Finset.erase_insert hσ, Finset.erase_insert hτ] using
    congrArg (fun s : Finset V => s.erase a) h

/-- The recursion carries an already downward-closed current complex. -/
private theorem exhaust_pairs (a : V) (L : PreAbstractSimplicialComplex V)
    (R : Finset (Finset V)) :
    ∀ K : PreAbstractSimplicialComplex V,
    (∀ σ ∈ R, σ.Nonempty ∧ a ∉ σ) →
    (∀ σ ∈ R, ∀ τ ∈ L, ¬ σ ⊆ τ) →
    (∀ τ, τ ∈ K ↔ τ ∈ L ∨ τ ∈ R ∨ ∃ σ ∈ R, insert a σ = τ) →
    Collapses K L := by
  classical
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    intro K hR hL hK
    by_cases hr : R.Nonempty
    · obtain ⟨σ, hσ, hmax⟩ := R.exists_max_image Finset.card hr
      have hs := (hR σ hσ).1
      have ha := (hR σ hσ).2
      have hσK : σ ∈ K := (hK σ).mpr (Or.inr (Or.inl hσ))
      have huK : insert a σ ∈ K := (hK _).mpr (Or.inr (Or.inr ⟨σ, hσ, rfl⟩))
      have hfree : ∀ τ ∈ K, σ ⊂ τ → τ = insert a σ := by
        intro τ hτ hst
        rcases (hK τ).mp hτ with hτL | hτR | ⟨ρ, hρ, he⟩
        · exact (hL σ hσ τ hτL hst.subset).elim
        · have heq : σ = τ := Finset.eq_of_subset_of_card_le hst.subset (hmax τ hτR)
          exact (hst.ne heq).elim
        · have hsub : σ ⊆ ρ := by
            intro x hx
            have hxi : x ∈ insert a ρ := he.symm ▸ hst.subset hx
            rcases Finset.mem_insert.mp hxi with rfl | hxρ
            · exact (ha hx).elim
            · exact hxρ
          have heq : σ = ρ := Finset.eq_of_subset_of_card_le hsub (hmax ρ hρ)
          exact he.symm.trans (congrArg (insert a) heq.symm)
      let K' := deletePair K σ a ha hfree
      have hstep : ElementaryCollapse K K' :=
        ⟨σ, a, hs, hσK, ha, huK, hfree, fun _ => Iff.rfl⟩
      have hinv : ∀ τ, τ ∈ K' ↔
          τ ∈ L ∨ τ ∈ R.erase σ ∨ ∃ ρ ∈ R.erase σ, insert a ρ = τ := by
        intro τ
        change (τ ∈ K ∧ τ ≠ σ ∧ τ ≠ insert a σ) ↔ _
        constructor
        · rintro ⟨hτ, hnσ, hnu⟩
          rcases (hK τ).mp hτ with hτL | hτR | ⟨ρ, hρ, he⟩
          · exact Or.inl hτL
          · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨hnσ, hτR⟩))
          · exact Or.inr (Or.inr ⟨ρ, Finset.mem_erase.mpr
              ⟨fun eq => hnu (eq ▸ he.symm), hρ⟩, he⟩)
        · intro hτ
          have hτK : τ ∈ K := (hK τ).mpr (by
            rcases hτ with h | h | ⟨ρ, hρ, he⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl (Finset.mem_of_mem_erase h))
            · exact Or.inr (Or.inr ⟨ρ, Finset.mem_of_mem_erase hρ, he⟩))
          refine ⟨hτK, ?_, ?_⟩
          · intro eq
            subst τ
            rcases hτ with h | h | ⟨ρ, _, he⟩
            · exact hL σ hσ σ h (Finset.Subset.refl _)
            · exact (Finset.mem_erase.mp h).1 rfl
            · exact ha (he ▸ Finset.mem_insert_self a ρ)
          · intro eq
            subst τ
            rcases hτ with h | h | ⟨ρ, hρ, he⟩
            · exact hL σ hσ _ h (Finset.subset_insert _ _)
            · exact (hR _ (Finset.mem_of_mem_erase h)).2 (Finset.mem_insert_self _ _)
            · exact (Finset.mem_erase.mp hρ).1
                (insert_injective_off a (hR ρ (Finset.mem_of_mem_erase hρ)).2 ha he)
      have hrest : Collapses K' L := ih (R.erase σ) (Finset.erase_ssubset hσ) K'
        (fun ρ hρ => hR ρ (Finset.mem_of_mem_erase hρ))
        (fun ρ hρ => hL ρ (Finset.mem_of_mem_erase hρ)) hinv
      exact (Relation.ReflTransGen.single hstep).trans hrest
    · have he : K = L := by
        ext τ
        change (τ ∈ K) ↔ (τ ∈ L)
        simpa [Finset.not_nonempty_iff_eq_empty.mp hr] using hK τ
      subst K
      exact Relation.ReflTransGen.refl

end FiniteSimplicialCollapse

namespace FiniteGraphDominationCollapse
open D5.S3.Geometry.FiniteGraphVertexSubstitution FiniteSimplicialCollapse
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem insert_independent (G : SimpleGraph V) (a : V) (D : Finset V)
    (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d)
    {σ : Finset V} (hi : G.IsIndepSet (σ : Set V))
    (hm : ∃ d ∈ D, d ∈ σ) : G.IsIndepSet ((insert a σ : Finset V) : Set V) := by
  obtain ⟨d, hd, hdσ⟩ := hm
  have hax : ∀ x ∈ σ, ¬ G.Adj a x := by
    intro x hx hax
    have hdx : G.Adj d x := hdom d hd hax
    exact hi hdσ hx hdx.ne hdx
  intro x hx y hy hxy hxyadj
  rcases Finset.mem_insert.mp hx with rfl | hxσ
  · rcases Finset.mem_insert.mp hy with rfl | hyσ
    · exact hxy rfl
    · exact hax y hyσ hxyadj
  · rcases Finset.mem_insert.mp hy with rfl | hyσ
    · exact hax x hxσ hxyadj.symm
    · exact hi hxσ hyσ hxy hxyadj

/-- Simultaneous open-neighborhood domination yields actual finite free-pair
collapses, on the original carrier, onto the retained independent faces. -/
theorem domination_collapses (G : SimpleGraph V) (a : V) (D : Finset V)
    (ha : a ∉ D) (hdom : ∀ d ∈ D, G.neighborSet a ⊆ G.neighborSet d) :
    Collapses (independenceComplex G).toPreAbstractSimplicialComplex
      (restricted G (fun x => x ∉ D)) := by
  classical
  let R : Finset (Finset V) := Finset.univ.filter fun σ =>
    σ ∈ (independenceComplex G).toPreAbstractSimplicialComplex ∧
      a ∉ σ ∧ ∃ d ∈ D, d ∈ σ
  have hR : ∀ σ, σ ∈ R ↔
      (σ.Nonempty ∧ G.IsIndepSet (σ : Set V)) ∧ a ∉ σ ∧ ∃ d ∈ D, d ∈ σ := by
    intro σ
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  apply FiniteSimplicialCollapse.exhaust_pairs a _ R _
  · intro σ hσ
    exact ⟨((hR σ).mp hσ).1.1, ((hR σ).mp hσ).2.1⟩
  · intro σ hσ τ hτ hsub
    obtain ⟨d, hd, hdσ⟩ := ((hR σ).mp hσ).2.2
    exact hτ.2.2 d (hsub hdσ) hd
  · intro τ
    change (τ.Nonempty ∧ G.IsIndepSet (τ : Set V)) ↔ _
    constructor
    · intro hτ
      by_cases hm : ∃ d ∈ D, d ∈ τ
      · by_cases hat : a ∈ τ
        · right; right
          refine ⟨τ.erase a, (hR _).mpr ?_, Finset.insert_erase hat⟩
          have hm' : ∃ d ∈ D, d ∈ τ.erase a := by
            obtain ⟨d, hd, hdt⟩ := hm
            exact ⟨d, hd, Finset.mem_erase.mpr ⟨fun eq => ha (eq ▸ hd), hdt⟩⟩
          refine ⟨⟨?_, hτ.2.mono (fun _ hx => Finset.mem_of_mem_erase hx)⟩,
            Finset.notMem_erase _ _, hm'⟩
          obtain ⟨d, _, hd⟩ := hm'
          exact ⟨d, hd⟩
        · exact Or.inr (Or.inl ((hR _).mpr ⟨hτ, hat, hm⟩))
      · left
        exact ⟨hτ.1, hτ.2, fun x hx hd => hm ⟨x, hd, hx⟩⟩
    · rintro (hτ | hτ | ⟨σ, hσ, rfl⟩)
      · exact ⟨hτ.1, hτ.2.1⟩
      · exact ((hR _).mp hτ).1
      · have hs := (hR σ).mp hσ
        exact ⟨Finset.insert_nonempty _ _, insert_independent G a D hdom hs.1.2 hs.2.2⟩

end FiniteGraphDominationCollapse
end D5.S3.GraphInvariants
