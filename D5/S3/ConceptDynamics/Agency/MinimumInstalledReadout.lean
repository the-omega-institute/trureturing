/- GID: D5/S3/ConceptDynamics/Agency/MinimumInstalledReadout
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/MinimumInstalledReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The attained effective installed alphabet is the sink count plus the minimum enabled-event hitting number. -/

import D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
import Mathlib.Data.Nat.Find

/-! Effective symbol counts and the enabled-event hitting minimum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout

open D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition

universe u v
variable {E : Type u} [Fintype E] [DecidableEq E]

noncomputable def sinks (F : Finset (Finset E)) : Finset (State F) := by
  classical
  exact Finset.univ.filter (Sink F)

noncomputable def nonsinks (F : Finset (Finset E)) : Finset (State F) := by
  classical
  exact Finset.univ.filter (fun C => ¬ Sink F C)

def Hits (F : Finset (Finset E)) (H : Finset E) : Prop :=
  ∀ C : State F, ¬ Sink F C → ∃ e ∈ H, Enabled F C e

private theorem hitting_exists (F : Finset (Finset E)) :
    ∃ n : ℕ, ∃ H : Finset E, Hits F H ∧ H.card = n := by
  classical
  refine ⟨Fintype.card E, Finset.univ, ?_, Finset.card_univ⟩
  intro C hn
  obtain ⟨e, he⟩ : ∃ e, Enabled F C e := by simpa [Sink] using hn
  exact ⟨e, Finset.mem_univ _, he⟩

noncomputable def hittingNumber (F : Finset (Finset E)) : ℕ := by
  classical
  exact Nat.find (hitting_exists F)

private theorem minimum_hitting (F : Finset (Finset E)) :
    (∃ H : Finset E, Hits F H ∧ H.card = hittingNumber F) ∧
    ∀ K : Finset E, Hits F K → hittingNumber F ≤ K.card := by
  classical
  exact ⟨Nat.find_spec (hitting_exists F),
    fun K hK => Nat.find_min' (hitting_exists F) ⟨K, hK, rfl⟩⟩

noncomputable def effectiveSize {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) : ℕ := (symbols r).card

private theorem mem_sinks (F : Finset (Finset E)) (C : State F) :
    C ∈ sinks F ↔ Sink F C := by
  classical
  simp [sinks]

private theorem mem_nonsinks (F : Finset (Finset E)) (C : State F) :
    C ∈ nonsinks F ↔ ¬ Sink F C := by
  classical
  simp [nonsinks]

private theorem effective_lower_bound {F : Finset (Finset E)} (hF : F.Nonempty)
    {Q : Type v} (r : State F → Q) (hc : CommonEnabled r) :
    (sinks F).card + hittingNumber F ≤ effectiveSize r := by
  classical
  obtain ⟨isolated, common⟩ := (acquisition_criterion hF r).2.1.mp hc
  let ts := (sinks F).image r
  let ns := (nonsinks F).image r
  have ht : ts.card = (sinks F).card := by
    apply Finset.card_image_of_injOn
    intro C hC D hD hCD
    exact (isolated C ((mem_sinks F C).mp hC) D hCD.symm).symm
  have disjoint : Disjoint ts ns := by
    apply Finset.disjoint_left.mpr
    intro q hqt hqn
    obtain ⟨C, hC, hCq⟩ := Finset.mem_image.mp hqt
    obtain ⟨D, hD, hDq⟩ := Finset.mem_image.mp hqn
    have hDC := isolated C ((mem_sinks F C).mp hC) D (hDq.trans hCq.symm)
    exact ((mem_nonsinks F D).mp hD) (hDC ▸ (mem_sinks F C).mp hC)
  have union : ts ∪ ns = symbols r := by
    ext q
    simp only [ts, ns, symbols, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩) <;> exact ⟨C, rfl⟩
    · rintro ⟨C, rfl⟩
      by_cases hs : Sink F C
      · exact Or.inl ⟨C, (mem_sinks F C).mpr hs, rfl⟩
      · exact Or.inr ⟨C, (mem_nonsinks F C).mpr hs, rfl⟩
  have hcount : effectiveSize r = (sinks F).card + ns.card := by
    rw [effectiveSize, ← union, Finset.card_union_of_disjoint disjoint, ht]
  have hex (q : {q // q ∈ ns}) :
      ∃ e : E, ∀ C, r C = q.val → Enabled F C e := by
    obtain ⟨C, hC, hCq⟩ := Finset.mem_image.mp q.property
    obtain ⟨e, he⟩ := common C ((mem_nonsinks F C).mp hC)
    exact ⟨e, fun D hD => he D (hD.trans hCq.symm)⟩
  choose pick hpick using hex
  let H : Finset E := ns.attach.image pick
  have hH : Hits F H := by
    intro C hn
    have hq : r C ∈ ns := Finset.mem_image.mpr
      ⟨C, (mem_nonsinks F C).mpr hn, rfl⟩
    refine ⟨pick ⟨r C, hq⟩, ?_, hpick ⟨r C, hq⟩ C rfl⟩
    exact Finset.mem_image.mpr ⟨⟨r C, hq⟩, Finset.mem_attach .., rfl⟩
  have hmin := (minimum_hitting F).2 H hH
  have hcard : H.card ≤ ns.card := by
    simpa [H] using (Finset.card_image_le (s := ns.attach) (f := pick))
  omega

private theorem attaining_readout {F : Finset (Finset E)} (hF : F.Nonempty)
    (H : Finset E) (hH : Hits F H) :
    ∃ r : State F → State F ⊕ E,
      FiniteAcquirable r ∧ effectiveSize r ≤ (sinks F).card + H.card := by
  classical
  let chooseEvent (C : State F) (hn : ¬ Sink F C) : E :=
    Classical.choose (hH C hn)
  have choose_mem (C : State F) (hn : ¬ Sink F C) : chooseEvent C hn ∈ H :=
    (Classical.choose_spec (hH C hn)).1
  have choose_enabled (C : State F) (hn : ¬ Sink F C) :
      Enabled F C (chooseEvent C hn) := (Classical.choose_spec (hH C hn)).2
  let r (C : State F) : State F ⊕ E :=
    if hs : Sink F C then Sum.inl C else Sum.inr (chooseEvent C hs)
  have hi : IsolatedSinks r := by
    constructor
    · intro C hs D hD
      by_cases hd : Sink F D
      · simpa [r, hs, hd] using hD
      · simp [r, hs, hd] at hD
    · intro C hn
      refine ⟨chooseEvent C hn, ?_⟩
      intro D hD
      by_cases hd : Sink F D
      · simp [r, hn, hd] at hD
      · have he : chooseEvent D hd = chooseEvent C hn := by
          simpa [r, hn, hd] using hD
        simpa only [he] using choose_enabled D hd
  have hc : CommonEnabled r := (acquisition_criterion hF r).2.1.mpr hi
  have hf := (acquisition_criterion hF r).2.2.mp hc
  let labels : Finset (State F ⊕ E) :=
    ((sinks F).image Sum.inl) ∪ (H.image Sum.inr)
  have hsub : symbols r ⊆ labels := by
    intro q hq
    obtain ⟨C, rfl⟩ : ∃ C, r C = q := by
      simpa only [symbols, Finset.mem_image, Finset.mem_univ, true_and] using hq
    by_cases hs : Sink F C
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨C, (mem_sinks F C).mpr hs, by simp [r, hs]⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨chooseEvent C hs, choose_mem C hs, by simp [r, hs]⟩
  have hcard : labels.card ≤ (sinks F).card + H.card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (Finset.card_image_le) (Finset.card_image_le))
  exact ⟨r, hf, (Finset.card_le_card hsub).trans hcard⟩

/-- For every arbitrary nonempty finite configuration family, the true minimum
hitting number exists, every history-based feasible installed port uses at
least the sink count plus that number of effective symbols, and a finite-table
safe terminating protocol attains equality. -/
theorem installed_readout_optimum (F : Finset (Finset E)) (hF : F.Nonempty) :
    ((∃ H : Finset E, Hits F H ∧ H.card = hittingNumber F) ∧
      ∀ K : Finset E, Hits F K → hittingNumber F ≤ K.card) ∧
    (∀ (Q : Type v) (r : State F → Q),
      (∃ p : History E Q → Decision F, Acquires r p) →
      (sinks F).card + hittingNumber F ≤ effectiveSize r) ∧
    (∃ r : State F → State F ⊕ E, FiniteAcquirable r ∧
      effectiveSize r = (sinks F).card + hittingNumber F) := by
  refine ⟨minimum_hitting F, ?_, ?_⟩
  · intro Q r hp
    exact effective_lower_bound hF r ((acquisition_criterion hF r).1.mp hp)
  · obtain ⟨H, hH, hcard⟩ := (minimum_hitting F).1
    obtain ⟨r, hf, hbound⟩ := attaining_readout hF H hH
    have hlower := effective_lower_bound hF r
      ((acquisition_criterion hF r).2.2.mpr hf)
    exact ⟨r, hf, Nat.le_antisymm (by simpa [hcard] using hbound) hlower⟩

#print axioms installed_readout_optimum

end D5.S3.ConceptDynamics.Agency.MinimumInstalledReadout
