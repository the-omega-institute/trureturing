/- GID: D5/S3/Combinatorics/TotalRoman/DiameterTwoWeight
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/DiameterTwoWeight
   mirror-E: none(waiver:small-total-roman-support)
   anchors: []
   utility: none
   digest: Low total Roman weight forces an ordinary dominating pair. -/

import D5.S3.Combinatorics.TotalRoman.SupercriticalBasics

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.DiameterTwoWeight

open SupercriticalDefs SupercriticalBasics

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Weight below the order forces a two-labelled vertex. -/
theorem exists_two_of_weight_lt_card {f : V → ℕ} (hf : IsTRDF G f)
    (hw : (∑ v, f v) < Fintype.card V) : ∃ a, f a = 2 := by
  by_contra hn
  push Not at hn
  have hpos : ∀ v, 1 ≤ f v := by
    intro v
    by_contra hp
    obtain ⟨u, _, hu⟩ := hf.2.1 v (by omega)
    exact hn u hu
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpos v)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at ht
  omega

theorem dominating_pair_of_weight_le_five {f : V → ℕ}
    (hcard : 6 ≤ Fintype.card V) (hf : IsTRDF G f) (hw : (∑ v, f v) ≤ 5) :
    ∃ a b, ∀ v, v = a ∨ v = b ∨ G.Adj v a ∨ G.Adj v b := by
  classical
  have hs (s : Finset V) : (∑ x ∈ s, f x) ≤ ∑ x, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ => Nat.zero_le _)
  obtain ⟨a, ha⟩ := exists_two_of_weight_lt_card hf (by omega)
  by_cases htwo : ∃ b, b ≠ a ∧ f b = 2
  · obtain ⟨b, hba, hb⟩ := htwo
    refine ⟨a, b, ?_⟩
    intro v
    by_contra hv
    push Not at hv
    have hfv : 0 < f v := by
      by_contra hz
      obtain ⟨u, hu, hfu⟩ := hf.2.1 v (by omega)
      by_cases hua : u = a
      · subst u
        exact hv.2.2.1 hu
      · have hub : u = b := by
          by_contra hub
          have hbound := hs {a, b, u}
          simp [ha, hb, hfu, hba.symm, Ne.symm hua, Ne.symm hub] at hbound
          omega
        subst u
        exact hv.2.2.2 hu
    obtain ⟨u, hvu, hfu⟩ := hf.2.2 v hfv
    have hua : u ≠ a := by intro he; subst u; exact hv.2.2.1 hvu
    have hub : u ≠ b := by intro he; subst u; exact hv.2.2.2 hvu
    have huv : u ≠ v := (G.ne_of_adj hvu).symm
    have hbound := hs {a, b, v, u}
    simp [hba.symm, hv.1.symm, hv.2.1.symm,
      hua.symm, hub.symm, huv.symm, ha, hb] at hbound
    omega
  · have hunique (u : V) (hu : f u = 2) : u = a := by
      by_contra hne
      exact htwo ⟨u, hne, hu⟩
    have hz (v : V) (hv : f v = 0) : G.Adj v a := by
      obtain ⟨u, hu, hfu⟩ := hf.2.1 v hv
      simpa [hunique u hfu] using hu
    obtain ⟨b, hab, hfb⟩ := hf.2.2 a (by omega)
    have hba : b ≠ a := (G.ne_of_adj hab).symm
    by_cases hdom : ∀ v, v = a ∨ v = b ∨ G.Adj v a ∨ G.Adj v b
    · exact ⟨a, b, hdom⟩
    · push Not at hdom
      obtain ⟨c, hca, hcb, hcadj, hcbadj⟩ := hdom
      have hfc : 0 < f c := by
        by_contra hc
        exact hcadj (hz c (by omega))
      obtain ⟨d, hcd, hfd⟩ := hf.2.2 c hfc
      have hda : d ≠ a := by intro he; subst d; exact hcadj hcd
      have hdb : d ≠ b := by intro he; subst d; exact hcbadj hcd
      have hdc : d ≠ c := (G.ne_of_adj hcd).symm
      have hsupport (v : V) (hv : 0 < f v) :
          v = a ∨ v = b ∨ v = c ∨ v = d := by
        by_contra hn
        push Not at hn
        have hbound := hs {a, b, c, d, v}
        simp [ha, hba.symm, hca.symm, hcb.symm,
          hda.symm, hdb.symm, hdc.symm,
          hn.1.symm, hn.2.1.symm,
          hn.2.2.1.symm, hn.2.2.2.symm] at hbound
        omega
      refine ⟨a, c, ?_⟩
      intro v
      by_cases hv : f v = 0
      · exact Or.inr (Or.inr (Or.inl (hz v hv)))
      · rcases hsupport v (by omega) with he | he | he | he
        · exact Or.inl he
        · subst v
          exact Or.inr (Or.inr (Or.inl hab.symm))
        · exact Or.inr (Or.inl he)
        · subst v
          exact Or.inr (Or.inr (Or.inr hcd.symm))

/-- At weight at most three, a two-labelled vertex must be universal. -/
theorem universal_of_weight_le_three {f : V → ℕ}
    (hcard : 4 ≤ Fintype.card V) (hf : IsTRDF G f) (hw : (∑ v, f v) ≤ 3) :
    ∃ a, ∀ v, v ≠ a → G.Adj v a := by
  classical
  obtain ⟨a, ha⟩ := exists_two_of_weight_lt_card hf (by omega)
  obtain ⟨b, hab, hfb⟩ := hf.2.2 a (by omega)
  have hba : b ≠ a := (G.ne_of_adj hab).symm
  have hsupport (v : V) (hv : 0 < f v) : v = a ∨ v = b := by
    by_contra hn
    push Not at hn
    have hs : (∑ x ∈ ({a, b, v} : Finset V), f x) ≤ ∑ x, f x :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ => Nat.zero_le _)
    simp [ha, hba.symm, hn.1.symm, hn.2.symm] at hs
    omega
  refine ⟨a, ?_⟩
  intro v hva
  by_cases hvb : v = b
  · subst v
    exact hab.symm
  · have hz : f v = 0 := by
      by_contra hp
      exact (hsupport v (by omega)).elim hva hvb
    obtain ⟨u, hvu, hfu⟩ := hf.2.1 v hz
    have hua : u = a := by
      rcases hsupport u (by omega) with hu | hu
      · exact hu
      · subst u
        have hp := weight_pair (f := f) hba
        omega
    simpa [hua] using hvu

#print axioms exists_two_of_weight_lt_card
#print axioms dominating_pair_of_weight_le_five
#print axioms universal_of_weight_le_three

end D5.S3.Combinatorics.TotalRoman.DiameterTwoWeight
