/- GID: D5/S3/Combinatorics/OuterIndependentRoman/CactusLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OuterIndependentRoman/CactusLabels
   mirror-E: none(waiver:paired-domination-construction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Complementary tree colour classes give a paired domination weight bound. -/

import D5.S3.Combinatorics.OuterIndependentRoman.CactusDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OuterIndependentRoman.CactusLabels

open CactusDefs

attribute [local instance] Classical.propDecidable

/-- Two complementary labels, repaired along extra edges, bound the minimum weight. -/
theorem paired_labelling_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G T : SimpleGraph V) (hTG : T ≤ G) (c : V → Bool)
    (hc : ∀ {u v}, T.Adj u v → c u ≠ c v)
    (hn : ∀ v, ∃ u, T.Adj v u) :
    2 * gammaOIDR G ≤ 2 * Fintype.card V +
      ({v | ∃ u, T.Adj v u ∧ T.degree u = 1} : Set V).toFinset.card +
      (G.edgeFinset \ T.edgeFinset).card := by
  classical
  let S := ({v | ∃ u, T.Adj v u ∧ T.degree u = 1} : Set V).toFinset
  let E := G.edgeFinset \ T.edgeFinset
  let R := E.image (fun e => e.out.1)
  have hcover {u v : V} (h : G.Adj u v) (heq : c u = c v) : u ∈ R ∨ v ∈ R := by
    have hnt : ¬ T.Adj u v := fun ht => hc ht heq
    have he : s(u, v) ∈ E := by simp [E, h, hnt]
    have hr : s(u, v).out.1 ∈ R := Finset.mem_image_of_mem _ he
    have hout : s(s(u, v).out.1, s(u, v).out.2) = s(u, v) := Quot.out_eq _
    rcases Sym2.eq_iff.mp hout with hh | hh
    · exact Or.inl (hh.1 ▸ hr)
    · exact Or.inr (hh.1 ▸ hr)
  let f (b : Bool) (v : V) : ℕ :=
    if c v = b then if v ∈ R then 1 else 0 else if v ∈ S then 3 else 2
  have hother {b : Bool} {v u : V} (hv : c v = b) (hvu : T.Adj v u) :
      c u ≠ b := by
    intro hu
    exact hc hvu (hv.trans hu.symm)
  have hvalid (b : Bool) : IsOIDRDF G (f b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      dsimp [f]
      split_ifs <;> omega
    · intro v hv
      have hvb : c v = b := by
        by_contra hh
        simp only [f, if_neg hh] at hv
        split_ifs at hv <;> omega
      have hval {u : V} (hvu : T.Adj v u) :
          f b u = if u ∈ S then 3 else 2 := by simp [f, hother hvb hvu]
      by_cases hs : ∃ u, T.Adj v u ∧ u ∈ S
      · obtain ⟨u, hu, hus⟩ := hs
        exact Or.inl ⟨u, hTG hu, by simp [hval hu, hus]⟩
      · obtain ⟨u, hu⟩ := hn v
        have hus : u ∉ S := fun hh => hs ⟨u, hu, hh⟩
        have hw : ∃ w, T.Adj v w ∧ w ≠ u := by
          by_contra hh
          have huniq : ∃! w, T.Adj v w := by
            refine ⟨u, hu, ?_⟩
            intro w hw
            by_contra hne
            exact hh ⟨w, hw, hne⟩
          have hd : T.degree v = 1 :=
            SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr huniq
          exact hus (by simp [S]; exact ⟨v, hu.symm, hd⟩)
        obtain ⟨w, hw, hwu⟩ := hw
        have hws : w ∉ S := fun hh => hs ⟨w, hw, hh⟩
        exact Or.inr ⟨u, w, hwu.symm, hTG hu, hTG hw,
          by simp [hval hu, hus], by simp [hval hw, hws]⟩
    · intro v hv
      have hvb : c v = b := by
        by_contra hh
        simp only [f, if_neg hh] at hv
        split_ifs at hv <;> omega
      obtain ⟨u, hu⟩ := hn v
      refine ⟨u, hTG hu, ?_⟩
      simp only [f, if_neg (hother hvb hu)]
      split_ifs <;> omega
    · intro u v huv hu hv
      have hub : c u = b := by
        by_contra hh
        simp only [f, if_neg hh] at hu
        split_ifs at hu <;> omega
      have hvb : c v = b := by
        by_contra hh
        simp only [f, if_neg hh] at hv
        split_ifs at hv <;> omega
      have hur : u ∉ R := by simpa [f, hub] using hu
      have hvr : v ∉ R := by simpa [f, hvb] using hv
      exact (hcover huv (hub.trans hvb.symm)).elim hur hvr
  have hmin (b : Bool) : gammaOIDR G ≤ ∑ v, f b v :=
    Nat.sInf_le ⟨f b, hvalid b, rfl⟩
  have hpoint (v : V) : f false v + f true v =
      2 + (if v ∈ S then 1 else 0) + (if v ∈ R then 1 else 0) := by
    cases hcv : c v <;> simp [f, hcv] <;> split_ifs <;> omega
  have hsum : (∑ v, f false v) + (∑ v, f true v) =
      2 * Fintype.card V + S.card + R.card := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib, Finset.sum_ite_mem, mul_comm]
  have hcard : R.card ≤ E.card := Finset.card_image_le
  have ha := hmin false
  have hb := hmin true
  dsimp [S, E] at hsum hcard
  omega

#print axioms paired_labelling_bound

end D5.S3.Combinatorics.OuterIndependentRoman.CactusLabels
