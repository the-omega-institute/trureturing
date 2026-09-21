/- GID: D5/S1/Words/Patterns/Separable/ProperCut
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/ProperCut
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Graph separation supporting the classical separable-permutation proper cut. -/

import D5.S1.Words.Patterns.DerangementRatioNonconvergence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases

/-!
Supporting draft for the actual classical avoidance problem #9208.
The proper-cut characterization is classical (Fu--Lin--Zeng,
arXiv:1507.05184v2, Proposition 2.1, citing Kitaev). No resolution of the
descent-polynomial real-rootedness problem is asserted here.
-/

namespace D5.S1.Words.Patterns.Separable.ProperCut

open SimpleGraph
open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)

/-- The literal classical pattern 2413, with zero-based values. -/
def pattern2413 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide
  right_inv := by decide

/-- The literal classical pattern 3142, with zero-based values. -/
def pattern3142 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide
  right_inv := by decide

private def InducedP4 {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b d

private theorem insertion_meets_component {V : Type*} (G : SimpleGraph V)
    (S : Set V) {v : V} (hv : v ∉ S) (hc : (G.induce (insert v S)).Preconnected)
    (x : S) : ∃ y : S, (G.induce S).Reachable x y ∧ G.Adj y.val v := by
  classical
  obtain ⟨p⟩ := hc ⟨x.val, Set.mem_insert_of_mem _ x.property⟩ ⟨v, Set.mem_insert _ _⟩
  have go : ∀ {a b : ↥(insert v S)}, (G.induce (insert v S)).Walk a b →
      b.val = v → ∀ ha : a.val ∈ S,
      ∃ y : S, (G.induce S).Reachable ⟨a.val, ha⟩ y ∧ G.Adj y.val v := by
    intro a b q
    induction q with
    | nil => intro he ha; exact (hv (he ▸ ha)).elim
    | @cons a b c hab q ih =>
      intro he ha
      by_cases hb : b.val = v
      · refine ⟨⟨a.val, ha⟩, Reachable.rfl, ?_⟩
        change G.Adj a.val b.val at hab
        change G.Adj a.val v
        exact (congrArg (G.Adj a.val) hb).mp hab
      · have hbS : b.val ∈ S := (Set.mem_insert_iff.mp b.property).resolve_left hb
        obtain ⟨y, hy, hyv⟩ := ih he hbS
        exact ⟨y, (show (G.induce S).Adj ⟨a.val, ha⟩ ⟨b.val, hbS⟩ from hab).reachable.trans hy, hyv⟩
  exact go p rfl x.property

private theorem p4_free_separation {V : Type*} [Finite V] [Nontrivial V]
    (G : SimpleGraph V) (hf : ∀ a b c d, ¬InducedP4 G a b c d) :
    ¬G.Preconnected ∨ ¬Gᶜ.Preconnected := by
  classical
  let _ := Fintype.ofFinite V
  by_cases hc : G.Preconnected
  · right
    by_cases hcomplete : ∀ a b, a ≠ b → G.Adj a b
    · have he : Gᶜ = ⊥ := by
        ext a b
        simp only [compl_adj, bot_adj, iff_false, not_and]
        exact fun hn h => h (hcomplete a b hn)
      rw [he]
      exact not_preconnected_bot
    push Not at hcomplete
    obtain ⟨a, b, hab, hna⟩ := hcomplete
    let candidates : Finset (Finset V) :=
      Finset.univ.filter (fun S => ¬(G.induce (S : Set V)).Preconnected)
    have hpair : ¬(G.induce ({a, b} : Set V)).Preconnected := by
      intro hh
      obtain ⟨z, hz⟩ := (hh ⟨a, by simp⟩ ⟨b, by simp⟩).nonempty_neighborSet_left
        (fun he => hab (congrArg Subtype.val he))
      change G.Adj a z.val at hz
      rcases z.property with hz' | hz'
      · exact (G.ne_of_adj hz) hz'.symm
      · exact hna (hz' ▸ hz)
    have hn : candidates.Nonempty := by
      refine ⟨{a, b}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [Finset.coe_pair]
      exact hpair
    obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card hn
    have hdisc : ¬(G.induce (S : Set V)).Preconnected := (Finset.mem_filter.mp hS).2
    have hproper : ∃ v, v ∉ S := by
      by_contra! hall
      apply hdisc
      intro x y
      let f : G →g G.induce (S : Set V) :=
        { toFun := fun z => ⟨z, hall z⟩, map_rel' := fun h => h }
      exact (hc x.val y.val).map f
    have hins : ∀ v, v ∉ S → (G.induce (insert v (S : Set V))).Preconnected := by
      intro v hv
      by_contra hn
      have hm := hmax (insert v S) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          rw [Finset.coe_insert]
          exact hn⟩)
      rw [Finset.card_insert_of_notMem hv] at hm
      omega
    have hall : ∀ v, v ∉ S → ∀ x ∈ S, G.Adj x v := by
      intro v hv x hx
      by_contra hnx
      let xs : (S : Set V) := ⟨x, hx⟩
      obtain ⟨y, ⟨p⟩, hyv⟩ := insertion_meets_component G (S : Set V) hv (hins v hv) xs
      obtain ⟨d, hd, hd0, hd1⟩ := p.exists_boundary_dart
        {z | ¬G.Adj z.val v} hnx (by simpa using hyv)
      have hxb := (p.takeUntil d.snd (p.dart_snd_mem_support_of_mem_darts hd)).reachable
      have hxa := (p.takeUntil d.fst (p.dart_fst_mem_support_of_mem_darts hd)).reachable
      have hz : ∃ z : (S : Set V), ¬(G.induce (S : Set V)).Reachable xs z := by
        by_contra! hh
        exact hdisc (fun u w => (hh u).symm.trans (hh w))
      obtain ⟨z, hz⟩ := hz
      obtain ⟨w, hzw, hwv⟩ := insertion_meets_component G (S : Set V) hv (hins v hv) z
      have hna : ¬G.Adj d.fst.val w.val := by
        intro h
        have hr := (show (G.induce (S : Set V)).Adj d.fst w from h).reachable
        exact hz ((hxa.trans hr).trans hzw.symm)
      have hnb : ¬G.Adj d.snd.val w.val := by
        intro h
        have hr := (show (G.induce (S : Set V)).Adj d.snd w from h).reachable
        exact hz ((hxb.trans hr).trans hzw.symm)
      have hab' : G.Adj d.fst.val d.snd.val := d.adj
      have hbv : G.Adj d.snd.val v := not_not.mp hd1
      apply hf d.fst.val d.snd.val v w.val
      refine ⟨hab'.ne, ?_, ?_, hbv.ne, ?_, hwv.ne.symm,
        hab', hbv, hwv.symm, hd0, hna, hnb⟩
      · exact fun he => hv (he ▸ d.fst.property)
      · intro he
        exact hd0 (he ▸ hwv)
      · intro he
        exact hna (he ▸ hab')
    obtain ⟨v, hv⟩ := hproper
    have hSne : S.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      exact hdisc (by intro x; have := x.property; simp at this)
    obtain ⟨x, hx⟩ := hSne
    intro hcc
    obtain ⟨p⟩ := hcc x v
    obtain ⟨d, _, hd0, hd1⟩ := p.exists_boundary_dart (S : Set V) hx hv
    exact (compl_adj G _ _).mp d.adj |>.2 (hall d.snd hd1 d.fst hd0)
  · exact Or.inl hc

private def Spans {V : Type*} [LinearOrder V] (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y z : V⦄, x < y → y < z → G.Adj x z → G.Adj x y ∨ G.Adj y z

private theorem reachable_between {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (hs : Spans G) {x y z : V} (hxy : x < y) (hyz : y < z)
    (hxz : G.Reachable x z) : G.Reachable x y := by
  classical
  obtain ⟨p⟩ := hxz
  obtain ⟨d, hd, hp, hq⟩ := p.exists_boundary_dart {a | a < y} hxy (not_lt.mpr hyz.le)
  have hxp := (p.takeUntil d.fst (p.dart_fst_mem_support_of_mem_darts hd)).reachable
  have hyq : y ≤ d.snd := le_of_not_gt hq
  rcases hyq.eq_or_lt with heq | hlt
  · exact heq ▸ hxp.trans d.adj.reachable
  · rcases hs hp hlt d.adj with h | h
    · exact hxp.trans h.reachable
    · exact (hxp.trans d.adj.reachable).trans h.symm.reachable

private theorem disconnected_spans_cut {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (hs : Spans G) (hd : ¬G.Preconnected) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧
      ∀ i j : Fin n, i.val < m → m ≤ j.val → ¬G.Adj i j := by
  classical
  let root : Fin n := ⟨0, by omega⟩
  have hex : ∃ v, ¬G.Reachable root v := by
    by_contra! h
    exact hd (fun a b => (h a).symm.trans (h b))
  let omitted := Finset.univ.filter (fun v => ¬G.Reachable root v)
  have hom : omitted.Nonempty := by
    obtain ⟨v, hv⟩ := hex
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  obtain ⟨m, hm, hmin⟩ := omitted.exists_min_image Fin.val hom
  have hmr : ¬G.Reachable root m := (Finset.mem_filter.mp hm).2
  have hmpos : 1 ≤ m.val := by
    by_contra h
    have heq : m = root := Fin.ext (by dsimp [root]; omega)
    exact hmr (heq ▸ Reachable.rfl)
  have hsmall : ∀ i : Fin n, i.val < m.val → G.Reachable root i := by
    intro i hi
    by_contra h
    have := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  refine ⟨m.val, hmpos, m.isLt, ?_⟩
  intro i j hi hj hij
  have hrj := (hsmall i hi).trans hij.reachable
  rcases eq_or_lt_of_le hj with heq | hlt
  · exact hmr ((Fin.ext heq) ▸ hrj)
  · exact hmr (reachable_between hs (show root < m from hmpos) hlt hrj)

private def inversionGraph {n : ℕ} (π : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := (i < j ∧ π j < π i) ∨ (j < i ∧ π i < π j)
  symm := by tauto
  loopless := ⟨by intro i; simp⟩

private theorem induced_path_contains {n : ℕ} (π : Equiv.Perm (Fin n))
    {a b c d : Fin n} (hp : InducedP4 (inversionGraph π) a b c d) :
    Contains pattern2413 π ∨ Contains pattern3142 π := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd, eab, ebc, ecd, nac, nad, nbd⟩ := hp
  have vab := π.injective.ne hab
  have vac := π.injective.ne hac
  have vad := π.injective.ne had
  have vbc := π.injective.ne hbc
  have vbd := π.injective.ne hbd
  have vcd := π.injective.ne hcd
  simp only [inversionGraph] at eab ebc ecd nac nad nbd
  have hcases :
      (a < c ∧ c < b ∧ b < d ∧ π b < π a ∧ π a < π d ∧ π d < π c) ∨
      (d < b ∧ b < c ∧ c < a ∧ π c < π d ∧ π d < π a ∧ π a < π b) ∨
      (b < a ∧ a < d ∧ d < c ∧ π a < π c ∧ π c < π b ∧ π b < π d) ∨
      (c < d ∧ d < a ∧ a < b ∧ π d < π b ∧ π b < π c ∧ π c < π a) := by
    rcases eab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases ebc with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases ecd with ⟨h5, h6⟩ | ⟨h5, h6⟩
    all_goals by_cases h7 : a < c
    all_goals first
      | (left; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
      | (right; left; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
      | (right; right; left; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
      | (right; right; right; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
  have realize : ∀ x y z w : Fin n, x < y → y < z → z < w →
      (π z < π x ∧ π x < π w ∧ π w < π y) ∨
      (π y < π w ∧ π w < π x ∧ π x < π z) →
      Contains pattern2413 π ∨ Contains pattern3142 π := by
    intro x y z w hxy hyz hzw hv
    let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![x, y, z, w] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega)
    rcases hv with ⟨hzx, hxw, hwy⟩ | ⟨hyw, hwx, hxz⟩
    · left
      refine ⟨f, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [pattern2413, f, OrderEmbedding.ofStrictMono] <;> omega
    · right
      refine ⟨f, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [pattern3142, f, OrderEmbedding.ofStrictMono] <;> omega
  rcases hcases with ⟨h1, h2, h3, hv⟩ | ⟨h1, h2, h3, hv⟩ |
    ⟨h1, h2, h3, hv⟩ | ⟨h1, h2, h3, hv⟩
  · exact realize a c b d h1 h2 h3 (Or.inl hv)
  · exact realize d b c a h1 h2 h3 (Or.inl hv)
  · exact realize b a d c h1 h2 h3 (Or.inr hv)
  · exact realize c d a b h1 h2 h3 (Or.inr hv)

/-- Actual classical 2413/3142 avoidance gives a nonempty proper direct or skew cut. -/
theorem avoidance_proper_cut {n : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    (h2413 : ¬Contains pattern2413 π) (h3142 : ¬Contains pattern3142 π) :
    ∃ m : ℕ, 1 ≤ m ∧ m < n ∧
      ((∀ i j : Fin n, i.val < m → m ≤ j.val → π i < π j) ∨
       (∀ i j : Fin n, i.val < m → m ≤ j.val → π j < π i)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hf : ∀ a b c d, ¬InducedP4 (inversionGraph π) a b c d := by
    intro a b c d hp
    exact (induced_path_contains π hp).elim h2413 h3142
  rcases p4_free_separation (inversionGraph π) hf with hg | hg
  · have hs : Spans (inversionGraph π) := by
      intro x y z hxy hyz hxz
      change (x < z ∧ π z < π x) ∨ (z < x ∧ π x < π z) at hxz
      change ((x < y ∧ π y < π x) ∨ (y < x ∧ π x < π y)) ∨
        ((y < z ∧ π z < π y) ∨ (z < y ∧ π y < π z))
      rcases hxz with hxz | hxz
      · by_cases h : π y < π x
        · exact Or.inl (Or.inl ⟨hxy, h⟩)
        · exact Or.inr (Or.inl ⟨hyz, lt_of_lt_of_le hxz.2 (le_of_not_gt h)⟩)
      · exact (not_lt_of_ge (le_of_lt (hxy.trans hyz)) hxz.1).elim
    obtain ⟨m, hm, hmn, hcut⟩ := disconnected_spans_cut hn (inversionGraph π) hs hg
    refine ⟨m, hm, hmn, Or.inl ?_⟩
    intro i j hi hj
    have hij : i < j := by omega
    exact lt_of_le_of_ne
      (le_of_not_gt (fun h => hcut i j hi hj (Or.inl ⟨hij, h⟩)))
      (π.injective.ne (ne_of_lt hij))
  · have hs : Spans (inversionGraph π)ᶜ := by
      intro x y z hxy hyz hxz
      simp only [compl_adj, inversionGraph] at hxz ⊢
      have hzy : ¬z < y := by omega
      have hyx : ¬y < x := by omega
      have hvxz : π x < π z := lt_of_le_of_ne
        (le_of_not_gt (fun h => hxz.2 (Or.inl ⟨hxy.trans hyz, h⟩)))
        (π.injective.ne (ne_of_lt (hxy.trans hyz)))
      by_cases h : π y < π x
      · right
        refine ⟨ne_of_lt hyz, ?_⟩
        rintro (⟨_, hh⟩ | ⟨hh, _⟩)
        · exact not_lt_of_ge (h.trans hvxz).le hh
        · exact hzy hh
      · left
        refine ⟨ne_of_lt hxy, ?_⟩
        rintro (⟨_, hh⟩ | ⟨hh, _⟩)
        · exact h hh
        · exact hyx hh
    obtain ⟨m, hm, hmn, hcut⟩ := disconnected_spans_cut hn (inversionGraph π)ᶜ hs hg
    refine ⟨m, hm, hmn, Or.inr ?_⟩
    intro i j hi hj
    have hij : i < j := by omega
    by_contra h
    apply hcut i j hi hj
    rw [compl_adj]
    refine ⟨ne_of_lt hij, ?_⟩
    rintro (⟨_, hh⟩ | ⟨hh, _⟩)
    · exact h hh
    · exact (not_lt_of_ge hij.le) hh

end D5.S1.Words.Patterns.Separable.ProperCut
