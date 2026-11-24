/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Capped tetrahedral cycles have minimum nine, classify equality, and omit order ten. -/



import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases

/-!
# A lower bound for tetrahedral cycles

This is the abstract cycle bound for the Boolean shell in Hong–Wu–Xia
Problem 2. A nonempty mod-two tetrahedral cycle with at most three
tetrahedra in each five-set has at least nine tetrahedra.

The four-triangle link case is obtained by counting vertex incidences.
Every used vertex of such a link has at least three incident triangles,
so four triangles must exhaust the three-subsets of four vertices.
-/

set_option autoImplicit false

namespace Q9ShellTetrahedronCycle

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

private def support (C : Finset (Finset V)) : Finset V :=
  C.biUnion id

private theorem mem_support {C : Finset (Finset V)} {v : V} :
    v ∈ support C ↔ ∃ t ∈ C, v ∈ t := by
  simp only [support, Finset.mem_biUnion, id_eq]

private theorem subset_support {C : Finset (Finset V)} {t : Finset V} (ht : t ∈ C) :
    t ⊆ support C :=
  fun _ hx => mem_support.mpr ⟨t, ht, hx⟩

private theorem rank_lt_card_support {C : Finset (Finset V)} {k : ℕ}
    (hRank : ∀ t ∈ C, t.card = k) (hMany : 1 < C.card) :
    k < (support C).card := by
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hMany
  by_contra! hSmall
  have hs' := Finset.eq_of_subset_of_card_le (subset_support hs)
    (by rw [hRank s hs]; exact hSmall)
  have ht' := Finset.eq_of_subset_of_card_le (subset_support ht)
    (by rw [hRank t ht]; exact hSmall)
  exact hst (hs'.trans ht'.symm)

private def link (C : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (C.filter fun t => v ∈ t).image (fun t => t.erase v)

private theorem mem_link {C : Finset (Finset V)} {v : V} {t : Finset V} :
    t ∈ link C v ↔ v ∉ t ∧ insert v t ∈ C := by
  unfold link
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hsC, hvs⟩ := Finset.mem_filter.mp hs
    exact ⟨Finset.notMem_erase _ _, by simpa only [Finset.insert_erase hvs] using hsC⟩
  · rintro ⟨hvt, htC⟩
    exact Finset.mem_image.mpr
      ⟨insert v t, Finset.mem_filter.mpr ⟨htC, Finset.mem_insert_self _ _⟩,
        Finset.erase_insert hvt⟩

private theorem card_link (C : Finset (Finset V)) (v : V) :
    (link C v).card = (C.filter fun t => v ∈ t).card := by
  unfold link
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  have hvs := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
  have hvt := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
  calc
    s = insert v (s.erase v) := (Finset.insert_erase hvs).symm
    _ = insert v (t.erase v) := congrArg (insert v) hst
    _ = t := Finset.insert_erase hvt

private theorem link_nonempty {C : Finset (Finset V)} {v : V} (hv : v ∈ support C) :
    (link C v).Nonempty := by
  obtain ⟨t, ht, hvt⟩ := mem_support.mp hv
  exact ⟨t.erase v, Finset.mem_image.mpr
    ⟨t, Finset.mem_filter.mpr ⟨ht, hvt⟩, rfl⟩⟩

private theorem link_rank {C : Finset (Finset V)} {v : V} {k : ℕ}
    (hRank : ∀ t ∈ C, t.card = k + 1) (t : Finset V) (ht : t ∈ link C v) :
    t.card = k := by
  obtain ⟨hvt, hInsert⟩ := mem_link.mp ht
  have hCard := hRank _ hInsert
  rw [Finset.card_insert_of_notMem hvt] at hCard
  omega

private theorem link_even_boundary {C : Finset (Finset V)} {v : V} {k : ℕ}
    (hEven : ∀ r : Finset V, r.card = k + 1 → Even ((C.filter (r ⊆ ·)).card))
    (r : Finset V) (hr : r.card = k) :
    Even (((link C v).filter (r ⊆ ·)).card) := by
  by_cases hvr : v ∈ r
  · have hEmpty : (link C v).filter (r ⊆ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨htLink, hrt⟩ := Finset.mem_filter.mp ht
      exact (mem_link.mp htLink).1 (hrt hvr)
    simp [hEmpty]
  · have hFilter : (link C v).filter (r ⊆ ·) = link (C.filter (r ⊆ ·)) v := by
      ext t
      simp only [Finset.mem_filter, mem_link, Finset.subset_insert_iff_of_notMem hvr]
      exact ⟨fun ⟨⟨hvt, htC⟩, hrt⟩ => ⟨hvt, htC, hrt⟩,
        fun ⟨hvt, htC, hrt⟩ => ⟨⟨hvt, htC⟩, hrt⟩⟩
    have hCofaces : (C.filter (r ⊆ ·)).filter (fun t => v ∈ t) =
        C.filter (insert v r ⊆ ·) := by
      ext t
      simp only [Finset.mem_filter, Finset.insert_subset_iff]
      exact ⟨fun ⟨⟨htC, hrt⟩, hvt⟩ => ⟨htC, hvt, hrt⟩,
        fun ⟨htC, hvt, hrt⟩ => ⟨⟨htC, hrt⟩, hvt⟩⟩
    rw [hFilter, card_link, hCofaces]
    exact hEven _ (by rw [Finset.card_insert_of_notMem hvr, hr])

private theorem vertex_incidence_below {C : Finset (Finset V)} {t : Finset V} (ht : t ∈ C) :
    (support C).bipartiteBelow (fun v s => v ∈ s) t = t := by
  ext v
  simp only [Finset.mem_bipartiteBelow]
  exact ⟨And.right, fun h => ⟨subset_support ht h, h⟩⟩

/-- A nonempty simple graph with even vertex degrees has at least three edges. -/
private theorem three_le_card_of_even_degrees {C : Finset (Finset V)}
    (hNonempty : C.Nonempty) (hRank : ∀ t ∈ C, t.card = 2)
    (hEven : ∀ r : Finset V, r.card = 1 → Even ((C.filter (r ⊆ ·)).card)) :
    3 ≤ C.card := by
  by_contra! hSmall
  obtain ⟨e, he⟩ := hNonempty
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < e.card by rw [hRank e he]; decide)
  have hMate (x : V) (hx : x ∈ e) : ∃ f ∈ C.erase e, x ∈ f := by
    let D := C.filter (({x} : Finset V) ⊆ ·)
    have heD : e ∈ D := Finset.mem_filter.mpr ⟨he, Finset.singleton_subset_iff.mpr hx⟩
    have hPos := Finset.card_pos.mpr (show D.Nonempty from ⟨e, heD⟩)
    have hParity : D.card % 2 = 0 := Nat.even_iff.mp (hEven {x} (Finset.card_singleton x))
    obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_ne (s := D) (by omega) e
    obtain ⟨hfC, hxf⟩ := Finset.mem_filter.mp hf
    exact ⟨f, Finset.mem_erase.mpr ⟨hfe, hfC⟩, Finset.singleton_subset_iff.mp hxf⟩
  obtain ⟨f, hf, _⟩ := hMate a ha
  have hErase : (C.erase e).card ≤ 1 := by rw [Finset.card_erase_of_mem he]; omega
  have hSub : e ⊆ f := by
    intro x hx
    obtain ⟨g, hg, hxg⟩ := hMate x hx
    exact (Finset.card_le_one.mp hErase g hg f hf) ▸ hxg
  have hef := Finset.eq_of_subset_of_card_le hSub
    (by rw [hRank e he, hRank f (Finset.mem_erase.mp hf).2])
  exact (Finset.mem_erase.mp hf).1 hef.symm

private theorem card_support_le_card_triangle_cycle {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 3)
    (hEven : ∀ r : Finset V, r.card = 2 → Even ((C.filter (r ⊆ ·)).card)) :
    (support C).card ≤ C.card := by
  have hCount := Finset.card_mul_le_card_mul (fun v (t : Finset V) => v ∈ t)
    (s := support C) (t := C) (m := 3) (n := 3)
    (fun v hv => by
      change 3 ≤ (C.filter fun t => v ∈ t).card
      rw [← card_link C v]
      exact three_le_card_of_even_degrees (link_nonempty hv)
        (link_rank (k := 2) hRank) (link_even_boundary (k := 1) hEven))
    (fun t ht => by rw [vertex_incidence_below ht, hRank t ht])
  omega

private theorem even_card_triangle_cycle {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 3)
    (hEven : ∀ r : Finset V, r.card = 2 → Even ((C.filter (r ⊆ ·)).card)) :
    Even C.card := by
  let E := (support C).powersetCard 2
  let r : Finset V → Finset V → Prop := (· ⊆ ·)
  have hBelow (t : Finset V) (ht : t ∈ C) : E.bipartiteBelow r t = t.powersetCard 2 := by
    ext e
    simp only [E, r, Finset.mem_bipartiteBelow, Finset.mem_powersetCard]
    exact ⟨fun ⟨⟨_, hCard⟩, het⟩ => ⟨het, hCard⟩,
      fun ⟨het, hCard⟩ => ⟨⟨het.trans (subset_support ht), hCard⟩, het⟩⟩
  have hEvenSum : Even (∑ e ∈ E, (C.bipartiteAbove r e).card) := by
    apply Finset.even_sum
    intro e he
    change Even ((C.filter (e ⊆ ·)).card)
    exact hEven e (Finset.mem_powersetCard.mp he).2
  have hCount : (∑ e ∈ E, (C.bipartiteAbove r e).card) = C.card * 3 := by
    calc
      _ = ∑ t ∈ C, (E.bipartiteBelow r t).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
      _ = ∑ _t ∈ C, (3 : ℕ) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hBelow t ht, Finset.card_powersetCard, hRank t ht] <;> decide
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  rw [hCount] at hEvenSum
  have hParity := Nat.even_iff.mp hEvenSum
  exact Nat.even_iff.mpr (by omega)

private theorem four_triangle_cycle {C : Finset (Finset V)}
    (hRank : ∀ t ∈ C, t.card = 3)
    (hSupport : (support C).card ≤ C.card) (hFour : C.card = 4) :
    (support C).card = 4 ∧ C = (support C).powersetCard 3 := by
  have hLower := rank_lt_card_support hRank (by omega)
  have hSupportCard : (support C).card = 4 := by omega
  refine ⟨hSupportCard, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro t ht
    exact Finset.mem_powersetCard.mpr ⟨subset_support ht, hRank t ht⟩
  · rw [Finset.card_powersetCard, hSupportCard, hFour] <;> decide

private theorem card_link_even_and_six_le {C : Finset (Finset V)} {v : V}
    (hRank : ∀ t ∈ C, t.card = 4)
    (hEven : ∀ r : Finset V, r.card = 3 → Even ((C.filter (r ⊆ ·)).card))
    (hCap : ∀ w : Finset V, w.card = 5 → (C.filter (· ⊆ w)).card ≤ 3)
    (hv : v ∈ support C) :
    Even (link C v).card ∧ 6 ≤ (link C v).card := by
  have hLinkRank := link_rank (v := v) (k := 3) hRank
  have hLinkBoundary := link_even_boundary (v := v) (k := 2) hEven
  have hParity := even_card_triangle_cycle hLinkRank hLinkBoundary
  refine ⟨hParity, ?_⟩
  have hMod := Nat.even_iff.mp hParity
  have hPos := Finset.card_pos.mpr (link_nonempty hv)
  have hSupport := card_support_le_card_triangle_cycle hLinkRank hLinkBoundary
  have hLower := rank_lt_card_support hLinkRank (by omega)
  by_contra! hSmall
  have hFour : (link C v).card = 4 := by omega
  obtain ⟨hWCard, hBoundary⟩ := four_triangle_cycle hLinkRank hSupport hFour
  have hvW : v ∉ support (link C v) := by
    intro hvW
    obtain ⟨t, ht, hvt⟩ := mem_support.mp hvW
    exact (mem_link.mp ht).1 hvt
  have hFive : (insert v (support (link C v))).card = 5 := by
    rw [Finset.card_insert_of_notMem hvW, hWCard]
  have hInclusion : (C.filter (fun t => v ∈ t)) ⊆
      C.filter (· ⊆ insert v (support (link C v))) := by
    intro t ht
    obtain ⟨htC, hvt⟩ := Finset.mem_filter.mp ht
    have hLink : t.erase v ∈ link C v := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    rw [hBoundary] at hLink
    have hSub := (Finset.mem_powersetCard.mp hLink).1
    refine Finset.mem_filter.mpr ⟨htC, ?_⟩
    rw [← Finset.insert_erase hvt]
    exact Finset.insert_subset_iff.mpr
      ⟨Finset.mem_insert_self _ _, fun _ hx => Finset.mem_insert_of_mem (hSub hx)⟩
  have hBound := (Finset.card_le_card hInclusion).trans (hCap _ hFive)
  rw [← card_link C v] at hBound
  omega

private theorem support_and_incidence_bound (C : Finset (Finset V))
    (hNonempty : C.Nonempty) (hRank : ∀ t ∈ C, t.card = 4)
    (hEven : ∀ r : Finset V, r.card = 3 → Even ((C.filter (r ⊆ ·)).card))
    (hCap : ∀ w : Finset V, w.card = 5 → (C.filter (· ⊆ w)).card ≤ 3) :
    6 ≤ (support C).card ∧ (support C).card * 6 ≤ C.card * 4 := by
  have hDegree (v : V) (hv : v ∈ support C) : 6 ≤ (C.filter fun t => v ∈ t).card := by
    rw [← card_link C v]
    exact (card_link_even_and_six_le hRank hEven hCap hv).2
  obtain ⟨t, ht⟩ := hNonempty
  obtain ⟨v, hvt⟩ := Finset.card_pos.mp (show 0 < t.card by rw [hRank t ht]; decide)
  have hMany : 6 ≤ C.card := (hDegree v (subset_support ht hvt)).trans
    (Finset.card_le_card (Finset.filter_subset (fun s => v ∈ s) C))
  have hSupportLower := rank_lt_card_support hRank (by omega)
  have hSix : 6 ≤ (support C).card := by
    by_contra! hSmall
    have hFive : (support C).card = 5 := by omega
    have hAll : C.filter (· ⊆ support C) = C :=
      Finset.filter_true_of_mem (fun _ hs => subset_support hs)
    have hBound := hCap _ hFive
    rw [hAll] at hBound
    omega
  have hCount := Finset.card_mul_le_card_mul (fun v (s : Finset V) => v ∈ s)
    (s := support C) (t := C) (m := 6) (n := 4)
    (fun v hv => hDegree v hv)
    (fun s hs => by rw [vertex_incidence_below hs, hRank s hs])
  exact ⟨hSix, hCount⟩

/-- A nonempty mod-two cycle of distinct tetrahedra has at least nine tetrahedra
if every five-set contains at most three of them. -/
theorem nine_le_card_tetrahedron_cycle (C : Finset (Finset V))
    (hNonempty : C.Nonempty) (hRank : ∀ t ∈ C, t.card = 4)
    (hEven : ∀ r : Finset V, r.card = 3 → Even ((C.filter (r ⊆ ·)).card))
    (hCap : ∀ w : Finset V, w.card = 5 → (C.filter (· ⊆ w)).card ≤ 3) :
    9 ≤ C.card := by
  obtain ⟨hSupport, hCount⟩ := support_and_incidence_bound C hNonempty hRank hEven hCap
  omega

private theorem edge_between_iff_of_even_triple {E : Finset (Finset V)} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hRank : ∀ e ∈ E, e.card = 2)
    (hEven : Even ((E.filter (· ⊆ ({a, b, c} : Finset V))).card)) :
    ({b, c} : Finset V) ∈ E ↔
      (({a, b} : Finset V) ∈ E ∧ ({a, c} : Finset V) ∉ E) ∨
      (({a, b} : Finset V) ∉ E ∧ ({a, c} : Finset V) ∈ E) := by
  let R : Finset V := {a, b, c}
  let ab : Finset V := {a, b}
  let ac : Finset V := {a, c}
  let bc : Finset V := {b, c}
  have habac : ab ≠ ac := by
    intro h
    have hb : b ∈ ac := h ▸ (by simp [ab] : b ∈ ab)
    simpa [ac, hab.symm, hbc] using hb
  have habbc : ab ≠ bc := by
    intro h
    have ha : a ∈ bc := h ▸ (by simp [ab] : a ∈ ab)
    simpa [bc, hab, hac] using ha
  have hacbc : ac ≠ bc := by
    intro h
    have ha : a ∈ bc := h ▸ (by simp [ac] : a ∈ ac)
    simpa [bc, hab, hac] using ha
  have hRCard : R.card = 3 := by
    change (insert a ({b, c} : Finset V)).card = 3
    rw [Finset.card_insert_of_notMem (show a ∉ ({b, c} : Finset V) by simp [hab, hac]),
      Finset.card_pair hbc]
  have hPairs : ({ab, ac, bc} : Finset (Finset V)) = R.powersetCard 2 := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      have ha : a ∈ R := by simp [R]
      have hb : b ∈ R := by simp [R]
      have hc : c ∈ R := by simp [R]
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩,
            Finset.card_pair hab⟩
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hc⟩,
            Finset.card_pair hac⟩
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset_iff.mpr ⟨hb, Finset.singleton_subset_iff.mpr hc⟩,
            Finset.card_pair hbc⟩
    · rw [Finset.card_powersetCard, hRCard,
        Finset.card_insert_of_notMem (show ab ∉ ({ac, bc} : Finset (Finset V)) by
          simp [habac, habbc]), Finset.card_pair hacbc] <;> decide
  have hFilter : E.filter (· ⊆ R) = (R.powersetCard 2).filter (· ∈ E) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun ⟨he, her⟩ => ⟨⟨her, hRank e he⟩, he⟩, fun ⟨⟨her, _⟩, he⟩ => ⟨he, her⟩⟩
  change Even ((E.filter (· ⊆ R)).card) at hEven
  rw [hFilter, ← hPairs] at hEven
  change bc ∈ E ↔ (ab ∈ E ∧ ac ∉ E) ∨ (ab ∉ E ∧ ac ∈ E)
  by_cases h₁ : ab ∈ E <;> by_cases h₂ : ac ∈ E <;> by_cases h₃ : bc ∈ E <;>
    simp [Finset.filter_insert, Finset.filter_singleton, Finset.card_insert_of_notMem,
      Nat.even_iff, h₁, h₂, h₃, habac, habbc, hacbc] at hEven ⊢ <;> omega

/-- A tetrahedral cycle on six used vertices is the complement of a cut.
Its order equals the product of the two part sizes. -/
theorem six_vertex_cycle_cut (C : Finset (Finset V))
    (hRank : ∀ t ∈ C, t.card = 4)
    (hEven : ∀ r : Finset V, r.card = 3 → Even ((C.filter (r ⊆ ·)).card))
    (hWCard : (support C).card = 6) :
    ∃ A B : Finset V, A.card + B.card = 6 ∧ A.card * B.card = C.card ∧ Disjoint A B ∧
      C = (A ×ˢ B).image (fun p => (A ∪ B) \ ({p.1, p.2} : Finset V)) := by
  let W := support C
  change W.card = 6 at hWCard
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  let E := C.image (fun t => W \ t)
  have hEdge {e : Finset V} (he : e ∈ E) : e ⊆ W ∧ e.card = 2 := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    refine ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset (subset_support ht : t ⊆ W), hWCard, hRank t ht]
  have hInv {t : Finset V} (ht : t ∈ C) : W \ (W \ t) = t :=
    Finset.sdiff_sdiff_eq_self (subset_support ht)
  have hInj : Set.InjOn (fun t => W \ t) (C : Set (Finset V)) := by
    intro t ht u hu h
    simpa only [hInv (Finset.mem_coe.mp ht), hInv (Finset.mem_coe.mp hu)] using
      congrArg (fun e => W \ e) h
  have hECard : E.card = C.card := Finset.card_image_of_injOn hInj
  have hParity {r : Finset V} (hr : r ⊆ W) (hrCard : r.card = 3) :
      Even ((E.filter (· ⊆ r)).card) := by
    let D := C.filter (W \ r ⊆ ·)
    have hDual {t : Finset V} (ht : t ∈ C) : W \ t ⊆ r ↔ W \ r ⊆ t := by
      have h : W \ t ⊆ W \ (W \ r) ↔ W \ r ⊆ t :=
        Finset.sdiff_subset_sdiff_iff_subset (subset_support ht : t ⊆ W)
          (Finset.sdiff_subset : W \ r ⊆ W)
      rw [Finset.sdiff_sdiff_eq_self hr] at h
      exact h
    have hFilter : E.filter (· ⊆ r) = D.image (fun t => W \ t) := by
      ext e
      simp only [E, D, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, htr⟩
        exact ⟨t, ⟨ht, (hDual ht).mp htr⟩, rfl⟩
      · rintro ⟨t, ⟨ht, hrt⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (hDual ht).mpr hrt⟩
    have hSub : (D : Set (Finset V)) ⊆ (C : Set (Finset V)) :=
      fun _ ht => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1
    rw [hFilter, Finset.card_image_of_injOn (hInj.mono hSub)]
    exact hEven (W \ r) (by rw [Finset.card_sdiff_of_subset hr, hWCard, hrCard])
  let A := W.filter (fun x => ({b, x} : Finset V) ∈ E)
  let B := W \ A
  have hASub : A ⊆ W := Finset.filter_subset _ W
  have hbb : ({b} : Finset V) ∉ E := by
    intro he
    have h := (hEdge he).2
    rw [Finset.card_singleton] at h
    omega
  have hCut {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) :
      ({x, y} : Finset V) ∈ E ↔ (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) := by
    by_cases hbx : b = x
    · subst x
      simp [A, hb, hy, hbb]
    by_cases hby : b = y
    · subst y
      simp [A, hx, hb, hbb, Finset.pair_comm x b]
    have hR : ({b, x, y} : Finset V) ⊆ W :=
      Finset.insert_subset_iff.mpr
        ⟨hb, Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩⟩
    have hRCard : ({b, x, y} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (show b ∉ ({x, y} : Finset V) by simp [hbx, hby]),
        Finset.card_pair hxy]
    simpa [A, hx, hy] using
      (edge_between_iff_of_even_triple hbx hby hxy (fun e he => (hEdge he).2)
        (hParity hR hRCard))
  let pair : V × V → Finset V := fun p => {p.1, p.2}
  have hPairs : E = (A ×ˢ B).image pair := by
    ext e
    constructor
    · intro he
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hEdge he).2
      have hx : x ∈ W := (hEdge he).1 (Finset.mem_insert_self _ _)
      have hy : y ∈ W := (hEdge he).1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      rcases (hCut hx hy hxy).mp he with ⟨hxA, hyA⟩ | ⟨hxA, hyA⟩
      · exact Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_product.mpr ⟨hxA, Finset.mem_sdiff.mpr ⟨hy, hyA⟩⟩, rfl⟩
      · exact Finset.mem_image.mpr
          ⟨(y, x), Finset.mem_product.mpr ⟨hyA, Finset.mem_sdiff.mpr ⟨hx, hxA⟩⟩,
            Finset.pair_comm y x⟩
    · rintro he
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hxA, hyB⟩ := Finset.mem_product.mp hxy
      obtain ⟨hy, hyA⟩ := Finset.mem_sdiff.mp hyB
      exact (hCut (hASub hxA) hy (fun h => hyA (h ▸ hxA))).mpr (Or.inl ⟨hxA, hyA⟩)
  have hPairInj : Set.InjOn pair (↑(A ×ˢ B) : Set (V × V)) := by
    intro p hp q hq heq
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    obtain ⟨hqA, hqB⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hq)
    have hp₁ : p.1 ∈ pair q := heq ▸ (Finset.mem_insert_self _ _ : p.1 ∈ pair p)
    have hp₂ : p.2 ∈ pair q :=
      heq ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self p.2) : p.2 ∈ pair p)
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hp₁ hp₂
    refine Prod.ext (hp₁.resolve_right ?_) (hp₂.resolve_left ?_)
    · intro h
      exact (Finset.mem_sdiff.mp hqB).2 (h ▸ hpA)
    · intro h
      exact (Finset.mem_sdiff.mp hpB).2 (h.symm ▸ hqA)
  have hProduct : A.card * B.card = C.card := by
    rw [← Finset.card_product, ← Finset.card_image_of_injOn hPairInj, ← hPairs, hECard]
  have hParts : B.card + A.card = 6 :=
    (Finset.card_sdiff_add_card_eq_card hASub).trans hWCard
  have hBack : E.image (fun e => W \ e) = C := by
    ext t
    simp only [E, Finset.mem_image]
    constructor
    · rintro ⟨e, ⟨u, hu, rfl⟩, rfl⟩
      simpa only [hInv hu] using hu
    · intro ht
      exact ⟨W \ t, ⟨t, ht, rfl⟩, hInv ht⟩
  refine ⟨A, B, by omega, hProduct, Finset.disjoint_sdiff, ?_⟩
  calc
    C = E.image (fun e => W \ e) := hBack.symm
    _ = (A ×ˢ B).image (fun p => W \ ({p.1, p.2} : Finset V)) := by
      rw [hPairs, Finset.image_image] <;> rfl
    _ = _ := by rw [Finset.union_sdiff_of_subset hASub]

/-- At equality the tetrahedra are the join of two triangle boundaries.
Each facet omits one vertex from each of two disjoint triples. -/
theorem tetrahedron_cycle_equality (C : Finset (Finset V))
    (hRank : ∀ t ∈ C, t.card = 4)
    (hEven : ∀ r : Finset V, r.card = 3 → Even ((C.filter (r ⊆ ·)).card))
    (hCap : ∀ w : Finset V, w.card = 5 → (C.filter (· ⊆ w)).card ≤ 3)
    (hNine : C.card = 9) :
    ∃ A B : Finset V, A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧
      C = (A ×ˢ B).image (fun p => (A ∪ B) \ ({p.1, p.2} : Finset V)) := by
  have hNonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hSupport, hCount⟩ := support_and_incidence_bound C hNonempty hRank hEven hCap
  obtain ⟨A, B, hParts, hProduct, hDisjoint, hEq⟩ :=
    six_vertex_cycle_cut C hRank hEven (by omega)
  have hACard : A.card = 3 := by
    have hLe : A.card ≤ 6 := by omega
    interval_cases h : A.card <;> (try rw [h] at hProduct) <;> omega
  exact ⟨A, B, hACard, by omega, hDisjoint, hEq⟩

/-- The next order after nine in a tetrahedral cycle with the five-set cap
cannot be ten. Ten facets would still be confined to the six-point cut. -/
theorem ten_ne_card_tetrahedron_cycle (C : Finset (Finset V))
    (hRank : ∀ t ∈ C, t.card = 4)
    (hEven : ∀ r : Finset V, r.card = 3 → Even ((C.filter (r ⊆ ·)).card))
    (hCap : ∀ w : Finset V, w.card = 5 → (C.filter (· ⊆ w)).card ≤ 3) :
    C.card ≠ 10 := by
  intro hTen
  have hNonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hSupport, hCount⟩ := support_and_incidence_bound C hNonempty hRank hEven hCap
  obtain ⟨A, B, hParts, hProduct, _, _⟩ :=
    six_vertex_cycle_cut C hRank hEven (by omega)
  have hLe : A.card ≤ 6 := by omega
  interval_cases h : A.card <;> (try rw [h] at hProduct) <;> omega

end Q9ShellTetrahedronCycle
