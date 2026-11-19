/- GID: D5/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/AlternatingWeldQueryBound
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: The revealed weld edges bound the chance of a new neighbor after complete adaptive queries. -/

import D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound

import D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw

/-! One-step probability bounds after conditioning on complete unordered weld queries. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.Graph.LinearForests
open CompatibleCycleInventory DirectedForestCompletion AlternatingForestSuccessorBound Relation
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound

private theorem vertex_connector_mass_le {V : Type*} [Finite V]
    (E : V → V → Prop) (k : V → Bool) (n : ℕ)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n)
    (hm : Nat.card {p : V × V // E p.1 p.2} + 2 ≤ n)
    (μ : PMF (AlternatingCompletion E k))
    (hμ : ∀ σ, μ σ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹)
    (x : V) (S : Finset V) :
    μ.toOuterMeasure {σ | ∃ y ∈ S, σ.1 x = y ∧ ¬ E x y ∧
      Quotient.mk (EqvGen.setoid E) y ≠ Quotient.mk (EqvGen.setoid E) x} ≤
      (S.card : ℝ≥0∞) / ((n - Nat.card {p : V × V // E p.1 p.2} - 1 : ℕ) : ℝ≥0∞) := by
  classical
  by_cases hx : ∃ y, E x y
  · obtain ⟨z, hz⟩ := hx
    have he : {σ : AlternatingCompletion E k | ∃ y ∈ S, σ.1 x = y ∧ ¬ E x y ∧
        Quotient.mk (EqvGen.setoid E) y ≠ Quotient.mk (EqvGen.setoid E) x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro σ ⟨y, _, hy, hny, _⟩
      exact hny (((σ.2.2.2.1 x z hz).symm.trans hy) ▸ hz)
    rw [he]
    simp
  · obtain ⟨tail, head, ht, hh, hBound⟩ := mass_of_successor_components E k n hr hb hm μ hμ
    let c (v : V) : Component E := Quotient.mk (EqvGen.setoid E) v
    let A := tail.symm ⟨x, hx⟩
    let T := (S.image c).erase A
    have htail : tail A = ⟨x, hx⟩ := tail.apply_symm_apply _
    have hA : c x = A := by
      simpa only [c, htail] using ht A
    have hSub : {σ : AlternatingCompletion E k | ∃ y ∈ S, σ.1 x = y ∧ ¬ E x y ∧ c y ≠ c x} ⊆
        {σ | ∃ B ∈ T, σ.1 (tail A) = (head B).1} := by
      rintro σ ⟨y, hyS, hσ, hne, hcomp⟩
      have hy : ¬ ∃ z, E z y := by
        rintro ⟨z, hz⟩
        have he : z = x := σ.1.injective ((σ.2.2.2.1 _ _ hz).trans hσ.symm)
        exact hne (he ▸ hz)
      let B := head.symm ⟨y, hy⟩
      have he : head B = ⟨y, hy⟩ := head.apply_symm_apply _
      have hB : c y = B := by simpa only [c, he] using hh B
      refine ⟨B, Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨y, hyS, hB⟩⟩, ?_⟩
      · exact hB ▸ hA ▸ hcomp
      · simpa only [htail, he] using hσ
    calc
      _ ≤ μ.toOuterMeasure {σ | ∃ B ∈ T, σ.1 (tail A) = (head B).1} :=
        μ.toOuterMeasure.mono hSub
      _ ≤ (T.card : ℝ≥0∞) / ((n - Nat.card {p : V × V // E p.1 p.2} - 1 : ℕ) : ℝ≥0∞) :=
        hBound A T (Finset.notMem_erase _ _)
      _ ≤ _ := ENNReal.div_le_div_right (Nat.cast_le.mpr
        (Finset.card_erase_le.trans Finset.card_image_le)) _

private theorem unclosed_component {V : Type*} [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (hacyclic : ∀ x, ¬ TransGen E x x) [Nontrivial (Component E)]
    (σ : CycleCompletion E) (x : Tail E) (y : Head E) (he : σ.1 x = y) :
    Quotient.mk (EqvGen.setoid E) y.1 ≠ Quotient.mk (EqvGen.setoid E) x.1 := by
  obtain ⟨t, h, Φ, ht, hh, hΦ⟩ := full_cycle_completion_equiv E hout hin hacyclic
  let A := t.symm x
  let B := h.symm y
  have hx : t A = x := t.apply_symm_apply _
  have hy : h B = y := h.apply_symm_apply _
  intro hsame
  have hs : B = A := by
    have htx := ht A
    have hhy := hh B
    rw [hx] at htx
    rw [hy] at hhy
    exact hhy.symm.trans (hsame.trans htx)
  have hEqAB : (Φ σ).1 A = B := by
    apply h.injective
    have hσ := hΦ σ A
    rw [hx, he] at hσ
    rw [hy]
    apply Subtype.ext
    exact hσ.symm
  have hEq : (Φ σ).1 A = A := hEqAB.trans hs
  exact ((Φ σ).2.apply_ne Set.nontrivial_univ (Set.mem_univ A)) hEq

open scoped BigOperators

section
variable {A B : Type*} [Fintype A] [Fintype B]

private theorem mass_le_of_fibers (p : PMF A) (f : A → B) (s : Set A) (c : ℝ≥0∞)
    (h : ∀ b : B, let t := {a : A | f a = b}
      p.toOuterMeasure (s ∩ t) ≤ c * p.toOuterMeasure t) :
    p.toOuterMeasure s ≤ c := by
  classical
  let fiber (b : B) : Set A := {a | f a = b}
  have hsplit (w : A → ℝ≥0∞) :
      ∑ b : B, ∑ a : A, (fiber b).indicator w a = ∑ a : A, w a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [fiber, Set.indicator, eq_comm]
  rw [PMF.toOuterMeasure_apply_fintype, ← hsplit (s.indicator p)]
  calc
    _ ≤ ∑ b : B, c * ∑ a : A, (fiber b).indicator p a := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [PMF.toOuterMeasure_apply_fintype, Set.indicator_indicator, Set.inter_comm]
        using h b
    _ = c := by
      have hsum : ∑ a : A, p a = 1 := (tsum_fintype (fun a : A => p a)).symm.trans p.tsum_coe
      rw [← Finset.mul_sum, hsplit, hsum, mul_one]

private theorem intersection_mass (p : PMF A) (s t : Set A)
    (ht : ∃ a ∈ t, a ∈ p.support) :
    (p.filter t ht).toOuterMeasure s * p.toOuterMeasure t =
      p.toOuterMeasure (s ∩ t) := by
  classical
  have hZero : p.toOuterMeasure t ≠ 0 := by
    intro hz
    obtain ⟨a, hat, ha⟩ := ht
    exact Set.disjoint_left.mp ((p.toOuterMeasure_apply_eq_zero_iff t).mp hz) ha hat
  have hTop : p.toOuterMeasure t ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top t
  have hMass : (p.filter t ht).toOuterMeasure s =
      p.toOuterMeasure (s ∩ t) * (p.toOuterMeasure t)⁻¹ := by
    rw [PMF.toOuterMeasure_apply_fintype, p.toOuterMeasure_apply_fintype (s ∩ t),
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hs : a ∈ s
    · by_cases hta : a ∈ t
      · simp [Set.indicator, PMF.filter_apply, hs, hta]
      · simp [Set.indicator, PMF.filter_apply, hs, hta]
    · simp [Set.indicator, hs]
  rw [hMass, mul_assoc, ENNReal.inv_mul_cancel hZero hTop, mul_one]

private theorem mass_le_of_conditional_fibers (p : PMF A) (f : A → B) (s : Set A) (c : ℝ≥0∞)
    (h : ∀ b : B, let t := {a : A | f a = b}
      ∀ ht : ∃ a ∈ t, a ∈ p.support,
        (p.filter t ht).toOuterMeasure s ≤ c) :
    p.toOuterMeasure s ≤ c := by
  apply mass_le_of_fibers p f s c
  intro b t
  by_cases ht : ∃ a ∈ t, a ∈ p.support
  · rw [← intersection_mass p s t ht]
    gcongr
    exact h b ht
  · have hz : p.toOuterMeasure (s ∩ t) = 0 := by
      apply (p.toOuterMeasure_apply_eq_zero_iff (s ∩ t)).mpr
      exact Set.disjoint_left.mpr (fun a ha hst => ht ⟨a, hst.2, ha⟩)
    rw [hz]
    exact zero_le



private theorem outgoing_bound {V : Type*} [Fintype V]
    (E : V → V → Prop) (k : V → Bool) (n : ℕ)
    (h0 : Nat.card (Side k false) = n) (h1 : Nat.card (Side k true) = n)
    (hm : Nat.card {p : V × V // E p.1 p.2} + 2 ≤ n)
    (p : PMF (AlternatingCompletion E k))
    (hp : ∀ σ, p σ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹)
    (x : V) (S : Finset V) :
    p.toOuterMeasure {σ | ∃ y ∈ S, σ.1 x = y ∧ ¬ E x y} ≤
      (S.card : ℝ≥0∞) / ((n - Nat.card {p : V × V // E p.1 p.2} - 1 : ℕ) : ℝ≥0∞) := by
  classical
  have hsparse : Nat.card {p : V × V // E p.1 p.2} < Nat.card V := by
    have hc : n ≤ Nat.card V := h0 ▸ Nat.card_le_card_of_injective
      (fun a : Side k false => a.1) Subtype.val_injective
    omega
  obtain ⟨ref, _⟩ := p.support_nonempty
  have hout : Relator.RightUnique E := fun {_ _ _} ha hb =>
    (ref.2.2.2.1 _ _ ha).symm.trans (ref.2.2.2.1 _ _ hb)
  have hin : Relator.LeftUnique E := fun {_ _ _} ha hb =>
    ref.1.injective ((ref.2.2.2.1 _ _ ha).trans (ref.2.2.2.1 _ _ hb).symm)
  have hacyclic := partial_cycle_acyclic E ref.1 ref.2.2.1 ref.2.2.2.1 hsparse
  obtain ⟨_, heads, _, _, _, _⟩ := full_cycle_completion_equiv E hout hin hacyclic
  have hHeads := heads_card_ge E k false
  have hCard : Nat.card {x : Head E // k x = false} ≤ Nat.card (Component E) :=
    (Nat.card_le_card_of_injective (fun x : {x : Head E // k x = false} => x.1)
      Subtype.val_injective).trans_eq (Nat.card_congr heads).symm
  have hTwo : 1 < Nat.card (Component E) := by omega
  let : Fintype (Component E) := Fintype.ofFinite _
  let : Nontrivial (Component E) := Fintype.one_lt_card_iff_nontrivial.mp
    (by rwa [← Nat.card_eq_fintype_card])
  apply le_trans (p.toOuterMeasure.mono ?_) (vertex_connector_mass_le E k n h0 h1 hm p hp x S)
  rintro σ ⟨y, hy, hxy, hnot⟩
  have hx : ¬ ∃ z, E x z := by
    rintro ⟨z, hz⟩
    exact hnot ((σ.2.2.2.1 x z hz).symm.trans hxy ▸ hz)
  have hny : ¬ ∃ z, E z y := by
    rintro ⟨z, hz⟩
    have hzx : z = x := σ.1.injective ((σ.2.2.2.1 z y hz).trans hxy.symm)
    exact hnot (hzx ▸ hz)
  exact ⟨y, hy, hxy, hnot,
    unclosed_component E hout hin hacyclic ⟨σ.1, σ.2.2.1, σ.2.2.2.1⟩
      ⟨x, hx⟩ ⟨y, hny⟩ hxy⟩

end

open AlternatingWeldOrientationLaw AlternatingUndirectedCompletionLaw UndirectedCycleCompletionLaw
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)

private theorem outgoing_mass_on_lifts {V : Type*} [Fintype V] {F : SimpleGraph V}
    (hn : 3 ≤ Fintype.card V) (k : V → Bool) (n : ℕ)
    (h0 : Nat.card (Side k false) = n) (h1 : Nat.card (Side k true) = n)
    (hm : Nat.card F.edgeSet + 2 ≤ n)
    (C : AlternatingCompletedGraph k F) (x : V) (S : Finset V) :
    ∃ (p : PMF (OrientedCompletion (F := F) k)) (q : PMF (AlternatingCompletedGraph k F)),
      (∀ l, p l = (Nat.card (OrientedCompletion (F := F) k) : ℝ≥0∞)⁻¹) ∧
      (∀ g, q g = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
      p.map (forgetOrientation hn k) = q ∧
      p.toOuterMeasure {l | ∃ y ∈ S, l.1.σ x = y ∧ ¬ F.Adj x y} ≤
        (S.card : ℝ≥0∞) / ((n - Nat.card F.edgeSet - 1 : ℕ) : ℝ≥0∞) := by
  classical
  obtain ⟨p, q, hp, hq, hpq, h⟩ := alternating_weld_orientation_law hn k C
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  let : Finite (Lift F) := Finite.of_injective (fun l : Lift F => l.σ)
    (fun _ _ h => lift_ext hn h)
  let : Fintype (OrientedCompletion (F := F) k) := Fintype.ofFinite _
  let : Fintype (V → V → Prop) := Fintype.ofFinite _
  apply mass_le_of_conditional_fibers p (fun l => l.1.E)
  intro R fiber hR
  obtain ⟨ref, href, _⟩ := id hR
  change ref.1.E = R at href
  subst R
  obtain ⟨hc, hLaw⟩ := h ref
  obtain ⟨ρ, toLift, hρ, hLift, hFilter⟩ := hLaw hR
  have hr : Nat.card {a : V × V // ref.1.E a.1 a.2} + 2 ≤ n := hc.symm ▸ hm
  change (p.filter _ hR).toOuterMeasure _ ≤ _
  rw [hFilter, PMF.toOuterMeasure_map_apply]
  let out : Set (AlternatingCompletion ref.1.E k) :=
    {c | ∃ y ∈ S, c.1 x = y ∧ ¬ ref.1.E x y}
  refine (ρ.toOuterMeasure.mono (s₂ := out) ?_).trans ?_
  · rintro c ⟨y, hy, he, hF⟩
    exact ⟨y, hy, (congrArg (fun σ : Equiv.Perm V => σ x) (hLift c).2).symm.trans he,
      fun hE => hF (ref.1.edge x y hE)⟩
  · rw [← hc]
    exact outgoing_bound ref.1.E k n h0 h1 hr ρ hρ x S

private def reversing {V : Type*} [Fintype V] {F : SimpleGraph V} {k : V → Bool}
    (hn : 3 ≤ Fintype.card V) :
    OrientedCompletion (F := F) k ≃ OrientedCompletion (F := F) k := by
  let rev (l : OrientedCompletion (F := F) k) : OrientedCompletion (F := F) k :=
    ⟨reverseLift l.1, fun x => by
      change k (l.1.σ.symm x) ≠ k x
      simpa using (l.2 (l.1.σ.symm x)).symm⟩
  refine
    { toFun := rev
      invFun := rev
      left_inv := ?_
      right_inv := ?_ } <;>
    intro l <;> exact Subtype.ext (lift_ext hn (by simp [rev, reverseLift]))

private theorem weld_neighbor_mass_le {V : Type*} [Fintype V] {F : SimpleGraph V}
    (hn : 3 ≤ Fintype.card V) (k : V → Bool) (n : ℕ)
    (h0 : Nat.card (Side k false) = n) (h1 : Nat.card (Side k true) = n)
    (hm : Nat.card F.edgeSet + 2 ≤ n)
    (C : AlternatingCompletedGraph k F) (x : V) (S : Finset V) :
    ∃ q : PMF (AlternatingCompletedGraph k F),
      (∀ g, q g = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
      q.toOuterMeasure {g | ∃ y ∈ S, g.1.1.Adj x y ∧ ¬ F.Adj x y} ≤
        (2 * S.card : ℝ≥0∞) / ((n - Nat.card F.edgeSet - 1 : ℕ) : ℝ≥0∞) := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hOut⟩ := outgoing_mass_on_lifts hn k n h0 h1 hm C x S
  let A := OrientedCompletion (F := F) k
  let out : Set A := {l | ∃ y ∈ S, l.1.σ x = y ∧ ¬ F.Adj x y}
  let rev : A ≃ A := reversing hn
  let : Finite (Lift F) := Finite.of_injective (fun l : Lift F => l.σ)
    (fun _ _ h => lift_ext hn h)
  let : Fintype A := Fintype.ofFinite _
  let : Nonempty A := ⟨p.support_nonempty.choose⟩
  have hUniform : p = uniformPmf A := by
    apply PMF.ext
    intro l
    simpa only [uniformPmf, PMF.ofFintype_apply, ← Nat.card_eq_fintype_card] using hp l
  have hRev : p.map rev = p := by rw [hUniform, uniform_equiv rev]
  refine ⟨q, hq, ?_⟩
  rw [← hpq, PMF.toOuterMeasure_map_apply]
  calc
    _ ≤ p.toOuterMeasure (out ∪ rev ⁻¹' out) := by
      apply p.toOuterMeasure.mono
      rintro l ⟨y, hy, hadj, hnF⟩
      change (shadow l.1.σ).Adj x y at hadj
      rcases (shadow_adj hn l.1.σ l.1.full x y).mp hadj with h | h
      · exact Or.inl ⟨y, hy, h, hnF⟩
      · have hyx : l.1.σ.symm x = y := l.1.σ.symm_apply_eq.mpr h.symm
        exact Or.inr ⟨y, hy, hyx, hnF⟩
    _ ≤ p.toOuterMeasure out + p.toOuterMeasure (rev ⁻¹' out) :=
      MeasureTheory.measure_union_le _ _
    _ = p.toOuterMeasure out + p.toOuterMeasure out := by
      rw [← PMF.toOuterMeasure_map_apply rev p out, hRev]
    _ ≤ _ := by
      rw [two_mul, ENNReal.add_div]
      exact add_le_add hOut hOut

open D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
open SimpleGraph
open scoped BigOperators

private theorem recorded_weld_edge_budget {V L : Type*} [Fintype L]
    (e : L ↪ V) (fixed : SimpleGraph V) (G : SimpleGraph L)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2) (T : History V)
    (hsub : (revealedEdges T \ fixed).comap e ≤ G) :
    Nat.card (((revealedEdges T \ fixed).comap e).edgeSet) ≤ 2 * T.length := by
  classical
  let F := (revealedEdges T \ fixed).comap e
  let queries := (T.map (fun r => r.1)).toFinset
  let allowed (x : V) : Finset (Sym2 L) :=
    if h : x ∈ Set.range e then G.incidenceFinset h.choose else ∅
  have hAdmit : F.edgeFinset ⊆ queries.biUnion allowed := by
    intro edge hp
    induction edge using Sym2.ind with
    | h a b =>
      have ha : F.Adj a b := F.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hp)
      have hG := hsub ha
      have hR : (revealedEdges T).Adj (e a) (e b) := ha.1
      rw [revealedEdges, fromRel_adj] at hR
      obtain ⟨_, hab | hba⟩ := hR
      · obtain ⟨row, hr, he, _⟩ := hab
        have hqa : e a ∈ queries := by
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, hr, he.symm⟩)
        refine Finset.mem_biUnion.mpr ⟨e a, hqa, ?_⟩
        have hea : e a ∈ Set.range e := ⟨a, rfl⟩
        simp only [allowed, dite_eq_left hea, e.injective hea.choose_spec, mem_incidenceFinset]
        exact G.mk'_mem_incidenceSet_left_iff.mpr hG
      · obtain ⟨row, hr, he, _⟩ := hba
        have hqb : e b ∈ queries := by
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, hr, he.symm⟩)
        refine Finset.mem_biUnion.mpr ⟨e b, hqb, ?_⟩
        have heb : e b ∈ Set.range e := ⟨b, rfl⟩
        simp only [allowed, dite_eq_left heb, e.injective heb.choose_spec, mem_incidenceFinset]
        exact G.mk'_mem_incidenceSet_right_iff.mpr hG
  have hb (x : V) : (allowed x).card ≤ 2 := by
    by_cases h : x ∈ Set.range e
    · simp only [allowed, dite_eq_left h, G.card_incidenceFinset_eq_degree, ← G.ncard_neighborSet]
      exact hdeg h.choose
    · simp only [allowed, dite_eq_right h, Finset.card_empty, Nat.zero_le]
  have hq : queries.card ≤ T.length := by
    exact (List.toFinset_card_le _).trans_eq (List.length_map _)
  change Nat.card F.edgeSet ≤ 2 * T.length
  rw [← F.coe_edgeFinset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  calc
    _ ≤ (queries.biUnion allowed).card := Finset.card_le_card hAdmit
    _ ≤ ∑ x ∈ queries, (allowed x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ queries, (2 : ℕ) := Finset.sum_le_sum (fun x _ => hb x)
    _ = 2 * queries.card := by simp [Nat.mul_comm]
    _ ≤ 2 * T.length := Nat.mul_le_mul_left _ hq

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript

private theorem color_partition_card {L : Type*} [Fintype L] (k : L → Bool) (n : ℕ)
    (h0 : Nat.card (Side k false) = n) (h1 : Nat.card (Side k true) = n) :
    Fintype.card L = 2 * n := by
  classical
  let other : Side k true ≃ {x : L // ¬ k x = false} :=
    Equiv.subtypeEquivRight (fun x => by cases k x <;> simp)
  let e : (Side k false ⊕ Side k true) ≃ L :=
    ((Equiv.refl (Side k false)).sumCongr other).trans (Equiv.sumCompl (fun x => k x = false))
  rw [← Fintype.card_congr e, Fintype.card_sum, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, h0, h1, two_mul]

/-- Bound the conditional probability of a new weld edge from a fixed leaf into a target set,
using the number of queries in the actual full-neighborhood transcript. -/
theorem weld_query_prefix_bound {V L : Type*} [Finite V] [Fintype L]
    (e : L ↪ V) (k : L → Bool) (n : ℕ) (hn : 2 ≤ n)
    (h0 : Nat.card (Side k false) = n) (h1 : Nat.card (Side k true) = n)
    (p : PassiveProtocol V (fun _ => Set V)) (fixed : SimpleGraph V)
    (ref : AlternatingCompletedGraph k ⊥) (hdisjoint : Disjoint fixed (ref.1.1.map e))
    (μ : PMF (AlternatingCompletedGraph k ⊥))
    (hμ : ∀ C, μ C = ((n.factorial * (n - 1).factorial / 2 : ℕ) : ℝ≥0∞)⁻¹)
    (x : L) (S : Finset L) :
    let T := runPassiveProtocol readNeighbors p (fixed ⊔ ref.1.1.map e)
    let F := (revealedEdges T \ fixed).comap e
    let event : Set (AlternatingCompletedGraph k ⊥) :=
      {C | runPassiveProtocol readNeighbors p (fixed ⊔ C.1.1.map e) = T}
    ∀ hEvent : ∃ C ∈ event, C ∈ μ.support,
      2 * T.length + 2 ≤ n →
      (μ.filter event hEvent).toOuterMeasure
        {C | ∃ y ∈ S, C.1.1.Adj x y ∧ ¬ F.Adj x y} ≤
        (2 * S.card : ℝ≥0∞) / ((n - 2 * T.length - 1 : ℕ) : ℝ≥0∞) := by
  classical
  intro T F event hEvent hq
  obtain ⟨he, _, hpost⟩ := weld_transcript_law e k n hn h0 h1 p fixed ref hdisjoint μ hμ
  have hv : event = {C | F ≤ C.1.1} := he
  have hsub : F ≤ ref.1.1 := by
    have href : ref ∈ event := rfl
    rw [hv] at href
    exact href
  have hbudget : Nat.card F.edgeSet ≤ 2 * T.length :=
    recorded_weld_edge_budget e fixed ref.1.1 (fun v => (ref.1.2.2.1 v).le) T hsub
  have hm : Nat.card F.edgeSet + 2 ≤ n := by omega
  let lift : AlternatingCompletedGraph k F :=
    ⟨⟨ref.1.1, ref.1.2.1, ref.1.2.2.1, hsub⟩, ref.2⟩
  have hL : 3 ≤ Fintype.card L := by rw [color_partition_card k n h0 h1]; omega
  obtain ⟨ν, hν, hfilter⟩ := hpost hEvent
  obtain ⟨ρ, hρ, hbound⟩ := weld_neighbor_mass_le hL k n h0 h1 hm lift x S
  have heq : ν = ρ := PMF.ext (fun c => (hν c).trans (hρ c).symm)
  change (μ.filter _ hEvent).toOuterMeasure _ ≤ _
  rw [hfilter, heq, PMF.toOuterMeasure_map_apply]
  exact hbound.trans (ENNReal.div_le_div_left (Nat.cast_le.mpr (by omega)) _)

end D5.S3.Combinatorics.Graph.Queries.AlternatingWeldQueryBound
