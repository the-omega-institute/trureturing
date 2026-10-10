/- GID: D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.result; premises=D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.C4_cliques,D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.C4_deletion_routes,D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.C4_clique_card,D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.base_noChord
   digest: Every positive connectivity admits a nonchordal unstable marked clique polynomial. -/

/-
proof_shape: result: bind-only.
escape_witness: none (open-problem-resolution basis).
admission_basis: open-problem-resolution (#14258; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Auxiliary proof_shape: bind-only for each consumed theorem listed below.
join_inl: proof_shape: bind-only; consumer: clique_join, connected_after.
join_inr: proof_shape: bind-only; consumer: clique_join, connected_after, family_nonchordal.
join_cross: proof_shape: bind-only; consumer: clique_join, connected_after.
join_cross': proof_shape: bind-only; consumer: clique_join.
clique_join: proof_shape: bind-only; consumer: C_B_join, clique_card.
C_B_sum: proof_shape: bind-only; consumer: C_B_join.
inter_disjSum: proof_shape: bind-only; consumer: C_B_join.
C_B_join: proof_shape: bind-only; consumer: family_factor.
complete_factor: proof_shape: bind-only; consumer: family_factor.
C4_cliques: proof_shape: bind-only; consumer: C4_factor.
C4_factor: proof_shape: bind-only; consumer: family_factor.
family_factor: proof_shape: bind-only; consumer: family_zero.
C4_deletion_routes: proof_shape: bind-only; consumer: connected_after.
connected_of_center: proof_shape: bind-only; consumer: connected_after.
connected_after: proof_shape: bind-only; consumer: family_connected.
family_connected: proof_shape: bind-only; consumer: family.
C4_clique_card: proof_shape: bind-only; consumer: clique_card.
clique_card: proof_shape: bind-only; consumer: family_cliqueFree.
family_cliqueFree: proof_shape: bind-only; consumer: family.
base_noChord: proof_shape: bind-only; consumer: family_nonchordal.
family_nonchordal: proof_shape: bind-only; consumer: family.
family_zero: proof_shape: bind-only; consumer: family_unstable.
family_unstable: proof_shape: bind-only; consumer: family.
family: proof_shape: bind-only; consumer: result.
Computational content: numeric-reduction; result consumes the finite cycle premises
through the join factorization, deletion connectivity and induced chordless cycle.
All four header premises are proved below; the parameter r is unbounded.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Analysis.Complex.Basic

open Finset Complex
open scoped Classical
namespace D5.S3.Combinatorics.Graph.CliquePolynomial.FaalNonStable
set_option maxHeartbeats 2000000

noncomputable def C_B {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (x y : ℂ) : ℂ := by
  exact ∑ K ∈ (Finset.univ : Finset V).powerset.filter (fun (K : Finset V) => G.IsClique (K : Set V)),
    x ^ K.card * y ^ (K ∩ B).card

def RealStable (f : ℂ → ℂ → ℂ) : Prop :=
  (∃ x y, f x y ≠ 0) ∧ ∀ x y, 0 < x.im → 0 < y.im → f x y ≠ 0

def RConnected {V : Type} [Fintype V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  r < Fintype.card V ∧ ∀ S : Finset V, S.card < r →
    (G.induce {v | v ∉ S}).Connected

def HasChord {V : Type} {G : SimpleGraph V} {v : V} (p : G.Walk v v) : Prop :=
  ∃ i j : Fin p.length, i.val + 1 < j.val ∧
    ¬(i.val = 0 ∧ j.val + 1 = p.length) ∧ G.Adj (p.getVert i) (p.getVert j)

def Chordal {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → 4 ≤ p.length → HasChord p

def claim : Prop := ∀ r : ℕ, 1 ≤ r →
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
    (_ : DecidableRel G.Adj) (B : Finset V),
    RConnected G r ∧ G.CliqueFree (r + 3) ∧ ¬Chordal G ∧ ¬RealStable (C_B G B)


private abbrev join {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  (Gᶜ.sum Hᶜ)ᶜ

@[simp] private theorem join_inl {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (u v : V) :
    (join G H).Adj (.inl u) (.inl v) ↔ G.Adj u v := by
  simp [join]
  exact ⟨fun h => h.2 h.1, fun h => ⟨h.ne, fun _ => h⟩⟩
@[simp] private theorem join_inr {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (u v : W) :
    (join G H).Adj (.inr u) (.inr v) ↔ H.Adj u v := by
  simp [join]
  exact ⟨fun h => h.2 h.1, fun h => ⟨h.ne, fun _ => h⟩⟩
@[simp] private theorem join_cross {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (u : V) (v : W) :
    (join G H).Adj (.inl u) (.inr v) := by simp [join]
@[simp] private theorem join_cross' {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (u : W) (v : V) :
    (join G H).Adj (.inr u) (.inl v) := by simp [join]

private theorem clique_join {V W : Type} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (s : Finset V) (t : Finset W) :
    (join G H).IsClique (s.disjSum t : Set (V ⊕ W)) ↔
      G.IsClique (s : Set V) ∧ H.IsClique (t : Set W) := by
  constructor
  · intro h
    constructor
    · intro u hu v hv hne
      exact (join_inl G H u v).mp (h (by simpa using hu) (by simpa using hv) (by simpa using hne))
    · intro u hu v hv hne
      exact (join_inr G H u v).mp (h (by simpa using hu) (by simpa using hv) (by simpa using hne))
  · rintro ⟨hs, ht⟩ (u | u) hu (v | v) hv hne
    · exact (join_inl G H u v).mpr (hs (by simpa using hu) (by simpa using hv) (by simpa using hne))
    · exact join_cross G H u v
    · exact join_cross' G H u v
    · exact (join_inr G H u v).mpr (ht (by simpa using hu) (by simpa using hv) (by simpa using hne))

private noncomputable def cliqueWeight {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (x y : ℂ) (K : Finset V) : ℂ :=
  @ite ℂ (G.IsClique (K : Set V)) (Classical.propDecidable _)
    (x ^ K.card * y ^ (K ∩ B).card) 0

private theorem C_B_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (x y : ℂ) :
    C_B G B x y = ∑ K : Finset V, cliqueWeight G B x y K := by
  simp only [C_B, cliqueWeight, Finset.powerset_univ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro K hK
  by_cases h : G.IsClique (K : Set V) <;> simp only [h, if_true, if_false]

private theorem inter_disjSum {V W : Type} [DecidableEq V] [DecidableEq W]
    (s A : Finset V) (t B : Finset W) :
    s.disjSum t ∩ A.disjSum B = (s ∩ A).disjSum (t ∩ B) := by
  ext (v | w) <;> simp

private theorem C_B_join {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (A : Finset V) (B : Finset W) (x y : ℂ) :
    C_B (join G H) (A.disjSum B) x y = C_B G A x y * C_B H B x y := by
  simp only [C_B_sum]
  let f : Finset (V ⊕ W) → ℂ := cliqueWeight (join G H) (A.disjSum B) x y
  have he : (∑ K, f K) = ∑ p : Finset V × Finset W, f (p.1.disjSum p.2) :=
    ((Finset.sumEquiv : Finset (V ⊕ W) ≃o Finset V × Finset W).toEquiv.symm.sum_comp f).symm
  change (∑ K, f K) = _
  rw [he]
  dsimp only [f]
  simp only [cliqueWeight, clique_join, inter_disjSum, Finset.card_disjSum]
  rw [Fintype.sum_prod_type]
  simp only [pow_add]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp_all <;> ring


private abbrev G (a : ℕ) : SimpleGraph (Fin a ⊕ Fin 4) := join ⊤ (SimpleGraph.cycleGraph 4)
private def B (a : ℕ) : Finset (Fin a ⊕ Fin 4) := {Sum.inr 0}

private theorem complete_factor (a : ℕ) (x y : ℂ) :
    C_B (⊤ : SimpleGraph (Fin a)) ∅ x y = (1 + x)^a := by
  simpa [C_B, Finset.sum_filter] using
    (Finset.prod_one_add (f := fun _ : Fin a => x) Finset.univ).symm

private theorem C4_cliques :
    (Finset.univ : Finset (Fin 4)).powerset.filter (fun (K : Finset (Fin 4)) => (SimpleGraph.cycleGraph 4).IsClique (K : Set (Fin 4))) =
      {∅, {0}, {1}, {2}, {3}, {0,1}, {1,2}, {2,3}, {0,3}} := by
  ext K
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  revert K
  decide

private theorem C4_factor (x y : ℂ) : C_B (SimpleGraph.cycleGraph 4) {0} x y = (1 + 2*x) * (1 + x + x*y) := by
  unfold C_B
  have hc : (Finset.univ : Finset (Fin 4)).powerset.filter (fun (K : Finset (Fin 4)) => (SimpleGraph.cycleGraph 4).IsClique (K : Set (Fin 4))) =
      {∅, {0}, {1}, {2}, {3}, {0,1}, {1,2}, {2,3}, {0,3}} := by
    convert C4_cliques using 1
  convert_to (∑ K ∈ ({∅, {0}, {1}, {2}, {3}, {0,1}, {1,2}, {2,3}, {0,3}} : Finset (Finset (Fin 4))),
    x ^ K.card * y ^ (K ∩ {0}).card) = (1 + 2*x)*(1+x+x*y) using 1
  · congr 1
    convert hc using 1
    all_goals
      ext K
      simp only [Finset.mem_filter]
  repeat' rw [Finset.sum_insert (by decide)]
  have h2 : ({2} : Finset (Fin 4)) ∩ {0} = ∅ := by decide
  have h3 : ({3} : Finset (Fin 4)) ∩ {0} = ∅ := by decide
  have h23 : ({2,3} : Finset (Fin 4)) ∩ {0} = ∅ := by decide
  have h12c : ({1,2} : Finset (Fin 4)).card = 2 := by decide
  have h23c : ({2,3} : Finset (Fin 4)).card = 2 := by decide
  have h03c : ({0,3} : Finset (Fin 4)).card = 2 := by decide
  norm_num [h2, h3, h23, h12c, h23c, h03c]
  ring

private theorem family_factor (a : ℕ) (x y : ℂ) :
    C_B (G a) (B a) x y = (1+x)^a * (1+2*x) * (1+x+x*y) := by
  have hb : B a = (∅ : Finset (Fin a)).disjSum ({0} : Finset (Fin 4)) := by simp [B]
  rw [hb, G, C_B_join, complete_factor, C4_factor]
  ring


private theorem C4_deletion_routes : ∀ T : Finset (Fin 4), T.card ≤ 1 →
    (∃ u, u ∉ T) ∧ ∀ u v, u ∉ T → v ∉ T →
      u = v ∨ (SimpleGraph.cycleGraph 4).Adj u v ∨ ∃ w, w ∉ T ∧ (SimpleGraph.cycleGraph 4).Adj u w ∧ (SimpleGraph.cycleGraph 4).Adj w v := by decide

private theorem connected_of_center {V : Type} (H : SimpleGraph V) (c : V)
    (hc : ∀ w, H.Reachable c w) : H.Connected :=
  (H.connected_iff_exists_forall_reachable).mpr ⟨c, hc⟩

private theorem connected_after (a : ℕ) (S : Finset (Fin a ⊕ Fin 4))
    (hS : S.card < a + 2) : ((G a).induce {v | v ∉ S}).Connected := by
  by_cases hleft : ∃ c : Fin a, Sum.inl c ∉ S
  · obtain ⟨c, hc⟩ := hleft
    refine connected_of_center _ ⟨Sum.inl c, hc⟩ ?_
    intro w
    by_cases he : w = ⟨Sum.inl c, hc⟩
    · subst w; exact SimpleGraph.Reachable.rfl
    · apply SimpleGraph.Adj.reachable
      change (G a).Adj (Sum.inl c) w.val
      rcases w with ⟨(v | v), hv⟩
      · apply (join_inl ⊤ (SimpleGraph.cycleGraph 4) c v).mpr
        change c ≠ v
        intro hh
        apply he
        subst v
        rfl
      · exact join_cross ⊤ (SimpleGraph.cycleGraph 4) c v
  · have hfull : (Finset.univ : Finset (Fin a)) ⊆ S.toLeft := by
      intro c hc
      simp only [Finset.mem_toLeft]
      by_contra h
      exact hleft ⟨c, h⟩
    have hcardL : a ≤ S.toLeft.card := by
      simpa using Finset.card_le_card hfull
    have hcardR : S.toRight.card ≤ 1 := by
      have he := Finset.card_toLeft_add_card_toRight (u := S)
      omega
    obtain ⟨hne, hroutes⟩ := C4_deletion_routes S.toRight hcardR
    obtain ⟨c, hc⟩ := hne
    have hcin : Sum.inr c ∉ S := by simpa using hc
    refine connected_of_center _ ⟨Sum.inr c, hcin⟩ ?_
    rintro ⟨(v | v), hv⟩
    · exact False.elim (hleft ⟨v, hv⟩)
    · have hv' : v ∉ S.toRight := by simpa using hv
      rcases hroutes c v hc hv' with he | ha | ⟨w, hw, hcw, hwv⟩
      · subst v; exact SimpleGraph.Reachable.rfl
      · apply SimpleGraph.Adj.reachable
        exact (join_inr ⊤ (SimpleGraph.cycleGraph 4) c v).mpr ha
      · have hw' : Sum.inr w ∉ S := by simpa using hw
        have h₁ : ((G a).induce {v | v ∉ S}).Adj
          ⟨Sum.inr c, hcin⟩ ⟨Sum.inr w, hw'⟩ := (join_inr ⊤ (SimpleGraph.cycleGraph 4) c w).mpr hcw
        have h₂ : ((G a).induce {v | v ∉ S}).Adj
          ⟨Sum.inr w, hw'⟩ ⟨Sum.inr v, hv⟩ := (join_inr ⊤ (SimpleGraph.cycleGraph 4) w v).mpr hwv
        exact h₁.reachable.trans h₂.reachable

private theorem family_connected (r : ℕ) (hr : 1 ≤ r) : RConnected (G (r - 2)) r := by
  constructor
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · intro S hS
    apply connected_after
    omega

private theorem C4_clique_card : ∀ K : Finset (Fin 4), (SimpleGraph.cycleGraph 4).IsClique (K : Set (Fin 4)) → K.card ≤ 2 := by decide

private theorem clique_card (a : ℕ) (K : Finset (Fin a ⊕ Fin 4))
    (hK : (G a).IsClique (K : Set (Fin a ⊕ Fin 4))) : K.card ≤ a + 2 := by
  have he := Finset.toLeft_disjSum_toRight (u := K)
  have hs : (join (⊤ : SimpleGraph (Fin a)) (SimpleGraph.cycleGraph 4)).IsClique (K.toLeft.disjSum K.toRight : Set (Fin a ⊕ Fin 4)) := by
    simpa only [he, G] using hK
  have hc := (clique_join ⊤ (SimpleGraph.cycleGraph 4) K.toLeft K.toRight).mp hs
  have hR := C4_clique_card K.toRight hc.2
  have hL : K.toLeft.card ≤ a := by simpa using Finset.card_le_univ K.toLeft
  have hsum := Finset.card_toLeft_add_card_toRight (u := K)
  omega

private theorem family_cliqueFree (r : ℕ) : (G (r - 2)).CliqueFree (r + 3) := by
  intro K hK
  have hbound := clique_card (r - 2) K hK.isClique
  have he := hK.card_eq
  omega


private abbrev cycleHom (a : ℕ) : (SimpleGraph.cycleGraph 4) →g G a :=
  ((SimpleGraph.Embedding.complEquiv
    (SimpleGraph.Embedding.sumInr : (SimpleGraph.cycleGraph 4)ᶜ ↪g
      ((⊤ : SimpleGraph (Fin a))ᶜ).sum (SimpleGraph.cycleGraph 4)ᶜ)).toHom).comp
    (SimpleGraph.Hom.ofLE
      (by simp : SimpleGraph.cycleGraph 4 ≤ (SimpleGraph.cycleGraph 4)ᶜᶜ))

private def fourWalk (a : ℕ) : (G a).Walk (Sum.inr 0) (Sum.inr 0) :=
  (SimpleGraph.cycleGraph.cycle 1).map (cycleHom a)

private theorem base_noChord : ¬ HasChord (SimpleGraph.cycleGraph.cycle 1) := by
  intro ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hw, ha⟩
  have hl : (SimpleGraph.cycleGraph.cycle 1).length = 4 :=
    SimpleGraph.cycleGraph.length_cycle
  simp only [hl] at hi hj hij hw
  have hi' : i ≤ 1 + 3 := by omega
  have hj' : j ≤ 1 + 3 := by omega
  rw [SimpleGraph.cycleGraph.getVert_cycle hi', SimpleGraph.cycleGraph.getVert_cycle hj'] at ha
  have hp : (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by omega
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert ha <;> decide

private theorem family_nonchordal (a : ℕ) : ¬Chordal (G a) := by
  intro h
  have hc : (fourWalk a).IsCycle := by
    apply (SimpleGraph.Walk.isCycle_map_iff_of_injective (f := cycleHom a) Sum.inr_injective).mpr
    exact SimpleGraph.cycleGraph.isCycle_cycle
  have hlength : (fourWalk a).length = (SimpleGraph.cycleGraph.cycle 1).length :=
    SimpleGraph.Walk.length_map (cycleHom a) (SimpleGraph.cycleGraph.cycle 1)
  have hl : 4 ≤ (fourWalk a).length := by
    rw [hlength, SimpleGraph.cycleGraph.length_cycle]
  obtain ⟨i, j, hij, hw, ha⟩ := h (Sum.inr 0) (fourWalk a) hc hl
  apply base_noChord
  let i' : Fin (SimpleGraph.cycleGraph.cycle 1).length :=
    ⟨i.val, by rw [← hlength]; exact i.isLt⟩
  let j' : Fin (SimpleGraph.cycleGraph.cycle 1).length :=
    ⟨j.val, by rw [← hlength]; exact j.isLt⟩
  refine ⟨i', j', hij, ?_, ?_⟩
  · simpa only [hlength] using hw
  · have hget (n : ℕ) : (fourWalk a).getVert n =
        Sum.inr ((SimpleGraph.cycleGraph.cycle 1).getVert n) :=
      SimpleGraph.Walk.getVert_map (cycleHom a) (SimpleGraph.cycleGraph.cycle 1) n
    rw [hget, hget] at ha
    exact (join_inr ⊤ (SimpleGraph.cycleGraph 4) _ _).mp ha

private theorem family_zero (a : ℕ) : C_B (G a) (B a) Complex.I (-1 + Complex.I) = 0 := by
  rw [family_factor]
  have hz : (1 : ℂ) + Complex.I + Complex.I * (-1 + Complex.I) = 0 := by
    simp [mul_add, Complex.I_mul_I]
  rw [hz, mul_zero]

private theorem family_unstable (a : ℕ) : ¬ RealStable (C_B (G a) (B a)) := by
  intro h
  have hz := h.2 Complex.I (-1 + Complex.I) (by simp) (by simp)
  exact hz (family_zero a)

private theorem family (r : ℕ) (hr : 1 ≤ r) :
    RConnected (G (r-2)) r ∧ (G (r-2)).CliqueFree (r+3) ∧
    ¬Chordal (G (r-2)) ∧ ¬RealStable (C_B (G (r-2)) (B (r-2))) :=
  ⟨family_connected r hr, family_cliqueFree r, family_nonchordal (r-2), family_unstable (r-2)⟩

theorem result : claim := by
  intro r hr
  refine ⟨Fin (r-2) ⊕ Fin 4, inferInstance, inferInstance, G (r-2), inferInstance,
    B (r-2), family r hr⟩

end D5.S3.Combinatorics.Graph.CliquePolynomial.FaalNonStable
