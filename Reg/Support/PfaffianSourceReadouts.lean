import Reg.Support.UniverseSingleReadout

namespace Reg.Support.PfaffianSourceReadouts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe t s
noncomputable section

abbrev equalitySignature (P : Type t) (X : P → Type s) : Signature :=
  Reg.Support.UniverseSingleReadout.signature P X (fun p => X p → Prop)

def equalityActual (P : Type t) (X : P → Type s) : Realization (equalitySignature P X) :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected (P : Type t) (X : P → Type s) : Realization (equalitySignature P X) :=
  realize _ (fun _ _ x y => x ≠ y) (fun e => nomatch e)

theorem equalityDependence {P : Type t} {X : P → Type s}
    (h : ∃ p, ∃ x y : X p, x ≠ y) :
    ObservationalDependence (equalitySignature P X) (equalityActual P X) := by
  intro i
  obtain ⟨p, x, y, hxy⟩ := h
  refine ⟨p, x, y, ?_⟩
  intro he
  exact hxy ((congrFun he y).mpr rfl)

abbrev finSignature := equalitySignature ℕ (fun n => Fin (2*n))
abbrev finActual := equalityActual ℕ (fun n => Fin (2*n))
abbrev finRejected := equalityRejected ℕ (fun n => Fin (2*n))

theorem finDependence : ObservationalDependence finSignature finActual :=
  equalityDependence ⟨1, 0, 1, by decide⟩

abbrev unitSignature := equalitySignature Unit (fun _ => ℤˣ)
abbrev unitActual := equalityActual Unit (fun _ => ℤˣ)
abbrev unitRejected := equalityRejected Unit (fun _ => ℤˣ)

theorem unitDependence : ObservationalDependence unitSignature unitActual :=
  equalityDependence ⟨(), 1, -1, by decide⟩

end
end Reg.Support.PfaffianSourceReadouts

import D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian

namespace Reg.Support.PfaffianAlternatingCycle
open _root_.D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open _root_.D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open _root_.D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing
open _root_.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PfaffianSourceReadouts LeanInformationAudit

noncomputable section
universe u

abbrev adjacencySignature : Signature where
  Params := Σ V : Type u, (⊤ : SimpleGraph V).Subgraph
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def adjacencyActual : Realization adjacencySignature.{u} :=
  realize _ (fun _ p x y => p.2.Adj x y) (fun e => nomatch e)
def adjacencyRejected : Realization adjacencySignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev predicateSignature : Signature where
  Params := Type u
  State V := V → V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def predicateActual : Realization predicateSignature.{u} :=
  realize _ (fun _ _ f => @decide (Function.Involutive f) (Classical.propDecidable _)) (fun e => nomatch e)
def predicateRejected : Realization predicateSignature.{u} :=
  realize _ (fun _ _ _ => false) (fun e => nomatch e)

abbrev perfectSignature : Signature where
  Params := ℕ
  State n := (⊤ : SimpleGraph (Fin (2*n))).Subgraph
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def perfectActual : Realization perfectSignature :=
  realize _ (fun _ _ M => @decide M.IsPerfectMatching (Classical.propDecidable _)) (fun e => nomatch e)
def perfectRejected : Realization perfectSignature :=
  realize _ (fun _ _ _ => false) (fun e => nomatch e)

abbrev graphPerfectSignature : Signature where
  Params := Σ V : Type u, SimpleGraph V
  State p := p.2.Subgraph
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def graphPerfectActual : Realization graphPerfectSignature.{u} :=
  realize _ (fun _ _ M => @decide M.IsPerfectMatching (Classical.propDecidable _)) (fun e => nomatch e)
def graphPerfectRejected : Realization graphPerfectSignature.{u} :=
  realize _ (fun _ _ _ => false) (fun e => nomatch e)

abbrev matchingAdjSignature : Signature where
  Params := Σ V : Type u, Σ G : SimpleGraph V, {M : G.Subgraph // M.IsPerfectMatching}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def matchingAdjActual : Realization matchingAdjSignature.{u} :=
  realize _ (fun _ p x y => p.2.2.val.Adj x y) (fun e => nomatch e)
def matchingAdjRejected : Realization matchingAdjSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev pairingSignature := equalitySignature ℕ P
abbrev pairingActual := equalityActual ℕ P
abbrev pairingRejected := equalityRejected ℕ P
abbrev matchingSignature := equalitySignature ℕ
  (fun n => {M : (⊤ : SimpleGraph (Fin (2*n))).Subgraph // M.IsPerfectMatching})
abbrev matchingActual := equalityActual ℕ
  (fun n => {M : (⊤ : SimpleGraph (Fin (2*n))).Subgraph // M.IsPerfectMatching})
abbrev matchingRejected := equalityRejected ℕ
  (fun n => {M : (⊤ : SimpleGraph (Fin (2*n))).Subgraph // M.IsPerfectMatching})
abbrev vertexSignature := equalitySignature (Type u) (fun V => V)
abbrev vertexActual := equalityActual (Type u) (fun V => V)
abbrev vertexRejected := equalityRejected (Type u) (fun V => V)

namespace MateAdj
abbrev arena : Arena where
  signature := adjacencySignature.{u}
  Law r := ∀ {V : Type u} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v : V), r.readout () ⟨V, M⟩ v (matchingMate M hM v)

theorem actual_law : arena.{u}.Law adjacencyActual.{u} := @matchingMate_adj.{u}
theorem bridge : (type_of% @matchingMate_adj.{u}) ↔ arena.{u}.Law adjacencyActual.{u} := Iff.rfl

end MateAdj

namespace MateIff
abbrev arena : Arena where
  signature := adjacencySignature.{u}
  Law r := ∀ {V : Type u} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v w : V),
    matchingMate M hM v = w ↔ r.readout () ⟨V, M⟩ v w

theorem actual_law : arena.{u}.Law adjacencyActual.{u} := @matchingMate_eq_iff.{u}
theorem bridge : (type_of% @matchingMate_eq_iff.{u}) ↔ arena.{u}.Law adjacencyActual.{u} := Iff.rfl

end MateIff

namespace MateInvolutive
abbrev arena : Arena where
  signature := predicateSignature.{u}
  Law r := ∀ {V : Type u} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching),
    r.readout () V (matchingMate M hM) = true

theorem actual_law : arena.{u}.Law predicateActual.{u} := by
  classical
  simpa only [arena, predicateActual, realize, decide_eq_true_eq] using @matchingMate_involutive.{u}
theorem bridge : (type_of% @matchingMate_involutive.{u}) ↔ arena.{u}.Law predicateActual.{u} := by
  classical
  simp only [arena, predicateActual, realize, decide_eq_true_eq]

end MateInvolutive

namespace MateNe
abbrev arena : Arena where
  signature := vertexSignature.{u}
  Law r := ∀ {V : Type u} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v : V),
    r.readout () V (matchingMate M hM v) v

theorem actual_law : arena.{u}.Law vertexRejected.{u} := @matchingMate_ne.{u}
theorem bridge : (type_of% @matchingMate_ne.{u}) ↔ arena.{u}.Law vertexRejected.{u} := Iff.rfl

end MateNe

namespace PairingPerfect
abbrev arena : Arena where
  signature := perfectSignature
  Law r := ∀ {n : ℕ} (p : P n),
    r.readout () n (pairingGraph p) = true

theorem actual_law : arena.Law perfectActual := by
  classical
  simpa only [arena, perfectActual, realize, decide_eq_true_eq] using @pairingGraph_perfect
theorem bridge : (type_of% @pairingGraph_perfect) ↔ arena.Law perfectActual := by
  classical
  simp only [arena, perfectActual, realize, decide_eq_true_eq]

end PairingPerfect

namespace PairingInverse
abbrev arena : Arena where
  signature := pairingSignature
  Law r := ∀ {n : ℕ} (p : P n),
    r.readout () n (matchingToPairing n (pairingToMatching p)) p

theorem actual_law : arena.Law pairingActual := @pairing_matching_inverse
theorem bridge : (type_of% @pairing_matching_inverse) ↔ arena.Law pairingActual := Iff.rfl

end PairingInverse

namespace MatchingInverse
abbrev arena : Arena where
  signature := matchingSignature
  Law r := ∀ (n : ℕ)
    (M : {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching}),
    r.readout () n (pairingToMatching (matchingToPairing n M)) M

theorem actual_law : arena.Law matchingActual := @matching_pairing_inverse
theorem bridge : (type_of% @matching_pairing_inverse) ↔ arena.Law matchingActual := Iff.rfl

end MatchingInverse

namespace Flip
abbrev arena : Arena where
  signature := graphPerfectSignature.{u}
  Law r := ∀ {V : Type u} {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe),
    Even p.length ∧ (∃ N : G.Subgraph, r.readout () ⟨V, G⟩ N = true ∧
      (∀ x y, N.Adj x y ↔
        (M.Adj x y ∧ ¬ p.toSubgraph.Adj x y) ∨
        (p.toSubgraph.Adj x y ∧ ¬ M.Adj x y))) ∧
    ∃ N : (G.induce p.toSubgraph.vertsᶜ).Subgraph, N.IsPerfectMatching

theorem actual_law : arena.{u}.Law graphPerfectActual.{u} := by
  classical
  simpa only [arena, graphPerfectActual, realize, decide_eq_true_eq] using @alternating_cycle_flip.{u}
theorem bridge : (type_of% @alternating_cycle_flip.{u}) ↔ arena.{u}.Law graphPerfectActual.{u} := by
  classical
  simp only [arena, graphPerfectActual, realize, decide_eq_true_eq]

end Flip

namespace MatchingPairingAdj
abbrev arena : Arena where
  signature := finSignature
  Law r := ∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : {M : G.Subgraph // M.IsPerfectMatching}) (x y : V),
    r.readout () n ((matchingPairing label M).val (label x)) (label y) ↔ M.val.Adj x y

theorem actual_law : arena.{u}.Law finActual := @matchingPairing_adj.{u}
theorem bridge : (type_of% @matchingPairing_adj.{u}) ↔ arena.{u}.Law finActual := Iff.rfl

end MatchingPairingAdj

namespace CanonicalAdj
abbrev arena : Arena where
  signature := matchingAdjSignature.{u}
  Law r := ∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : {M : G.Subgraph // M.IsPerfectMatching}) (i : Fin n),
    r.readout () ⟨V, G, M⟩
      (label.symm (canonicalListing (matchingPairing label M) ⟨2 * i.val, by omega⟩))
      (label.symm (canonicalListing (matchingPairing label M) ⟨2 * i.val + 1, by omega⟩))

theorem actual_law : arena.{u}.Law matchingAdjActual.{u} := @canonical_adj.{u}
theorem bridge : (type_of% @canonical_adj.{u}) ↔ arena.{u}.Law matchingAdjActual.{u} := Iff.rfl

end CanonicalAdj

namespace Transport
abbrev arena : Arena where
  signature := unitSignature
  Law r := ∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} (label : V ≃ Fin (2 * n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon)
    (M : {M : G.Subgraph // M.IsPerfectMatching})
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (ha : p.toSubgraph.spanningCoe.IsAlternating M.val.spanningCoe),
    ∃ N : {N : G.Subgraph // N.IsPerfectMatching},
      (∀ x y, N.val.Adj x y ↔
        (M.val.Adj x y ∧ ¬p.toSubgraph.Adj x y) ∨
        (p.toSubgraph.Adj x y ∧ ¬M.val.Adj x y)) ∧
      r.readout () () (matchingTau label epsilon M * matchingTau label epsilon N)
        (-(p.darts.map (dartSign epsilon)).prod)

theorem actual_law : arena.{u}.Law unitActual := @alternating_cycle_transport.{u}
theorem bridge : (type_of% @alternating_cycle_transport.{u}) ↔ arena.{u}.Law unitActual := Iff.rfl

end Transport

namespace Uniformity
abbrev arena : Arena where
  signature := unitSignature
  Law r := ∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} (label : V ≃ Fin (2 * n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon) (ho : NiceOdd epsilon)
    (M N : {M : G.Subgraph // M.IsPerfectMatching}),
    r.readout () () (matchingTau label epsilon M) (matchingTau label epsilon N)

theorem actual_law : arena.{u}.Law unitActual := @niceOdd_matching_tau_eq.{u}
theorem bridge : (type_of% @niceOdd_matching_tau_eq.{u}) ↔ arena.{u}.Law unitActual := Iff.rfl

end Uniformity

def liftedPairing (n : ℕ) : (⊤ : SimpleGraph (ULift.{u} (Fin (2*n)))).Subgraph where
  verts := Set.univ
  Adj x y := (e n).val x.down = y.down
  adj_sub := by
    intro x y h
    rw [SimpleGraph.top_adj]
    intro he
    exact (e n).property.2 x.down (h.trans (congrArg ULift.down he).symm)
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun x y h => by rw [← h]; exact (e n).property.1 x.down⟩

theorem liftedPairing_perfect (n : ℕ) : (liftedPairing.{u} n).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  refine ⟨⟨(e n).val x.down⟩, rfl, ?_⟩
  intro y h
  change (e n).val x.down = y.down at h
  exact ULift.ext h.symm

theorem adjacencyDependence : ObservationalDependence adjacencySignature.{u} adjacencyActual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} (Fin (2*1)), liftedPairing 1⟩, ⟨0⟩, ⟨1⟩, ?_⟩
  intro he
  have hh := congrFun he (ULift.up (1 : Fin (2*1)))
  have ha : (liftedPairing.{u} 1).Adj (ULift.up 0) (ULift.up 1) := by change ((e 1).val (0 : Fin (2*1))) = 1; decide +kernel
  have hn : ¬ (liftedPairing.{u} 1).Adj (ULift.up 1) (ULift.up 1) := by change ¬ ((e 1).val (1 : Fin (2*1))) = 1; decide +kernel
  exact hn (hh.mp ha)

theorem mateAdjBad : ¬ MateAdj.arena.{u}.Law adjacencyRejected := by
  intro h
  exact h (liftedPairing 1) (liftedPairing_perfect 1) ⟨0⟩

theorem mateIffBad : ¬ MateIff.arena.{u}.Law adjacencyRejected := by
  intro h
  exact (h (liftedPairing 1) (liftedPairing_perfect 1) ⟨0⟩ _).mp rfl

theorem predicateDependence : ObservationalDependence predicateSignature.{u} predicateActual := by
  classical
  intro i
  refine ⟨ULift.{u} Bool, id, (fun _ => ⟨true⟩), ?_⟩
  intro he
  change decide (Function.Involutive id) =
    decide (Function.Involutive (fun _ : ULift.{u} Bool => ULift.up true)) at he
  have hi : decide (Function.Involutive (id : ULift.{u} Bool → ULift Bool)) = true := by
    simp only [decide_eq_true_eq]; exact fun _ => rfl
  have hf := of_decide_eq_true (he.symm.trans hi)
  have hh := hf ⟨false⟩
  cases hh

theorem mateInvolutiveBad : ¬ MateInvolutive.arena.{u}.Law predicateRejected := by
  intro h
  exact Bool.false_ne_true (h (liftedPairing 1) (liftedPairing_perfect 1))

theorem vertexNeDependence : ObservationalDependence vertexSignature.{u} vertexRejected := by
  intro i
  refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
  intro he
  have hh := congrFun he (ULift.up true)
  exact hh.mp (by intro h; cases h) rfl

theorem mateNeBad : ¬ MateNe.arena.{u}.Law vertexActual := by
  intro h
  exact matchingMate_ne _ (liftedPairing_perfect 1) (ULift.up 0) (h (liftedPairing 1) (liftedPairing_perfect 1) ⟨0⟩)

theorem perfectDependence : ObservationalDependence perfectSignature perfectActual := by
  classical
  intro i
  refine ⟨1, pairingGraph (e 1), ⊥, ?_⟩
  intro he
  have hb : (⊥ : (⊤ : SimpleGraph (Fin (2*1))).Subgraph).IsPerfectMatching :=
    of_decide_eq_true (he.symm.trans (by
      change decide (pairingGraph (e 1)).IsPerfectMatching = true
      simpa only [decide_eq_true_eq] using pairingGraph_perfect (e 1)))
  obtain ⟨y, hy, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hb 0
  exact hy

theorem pairingPerfectBad : ¬ PairingPerfect.arena.Law perfectRejected := by
  intro h
  exact Bool.false_ne_true (h (e 1))

def anotherPairing : P 2 := pairingOfListing (Equiv.swap (1 : Fin (2*2)) 2)

theorem pairings_differ : e 2 ≠ anotherPairing := by
  intro h
  have hh := congrArg (fun p : P 2 => p.val 0) h
  change (1 : Fin (2*2)) = 2 at hh
  exact (by decide : (1 : Fin (2*2)) ≠ 2) hh

theorem pairingDependence : ObservationalDependence pairingSignature pairingActual :=
  equalityDependence ⟨2, e 2, anotherPairing, pairings_differ⟩

theorem pairingInverseBad : ¬ PairingInverse.arena.Law pairingRejected := by
  intro h
  exact h (e 0) (pairing_matching_inverse (e 0))

theorem matchingDependence : ObservationalDependence matchingSignature matchingActual := by
  apply equalityDependence
  refine ⟨2, pairingToMatching (e 2), pairingToMatching anotherPairing, ?_⟩
  intro h
  apply pairings_differ
  have hh := congrArg (matchingToPairing 2) h
  simpa only [pairing_matching_inverse] using hh

theorem matchingInverseBad : ¬ MatchingInverse.arena.Law matchingRejected := by
  intro h
  exact h 0 (pairingToMatching (e 0)) (matching_pairing_inverse 0 _)


def fourCycle : (⊤ : SimpleGraph (ULift.{u} (Fin (2*2)))).Walk ⟨0⟩ ⟨0⟩ :=
  .cons (by decide) (.cons (by decide) (.cons (by decide)
    (.cons (by decide) .nil : (⊤ : SimpleGraph (ULift.{u} (Fin (2*2)))).Walk ⟨3⟩ ⟨0⟩) :
      (⊤ : SimpleGraph (ULift.{u} (Fin (2*2)))).Walk ⟨2⟩ ⟨0⟩) :
        (⊤ : SimpleGraph (ULift.{u} (Fin (2*2)))).Walk ⟨1⟩ ⟨0⟩)

theorem fourCycle_isCycle : fourCycle.IsCycle := by
  simp [fourCycle, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]

theorem fourCycle_alternating : fourCycle.toSubgraph.spanningCoe.IsAlternating
    (liftedPairing.{u} 2).spanningCoe := by
  change ∀ (v w w' : ULift.{u} (Fin (2*2))), w ≠ w' →
    fourCycle.toSubgraph.Adj v w → fourCycle.toSubgraph.Adj v w' →
      ((e 2).val v.down = w.down ↔ ¬(e 2).val v.down = w'.down)
  simp only [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges, fourCycle,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  simp only [ULift.forall, ULift.ext_iff]
  decide +kernel

def liftedLabel (n : ℕ) : ULift.{u} (Fin (2*n)) ≃ Fin (2*n) :=
  ⟨ULift.down, ULift.up, by intro x; cases x; rfl, fun _ => rfl⟩

theorem graphPerfectDependence : ObservationalDependence graphPerfectSignature.{u} graphPerfectActual := by
  classical
  intro i
  refine ⟨⟨ULift.{u} (Fin (2*1)), ⊤⟩, liftedPairing 1, ⊥, ?_⟩
  intro he
  have hb : (⊥ : (⊤ : SimpleGraph (ULift.{u} (Fin (2*1)))).Subgraph).IsPerfectMatching :=
    of_decide_eq_true (he.symm.trans (by
      change decide (liftedPairing 1).IsPerfectMatching = true
      simpa only [decide_eq_true_eq] using liftedPairing_perfect 1))
  obtain ⟨y, hy, _⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hb ⟨0⟩
  exact hy

theorem flipBad : ¬ Flip.arena.{u}.Law graphPerfectRejected := by
  intro h
  obtain ⟨_, ⟨N, hN, _⟩, _⟩ := h (liftedPairing_perfect 2) fourCycle_isCycle fourCycle_alternating
  exact Bool.false_ne_true hN

theorem matchingPairingAdjBad : ¬ MatchingPairingAdj.arena.{u}.Law finRejected := by
  intro h
  let M : {M : (⊤ : SimpleGraph (ULift.{u} (Fin (2*1)))).Subgraph //
      M.IsPerfectMatching} := ⟨liftedPairing 1, liftedPairing_perfect 1⟩
  exact ((h (liftedLabel 1) M ⟨0⟩ ⟨1⟩).mpr (by change (e 1).val 0 = 1; decide +kernel))
    ((matchingPairing_adj (liftedLabel 1) M ⟨0⟩ ⟨1⟩).mpr
      (by change (e 1).val 0 = 1; decide +kernel))

theorem matchingAdjDependence : ObservationalDependence matchingAdjSignature.{u} matchingAdjActual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin (2*1)), ⊤, ⟨liftedPairing 1, liftedPairing_perfect 1⟩⟩,
    ⟨0⟩, ⟨1⟩, ?_⟩
  intro he
  have hh := congrFun he (ULift.up (1 : Fin (2*1)))
  have ha : (liftedPairing.{u} 1).Adj (ULift.up 0) (ULift.up 1) := by
    change (e 1).val 0 = 1; decide +kernel
  have hn : ¬(liftedPairing.{u} 1).Adj (ULift.up 1) (ULift.up 1) := by
    change ¬(e 1).val 1 = 1; decide +kernel
  exact hn (hh.mp ha)

theorem canonicalAdjBad : ¬ CanonicalAdj.arena.{u}.Law matchingAdjRejected := by
  intro h
  exact h (liftedLabel 1) ⟨liftedPairing 1, liftedPairing_perfect 1⟩ 0

def emptyOrientation : (⊤ : SimpleGraph (ULift.{u} (Fin (2*0)))).Dart → ZMod 2 :=
  fun d => Fin.elim0 d.fst.down

theorem emptyReverses : Reverses emptyOrientation.{u} := fun d => Fin.elim0 d.fst.down
theorem emptyNiceOdd : NiceOdd emptyOrientation.{u} := fun x => Fin.elim0 x.down

theorem uniformityBad : ¬ Uniformity.arena.{u}.Law unitRejected := by
  intro h
  let M : {M : (⊤ : SimpleGraph (ULift.{u} (Fin (2*0)))).Subgraph //
      M.IsPerfectMatching} := ⟨liftedPairing 0, liftedPairing_perfect 0⟩
  exact h (liftedLabel 0) emptyReverses emptyNiceOdd M M rfl

def fourOrientation : (⊤ : SimpleGraph (ULift.{u} (Fin (2*2)))).Dart → ZMod 2 :=
  fun d => if d.fst.down < d.snd.down then 0 else 1

theorem fourReverses : Reverses fourOrientation.{u} := by
  intro d
  have hn : d.fst.down ≠ d.snd.down := by
    intro h
    have hd := d.adj
    change d.fst ≠ d.snd at hd
    exact hd (ULift.ext h)
  change (if d.snd.down < d.fst.down then (0 : ZMod 2) else 1) =
    1 + (if d.fst.down < d.snd.down then 0 else 1)
  rcases lt_or_gt_of_ne hn with h | h
  · simp [h, not_lt.mpr h.le]
  · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h.le)]
    decide +kernel

theorem transportBad : ¬ Transport.arena.{u}.Law unitRejected := by
  intro h
  let M : {M : (⊤ : SimpleGraph (ULift.{u} (Fin (2*2)))).Subgraph //
      M.IsPerfectMatching} := ⟨liftedPairing 2, liftedPairing_perfect 2⟩
  obtain ⟨N, hN, he⟩ := alternating_cycle_transport (liftedLabel 2) fourReverses M
    fourCycle_isCycle fourCycle_alternating
  obtain ⟨N', hN', hne⟩ := h (liftedLabel 2) fourReverses M fourCycle_isCycle fourCycle_alternating
  have heq : N = N' := by
    apply Subtype.ext
    ext x y
    · exact iff_of_true (N.property.2 x) (N'.property.2 x)
    · exact (hN x y).trans (hN' x y).symm
  subst N'
  exact hne he


end
end Reg.Support.PfaffianAlternatingCycle
