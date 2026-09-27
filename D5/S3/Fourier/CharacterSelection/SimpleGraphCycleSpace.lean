/- GID: D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simple cycles generate binary graph relations and determine all anchored lifts. -/

import D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Probability.UniformOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
namespace D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

open SimpleGraph
open MeasureTheory ProbabilityTheory
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

/-- Every closed walk is a mod-two linear combination of actual simple cycles. -/
theorem closed_walk_mod_two_mem_simple_cycle_span
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    (v : V) (p : G.Walk v v) :
    (fun e : G.edgeSet => (p.edges.count e.val : ZMod 2)) ∈
      Submodule.span (ZMod 2)
        {z : G.edgeSet → ZMod 2 | ∃ (w : V) (q : G.Walk w w),
          q.IsCycle ∧
          z = (fun e : G.edgeSet => if e.val ∈ q.edges then 1 else 0)} := by
  let S := Submodule.span (ZMod 2)
    {z : G.edgeSet → ZMod 2 | ∃ (w : V) (q : G.Walk w w),
      q.IsCycle ∧ z = (fun e : G.edgeSet => if e.val ∈ q.edges then 1 else 0)}
  let vec := fun {a b : V} (q : G.Walk a b) =>
    (fun e : G.edgeSet => (q.edges.count e.val : ZMod 2))
  have append_vec {a b c : V} (q : G.Walk a b) (r : G.Walk b c) :
      vec (q.append r) = vec q + vec r := by
    funext e
    simp [vec, Walk.edges_append, List.count_append]
  have cons_vec {a b c : V} (h : G.Adj a b) (q : G.Walk b c) :
      vec (Walk.cons h q) = vec h.toWalk + vec q := by
    funext e
    simp [vec, Walk.edges_cons, SimpleGraph.Adj.toWalk, List.count_cons, Nat.cast_add, add_comm]
  have erase {a b : V} (q : G.Walk a b) : vec q - vec q.bypass ∈ S := by
    induction q with
    | nil => simp [Walk.bypass]
    | @cons a b c h q ih =>
      by_cases hs : a ∈ q.bypass.support
      · let r := q.bypass.takeUntil a hs
        let t := q.bypass.dropUntil a hs
        have hr : r.IsPath := q.bypass_isPath.takeUntil hs
        have split : q.bypass = r.append t := (Walk.take_spec _ hs).symm
        have loop : vec (Walk.cons h r) ∈ S := by
          by_cases he : s(a, b) ∈ r.edges
          · have hr' : r = h.symm.toWalk := by
              have he' : s(b, a) ∈ r.edges := by simpa only [Sym2.eq_swap] using he
              exact hr.eq_adj_toWalk_of_mem_edges he'
            rw [hr']
            have hz : vec (Walk.cons h h.symm.toWalk) = 0 := by
              funext e
              simp [vec, SimpleGraph.Adj.toWalk, Walk.edges_cons, List.count_cons,
                Sym2.eq_swap, Nat.cast_add, ZModModule.add_self]
            rw [hz]
            exact S.zero_mem
          · have hc : (Walk.cons h r).IsCycle := (Walk.cons_isCycle_iff r h).mpr ⟨hr, he⟩
            apply Submodule.subset_span
            refine ⟨a, Walk.cons h r, hc, ?_⟩
            funext e
            change ((Walk.cons h r).edges.count e.val : ZMod 2) = _
            by_cases he : e.val ∈ (Walk.cons h r).edges
            · simp only [if_pos he, hc.isTrail.count_edges_eq_one he, Nat.cast_one]
            · simp only [if_neg he, List.count_eq_zero.mpr he, Nat.cast_zero]
        have hb : (Walk.cons h q).bypass = t := by
          simp only [Walk.bypass, dif_pos hs]
          rfl
        rw [hb]
        convert S.add_mem ih loop using 1
        rw [cons_vec h q, cons_vec h r, split, append_vec]
        abel
      · have hb : (Walk.cons h q).bypass = Walk.cons h q.bypass := by
          simp only [Walk.bypass, dif_neg hs]
        rw [hb, cons_vec h q, cons_vec h q.bypass]
        convert ih using 1; abel
  have hp : p.bypass = Walk.nil :=
    (Walk.isPath_iff_nil.mp p.bypass_isPath).eq_nil
  have result := erase p
  have vz : vec (Walk.nil : G.Walk v v) = 0 := by funext e; simp [vec]
  rw [hp, vz, sub_zero] at result
  exact result

#print axioms closed_walk_mod_two_mem_simple_cycle_span

/-- The symmetric sum of the two endpoint evaluation functionals. -/
noncomputable def endpointCharacters {V : Type u} (G : SimpleGraph V) :
    G.edgeSet → Module.Dual (ZMod 2) (V → ZMod 2) :=
  fun e => Sym2.lift ⟨(fun a b => LinearMap.proj a + LinearMap.proj b),
    fun _ _ => add_comm _ _⟩ e.val

/-- The vertex-to-unordered-edge differential over the binary field. -/
noncomputable def edgeDifferential {V : Type u} (G : SimpleGraph V) :
    (V → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2) :=
  LinearMap.pi (endpointCharacters G)

/-- The span of indicators of actual simple cycles, independently of endpoint relations. -/
noncomputable def simpleCycleSpace {V : Type u} [DecidableEq V] (G : SimpleGraph V) :
    Submodule (ZMod 2) (G.edgeSet → ZMod 2) :=
  Submodule.span (ZMod 2)
    {z | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
      z = fun e : G.edgeSet => if e.val ∈ p.edges then 1 else 0}

/-- The label sum over the edge list, retaining every traversal with its multiplicity. -/
noncomputable def walkParity {V : Type u} {G : SimpleGraph V}
    (y : G.edgeSet → ZMod 2) {a b : V} (p : G.Walk a b) : ZMod 2 := by
  classical
  exact (p.edges.map (fun e => if h : e ∈ G.edgeSet then y ⟨e, h⟩ else 0)).sum

/-- Binary graph relations, all component anchors, every fundamental-cycle basis,
and the probability under independent fair edge labels. -/
theorem finite_graph_cycle_space
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    [MeasurableSpace (ZMod 2)] [MeasurableSingletonClass (ZMod 2)] :
    (simpleCycleSpace G = characterRelationSpace (ZMod 2) (endpointCharacters G) ∧
    Fintype.card G.ConnectedComponent ≤ Fintype.card V ∧
    Nat.card (Set.range (edgeDifferential G)) =
      2 ^ (Fintype.card V - Fintype.card G.ConnectedComponent) ∧
    (∀ y : G.edgeSet → ZMod 2,
      ((∃ x, edgeDifferential G x = y) ↔
        ∀ (v : V) (p : G.Walk v v), p.IsCycle → walkParity y p = 0) ∧
      (∀ (_hy : ∃ x, edgeDifferential G x = y),
        Nat.card {x // edgeDifferential G x = y} = 2 ^ Fintype.card G.ConnectedComponent ∧
        ∀ (o : (K : G.ConnectedComponent) → K),
          Function.Bijective (fun x : {x // edgeDifferential G x = y} =>
            fun K => x.val (o K))))) ∧
    (∃ T ≤ G, T.IsAcyclic ∧ T.Reachable = G.Reachable) ∧
    ∀ (T : SimpleGraph V) (hle : T ≤ G), T.IsAcyclic →
      T.Reachable = G.Reachable →
    let D := {e : G.edgeSet // e.val ∉ T.edgeSet}
    ∃ (cycles : D → Σ v, G.Walk v v),
      (∀ d, (cycles d).2.IsCycle) ∧
      (∀ d, ∃ (a b : V) (h : G.Adj a b) (p : T.Path b a),
        s(a,b) = d.val.val ∧
        cycles d = ⟨a, Walk.cons h (p.val.mapLe hle)⟩ ∧
        ∀ q : T.Path b a, q = p) ∧
      (∀ d e : D, (if e.val.val ∈ (cycles d).2.edges then (1 : ZMod 2) else 0) =
        if e = d then 1 else 0) ∧
      ∃ basis : Module.Basis D (ZMod 2) (simpleCycleSpace G),
        (∀ d e, (basis d).val e = if e.val ∈ (cycles d).2.edges then 1 else 0) ∧
        Nat.card T.edgeSet + Fintype.card G.ConnectedComponent = Fintype.card V ∧
        Fintype.card V ≤ Fintype.card G.edgeSet + Fintype.card G.ConnectedComponent ∧
        Nat.card D = Fintype.card G.edgeSet - Nat.card T.edgeSet ∧
        Nat.card D = Fintype.card G.edgeSet + Fintype.card G.ConnectedComponent - Fintype.card V ∧
        (Nat.card D : ℤ) = (Fintype.card G.edgeSet : ℤ) -
          (Fintype.card V : ℤ) + (Fintype.card G.ConnectedComponent : ℤ) ∧
        Module.finrank (ZMod 2) (simpleCycleSpace G) = Nat.card D ∧
        (∀ b : ZMod 2, (uniformOn (Set.univ : Set (ZMod 2))).real {b} = (1 : ℝ) / 2) ∧
        (Measure.pi (fun _ : G.edgeSet => uniformOn (Set.univ : Set (ZMod 2)))) =
          uniformOn (Set.univ : Set (G.edgeSet → ZMod 2)) ∧
        (Measure.pi (fun _ : G.edgeSet => uniformOn (Set.univ : Set (ZMod 2)))).real
          (Set.range (edgeDifferential G)) = (2 : ℝ) ^ (-(Nat.card D : ℤ)) ∧
        (2 : ℝ) ^ (-(Nat.card D : ℤ)) = ((2 : ℝ) ^ Nat.card D)⁻¹ := by
  classical
  have transport
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent] :
    simpleCycleSpace G = characterRelationSpace (ZMod 2) (endpointCharacters G) ∧
    Fintype.card G.ConnectedComponent ≤ Fintype.card V ∧
    Nat.card (Set.range (edgeDifferential G)) =
      2 ^ (Fintype.card V - Fintype.card G.ConnectedComponent) ∧
    (∀ y : G.edgeSet → ZMod 2,
      ((∃ x, edgeDifferential G x = y) ↔
        ∀ (v : V) (p : G.Walk v v), p.IsCycle → walkParity y p = 0) ∧
      (∀ (_hy : ∃ x, edgeDifferential G x = y),
        Nat.card {x // edgeDifferential G x = y} = 2 ^ Fintype.card G.ConnectedComponent ∧
        ∀ (o : (K : G.ConnectedComponent) → K),
          Function.Bijective (fun x : {x // edgeDifferential G x = y} =>
            fun K => x.val (o K)))) := by
    classical
    let vec := fun {a b : V} (p : G.Walk a b) =>
      (fun e : G.edgeSet => (p.edges.count e.val : ZMod 2))
    let pair : (G.edgeSet → ZMod 2) →ₗ[ZMod 2]
        Module.Dual (ZMod 2) (G.edgeSet → ZMod 2) :=
      standardCoordinatePairing (ZMod 2) G.edgeSet
    have parity_cons {a b c : V} (y : G.edgeSet → ZMod 2)
        (h : G.Adj a b) (p : G.Walk b c) :
        walkParity y (Walk.cons h p) = y ⟨s(a,b), G.mem_edgeSet.mpr h⟩ + walkParity y p := by
      simp [walkParity, Walk.edges_cons, G.mem_edgeSet.mpr h]
    have parity_append {a b c : V} (y : G.edgeSet → ZMod 2)
        (p : G.Walk a b) (q : G.Walk b c) :
        walkParity y (p.append q) = walkParity y p + walkParity y q := by
      simp [walkParity, Walk.edges_append]
    have parity_reverse {a b : V} (y : G.edgeSet → ZMod 2) (p : G.Walk a b) :
        walkParity y p.reverse = walkParity y p := by
      simp [walkParity, Walk.edges_reverse]
    have pairing {a b : V} (y : G.edgeSet → ZMod 2) (p : G.Walk a b) :
        pair (vec p) y = walkParity y p := by
      induction p with
      | nil => simp [vec, pair, standardCoordinatePairing, dotProductBilin,
          dotProduct, walkParity]
      | @cons a b c h p ih =>
        rw [parity_cons]
        have hv : vec (Walk.cons h p) =
            (fun e => if e = ⟨s(a,b), G.mem_edgeSet.mpr h⟩ then 1 else 0) + vec p := by
          funext e
          change ((Walk.cons h p).edges.count e.val : ZMod 2) = _
          simp only [Walk.edges_cons, List.count_cons, Nat.cast_add, Nat.cast_ite,
            Nat.cast_one, Nat.cast_zero, Pi.add_apply]
          by_cases he : s(a,b) = e.val
          · have he' : e = ⟨s(a,b), G.mem_edgeSet.mpr h⟩ := Subtype.ext he.symm
            simp only [he', beq_self_eq_true, if_true, vec, add_comm]
          · have he' : e ≠ ⟨s(a,b), G.mem_edgeSet.mpr h⟩ :=
              fun hh => he (congrArg Subtype.val hh).symm
            simp only [beq_iff_eq, he, if_false, he', vec, add_zero, zero_add]
        rw [hv, map_add, LinearMap.add_apply, ih]
        congr 1
        simp [pair, standardCoordinatePairing, dotProductBilin, dotProduct]
    have cycle_vec {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
        vec p = (fun e => if e.val ∈ p.edges then 1 else 0) := by
      funext e
      change (p.edges.count e.val : ZMod 2) = _
      by_cases he : e.val ∈ p.edges
      · simp only [if_pos he, hp.isTrail.count_edges_eq_one he, Nat.cast_one]
      · simp only [if_neg he, List.count_eq_zero.mpr he, Nat.cast_zero]
    have orth_iff (y : G.edgeSet → ZMod 2) :
        y ∈ characterOrthogonalComplement (ZMod 2) (simpleCycleSpace G) ↔
        ∀ (v : V) (p : G.Walk v v), p.IsCycle → walkParity y p = 0 := by
      constructor
      · intro hy v p hp
        rw [← pairing y p]
        exact hy _ (Submodule.subset_span ⟨v, p, hp, cycle_vec p hp⟩)
      · intro hy z hz
        refine Submodule.span_induction (fun z hz => ?_) ?_ ?_ ?_ hz
        · obtain ⟨v, p, hp, rfl⟩ := hz
          rw [← cycle_vec p hp, pairing]
          exact hy v p hp
        · simp
        · intro x z hx hz
          simp_all
        · intro a x hx
          simp_all
    have zero_loops (y : G.edgeSet → ZMod 2)
        (hy : ∀ (v : V) (p : G.Walk v v), p.IsCycle → walkParity y p = 0)
        (v : V) (p : G.Walk v v) : walkParity y p = 0 := by
      rw [← pairing y p]
      exact (orth_iff y).mpr hy _ (closed_walk_mod_two_mem_simple_cycle_span G v p)
    have telescopes (x : V → ZMod 2) {a b : V} (p : G.Walk a b) :
        walkParity (edgeDifferential G x) p = x a + x b := by
      induction p with
      | nil => simp [walkParity, ZModModule.add_self]
      | @cons a b c h p ih =>
        rw [parity_cons, ih]
        change (x a + x b) + (x b + x c) = _
        simp only [add_assoc, ← add_assoc (x b) (x b), ZModModule.add_self, zero_add]
    have realize (y : G.edgeSet → ZMod 2)
        (hy : ∀ (v : V) (p : G.Walk v v), p.IsCycle → walkParity y p = 0) :
        ∃ x, edgeDifferential G x = y := by
      let o : (K : G.ConnectedComponent) → K :=
        fun K => ⟨K.exists_rep.choose, K.exists_rep.choose_spec⟩
      let root : V → V := fun v => o (G.connectedComponentMk v)
      have reach (v : V) : G.Reachable (root v) v :=
        ConnectedComponent.exact (o (G.connectedComponentMk v)).property
      obtain ⟨T, hleT, _hacycT, hreachT⟩ := G.exists_isAcyclic_reachable_eq_le
      have reachT (v : V) : T.Reachable (root v) v := by
        rw [hreachT]
        exact reach v
      let paths : (v : V) → G.Walk (root v) v :=
        fun v => ((reachT v).some.toPath.val).mapLe hleT
      let x : V → ZMod 2 := fun v => walkParity y (paths v)
      refine ⟨x, ?_⟩
      funext e
      obtain ⟨e, he⟩ := e
      induction e using Sym2.inductionOn with
      | hf a b =>
        have hab : G.Adj a b := G.mem_edgeSet.mp he
        have hr : root a = root b :=
          congrArg (fun K => (o K).val) (ConnectedComponent.connectedComponentMk_eq_of_adj hab)
        let q : G.Walk (root a) b := (paths a).append hab.toWalk
        let r : G.Walk (root a) b := (paths b).copy hr.symm rfl
        have hz := zero_loops y hy (root a) (q.append r.reverse)
        have qr : walkParity y q = x a + y ⟨s(a,b), he⟩ := by
          simp [q, SimpleGraph.Adj.toWalk, walkParity, x, hab]
        have rr : walkParity y r = x b := by simp [r, walkParity, x]
        rw [parity_append, parity_reverse, qr, rr] at hz
        change x a + x b = y ⟨s(a,b), he⟩
        generalize x a = xa, x b = xb, y ⟨s(a,b), he⟩ = ye at hz ⊢
        linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) hz
    have criterion (y : G.edgeSet → ZMod 2) :
        (∃ x, edgeDifferential G x = y) ↔
        ∀ (v : V) (p : G.Walk v v), p.IsCycle → walkParity y p = 0 := by
      constructor
      · rintro ⟨x, rfl⟩ v p hp
        simpa [ZModModule.add_self] using telescopes x p
      · exact realize y
    have orth_eq : characterOrthogonalComplement (ZMod 2) (simpleCycleSpace G) =
        characterCode (ZMod 2) (endpointCharacters G) := by
      ext y
      exact (orth_iff y).trans (criterion y).symm
    have space_eq : simpleCycleSpace G =
        characterRelationSpace (ZMod 2) (endpointCharacters G) := by
      have hh := congrArg (characterOrthogonalComplement (ZMod 2)) orth_eq
      rw [character_code_eq_relation_space_orthogonal,
        standard_orthogonal_complement_involutive,
        standard_orthogonal_complement_involutive] at hh
      exact hh
    have anchors (y : G.edgeSet → ZMod 2) (hy : ∃ x, edgeDifferential G x = y)
        (o : (K : G.ConnectedComponent) → K) :
        Function.Bijective (fun x : {x // edgeDifferential G x = y} =>
          fun K => x.val (o K)) := by
      constructor
      · intro x x' hanchor
        apply Subtype.ext
        funext v
        let K := G.connectedComponentMk v
        have hreach : G.Reachable (o K).val v := ConnectedComponent.exact (o K).property
        let p := hreach.some
        have ht := congrArg (fun z => walkParity z p) (x.property.trans x'.property.symm)
        rw [telescopes, telescopes] at ht
        have ha : x.val (o K) = x'.val (o K) := congrFun hanchor K
        rw [ha] at ht
        exact add_left_cancel ht
      · intro a
        obtain ⟨x, hx⟩ := hy
        let z : V → ZMod 2 := fun v =>
          x v + x (o (G.connectedComponentMk v)) + a (G.connectedComponentMk v)
        have hz : edgeDifferential G z = y := by
          rw [← hx]
          funext e
          obtain ⟨e, he⟩ := e
          induction e using Sym2.inductionOn with
          | hf u v =>
            have huv : G.Adj u v := G.mem_edgeSet.mp he
            change z u + z v = x u + x v
            dsimp [z]
            rw [ConnectedComponent.connectedComponentMk_eq_of_adj huv]
            generalize x u = xu, x v = xv, x (o (G.connectedComponentMk v)) = xr,
              a (G.connectedComponentMk v) = av
            ring_nf
            simp [show (2 : ZMod 2) = 0 by decide]
        refine ⟨⟨z, hz⟩, ?_⟩
        funext K
        change z (o K) = a K
        dsimp [z]
        rw [(o K).property]
        simp [ZModModule.add_self]
    have hc : Fintype.card G.ConnectedComponent ≤ Fintype.card V :=
      Fintype.card_le_of_surjective G.connectedComponentMk (fun K => K.exists_rep)
    have fibers (y : G.edgeSet → ZMod 2) (hy : ∃ x, edgeDifferential G x = y) :
        Fintype.card {x // edgeDifferential G x = y} = 2 ^ Fintype.card G.ConnectedComponent := by
      let o : (K : G.ConnectedComponent) → K :=
        fun K => ⟨K.exists_rep.choose, K.exists_rep.choose_spec⟩
      have hh := Fintype.card_congr (Equiv.ofBijective _ (anchors y hy o))
      simpa only [Fintype.card_fun, ZMod.card] using hh
    let f : (V → ZMod 2) → Set.range (edgeDifferential G) :=
      fun x => ⟨edgeDifferential G x, ⟨x, rfl⟩⟩
    have fiber_f (y : Set.range (edgeDifferential G)) :
        Fintype.card {x // f x = y} = 2 ^ Fintype.card G.ConnectedComponent := by
      let e : {x // f x = y} ≃ {x // edgeDifferential G x = y.val} :=
        Equiv.subtypeEquivRight (fun x => Subtype.ext_iff)
      exact (Fintype.card_congr e).trans (fibers y.val y.property)
    have total : Fintype.card (Set.range (edgeDifferential G)) *
        2 ^ Fintype.card G.ConnectedComponent = 2 ^ Fintype.card V := by
      have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
      simpa only [Fintype.card_sigma, fiber_f, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, Fintype.card_fun, ZMod.card] using hh
    have image : Nat.card (Set.range (edgeDifferential G)) =
        2 ^ (Fintype.card V - Fintype.card G.ConnectedComponent) := by
      rw [Nat.card_eq_fintype_card]
      apply Nat.eq_of_mul_eq_mul_right (pow_pos (by decide : 0 < (2 : ℕ)) _)
      rw [total, ← pow_add, Nat.sub_add_cancel hc]
    exact ⟨space_eq, hc, image, fun y => ⟨criterion y, fun hy =>
      ⟨by simpa only [Nat.card_eq_fintype_card] using fibers y hy, anchors y hy⟩⟩⟩
  -- The graph statements now specialize the transport construction.
  refine ⟨transport G, G.exists_isAcyclic_reachable_eq_le, ?_⟩
  intro T hle hacyc hreach
  let : Fintype T.edgeSet := Fintype.ofFinite _
  let : Fintype T.ConnectedComponent := Fintype.ofFinite _
  have forest_card : Fintype.card T.edgeSet + Fintype.card G.ConnectedComponent =
      Fintype.card V := by
    let edgeMap : (Σ K : T.ConnectedComponent, K.toSimpleGraph.edgeSet) → T.edgeSet :=
      fun p => p.1.toSimpleGraph_hom.mapEdgeSet p.2
    have injective : Function.Injective edgeMap := by
      rintro ⟨K,e⟩ ⟨L,f⟩ h
      have hm : ((e.val.out.1 : K) : V) ∈ Sym2.map (fun v : L => v.val) f.val := by
        have he : ((e.val.out.1 : K) : V) ∈ Sym2.map (fun v : K => v.val) e.val :=
          Sym2.mem_map.mpr ⟨_, Sym2.out_fst_mem _, rfl⟩
        have hv := congrArg Subtype.val h
        change Sym2.map (fun v : K => v.val) e.val =
          Sym2.map (fun v : L => v.val) f.val at hv
        exact hv ▸ he
      obtain ⟨w, hw, hwv⟩ := Sym2.mem_map.mp hm
      have hKL : K = L := by
        have hk := (e.val.out.1).property
        have hl := w.property
        change T.connectedComponentMk (e.val.out.1).val = K at hk
        change T.connectedComponentMk w.val = L at hl
        rw [hwv] at hl
        exact hk.symm.trans hl
      subst L
      have hef : e = f :=
        SimpleGraph.Hom.mapEdgeSet.injective K.toSimpleGraph_hom Subtype.val_injective h
      subst f
      rfl
    have surjective : Function.Surjective edgeMap := by
      rintro ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | hf a b =>
        let K := T.connectedComponentMk a
        have ha : a ∈ K := rfl
        have hb : b ∈ K :=
          ConnectedComponent.connectedComponentMk_eq_of_adj (T.mem_edgeSet.mp he).symm
        let a' : K := ⟨a,ha⟩
        let b' : K := ⟨b,hb⟩
        have he' : s(a',b') ∈ K.toSimpleGraph.edgeSet := T.mem_edgeSet.mp he
        refine ⟨⟨K,⟨s(a',b'),he'⟩⟩, ?_⟩
        apply Subtype.ext
        rfl
    let : (K : T.ConnectedComponent) → Fintype K := fun _ => Fintype.ofFinite _
    let : (K : T.ConnectedComponent) → Fintype K.toSimpleGraph.edgeSet :=
      fun _ => Fintype.ofFinite _
    have edgeCount : (∑ K : T.ConnectedComponent, Fintype.card K.toSimpleGraph.edgeSet) =
        Fintype.card T.edgeSet := by
      simpa only [Fintype.card_sigma] using
        Fintype.card_congr (Equiv.ofBijective edgeMap ⟨injective,surjective⟩)
    have vertexCount : (∑ K : T.ConnectedComponent, Fintype.card K) = Fintype.card V := by
      have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv T.connectedComponentMk)
      rw [Fintype.card_sigma] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro K _
      exact Fintype.card_congr (Equiv.refl _)
    have components : Fintype.card T.ConnectedComponent = Fintype.card G.ConnectedComponent := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      change Nat.card (Quot T.Reachable) = Nat.card (Quot G.Reachable)
      rw [hreach]
    have trees (K : T.ConnectedComponent) :
        Fintype.card K.toSimpleGraph.edgeSet + 1 = Fintype.card K := by
      simpa only [edgeFinset_card] using (hacyc.isTree_connectedComponent K).card_edgeFinset
    have totals := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun K _ => trees K)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one, edgeCount, vertexCount, components] using totals
  let D := {e : G.edgeSet // e.val ∉ T.edgeSet}
  have build (d : D) : ∃ c : Σ v, G.Walk v v,
      c.2.IsCycle ∧
      (∃ (a b : V) (h : G.Adj a b) (p : T.Path b a),
        s(a,b) = d.val.val ∧ c = ⟨a, Walk.cons h (p.val.mapLe hle)⟩ ∧
        ∀ q : T.Path b a, q = p) ∧
      ∀ e : D, (if e.val.val ∈ c.2.edges then (1 : ZMod 2) else 0) =
        if e = d then 1 else 0 := by
    obtain ⟨⟨d, hd⟩, hn⟩ := d
    induction d using Sym2.inductionOn with
    | hf a b =>
      have hab : G.Adj a b := G.mem_edgeSet.mp hd
      have hr : T.Reachable b a := by rw [hreach]; exact hab.symm.reachable
      let p : T.Path b a := hr.some.toPath
      let c : G.Walk a a := Walk.cons hab (p.val.mapLe hle)
      have hnpath : s(a,b) ∉ (p.val.mapLe hle).edges := by
        rw [Walk.edges_mapLe_eq_edges]
        exact fun hm => hn (p.val.edges_subset_edgeSet hm)
      have hc : c.IsCycle := (Walk.cons_isCycle_iff _ _).mpr ⟨p.property.mapLe hle, hnpath⟩
      refine ⟨⟨a,c⟩, hc, ⟨a,b,hab,p,rfl,rfl,fun q => (hacyc.subsingleton_path b a).elim q p⟩, ?_⟩
      intro e
      have hnp : e.val.val ∉ p.val.edges := fun hm => e.property (p.val.edges_subset_edgeSet hm)
      have heq : e.val.val = s(a,b) ↔ e = ⟨⟨s(a,b),hd⟩,hn⟩ := by
        constructor
        · intro hh; exact Subtype.ext (Subtype.ext hh)
        · intro hh; exact congrArg (fun e : D => e.val.val) hh
      simp only [c, Walk.edges_cons, Walk.edges_mapLe_eq_edges, List.mem_cons, hnp,
        or_false, heq]
  choose cycles hcycles using build
  let cv : D → simpleCycleSpace G := fun d =>
    ⟨(fun e => if e.val ∈ (cycles d).2.edges then 1 else 0),
      Submodule.subset_span ⟨(cycles d).1, (cycles d).2, (hcycles d).1, rfl⟩⟩
  let res : simpleCycleSpace G →ₗ[ZMod 2] (D → ZMod 2) :=
    { toFun := fun z d => z.val d.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have unit (d : D) : res (cv d) = fun e => if e = d then 1 else 0 := by
    funext e
    exact (hcycles d).2.2 e
  have liftT (y : T.edgeSet → ZMod 2) : ∃ x, edgeDifferential T x = y := by
    apply ((transport T).2.2.2 y).1.mpr
    intro v p hp
    exact False.elim (hacyc p hp)
  have kerzero (z : simpleCycleSpace G) (hz : res z = 0) : z = 0 := by
    apply Subtype.ext
    funext e
    change z.val e = 0
    by_cases he : e.val ∈ T.edgeSet
    · let y : T.edgeSet → ZMod 2 := fun f =>
        if (⟨f.val, edgeSet_mono hle f.property⟩ : G.edgeSet) = e then 1 else 0
      obtain ⟨x, hx⟩ := liftT y
      have horth : edgeDifferential G x ∈
          characterOrthogonalComplement (ZMod 2) (simpleCycleSpace G) := by
        rw [(transport G).1,
          ← character_code_eq_relation_space_orthogonal]
        exact ⟨x, rfl⟩
      have hh := horth z.val z.property
      change ∑ f : G.edgeSet, z.val f * edgeDifferential G x f = 0 at hh
      have sums : (∑ f : G.edgeSet, z.val f * edgeDifferential G x f) = z.val e := by
        calc
          _ = ∑ f : G.edgeSet, z.val f * (if f = e then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro f hf
            by_cases htf : f.val ∈ T.edgeSet
            · have hval := congrFun hx ⟨f.val, htf⟩
              change edgeDifferential G x f = (if f = e then 1 else 0) at hval
              rw [hval]
            · have hzv : z.val f = 0 := congrFun hz ⟨f, htf⟩
              rw [hzv]
              simp
          _ = _ := by simp
      rwa [sums] at hh
    · exact congrFun hz ⟨e, he⟩
  have inj : Function.Injective res := by
    intro z w h
    apply sub_eq_zero.mp
    apply kerzero
    simp only [map_sub, h, sub_self]
  have lin : LinearIndependent (ZMod 2) cv := by
    apply LinearIndependent.of_comp res
    convert (Pi.basisFun (ZMod 2) D).linearIndependent using 1
    funext d e
    simp [unit, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have spans : ⊤ ≤ Submodule.span (ZMod 2) (Set.range cv) := by
    intro z hz
    have rep : z = ∑ d : D, (res z d) • cv d := by
      apply inj
      ext e
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, unit,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      exact (Fintype.sum_ite_eq e (fun d => res z d)).symm
    rw [rep]
    exact Submodule.sum_mem _ (fun d _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨d,rfl⟩))
  refine ⟨cycles, fun d => (hcycles d).1, fun d => (hcycles d).2.1,
    fun d e => (hcycles d).2.2 e, Module.Basis.mk lin spans, ?_⟩
  refine ⟨?_, ?_⟩
  · intro d e
    simp [Module.Basis.mk_apply, cv]
  let ef : {e : G.edgeSet // e.val ∈ T.edgeSet} ≃ T.edgeSet :=
    { toFun := fun e => ⟨e.val.val, e.property⟩
      invFun := fun e => ⟨⟨e.val, edgeSet_mono hle e.property⟩,e.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have et : Fintype.card {e : G.edgeSet // e.val ∈ T.edgeSet} = Fintype.card T.edgeSet :=
    Fintype.card_congr ef
  have tm : Fintype.card T.edgeSet ≤ Fintype.card G.edgeSet := by
    rw [← et]
    exact Fintype.card_subtype_le _
  have dc : Fintype.card D = Fintype.card G.edgeSet - Fintype.card T.edgeSet := by
    rw [Fintype.card_subtype_compl, et]
  have nd : Nat.card D = Fintype.card D := Nat.card_eq_fintype_card
  have nt : Nat.card T.edgeSet = Fintype.card T.edgeSet := Nat.card_eq_fintype_card
  refine ⟨by simpa only [nt] using forest_card, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Nat.card D = Fintype.card G.edgeSet - Nat.card T.edgeSet
    omega
  · change Nat.card D = Fintype.card G.edgeSet + Fintype.card G.ConnectedComponent - Fintype.card V
    omega
  · change (Nat.card D : ℤ) = (Fintype.card G.edgeSet : ℤ) -
      (Fintype.card V : ℤ) + (Fintype.card G.ConnectedComponent : ℤ)
    omega
  · change Module.finrank (ZMod 2) (simpleCycleSpace G) = Nat.card D
    rw [nd]
    exact Module.finrank_eq_card_basis (Module.Basis.mk lin spans)
  · intro b
    simp [Measure.real, uniformOn_univ, ZMod.card]
  · simpa only [Set.pi_univ] using
      (uniformOn_pi (f := fun _ : G.edgeSet => (Set.univ : Set (ZMod 2)))).symm
  · change (Measure.pi (fun _ : G.edgeSet => uniformOn (Set.univ : Set (ZMod 2)))).real
        (Set.range (edgeDifferential G)) = (2 : ℝ) ^ (-(Nat.card D : ℤ))
    have hm : Fintype.card G.edgeSet =
        (Fintype.card V - Fintype.card G.ConnectedComponent) + Nat.card D := by omega
    have joint : Measure.pi (fun _ : G.edgeSet => uniformOn (Set.univ : Set (ZMod 2))) =
        uniformOn (Set.univ : Set (G.edgeSet → ZMod 2)) := by
      simpa only [Set.pi_univ] using
        (uniformOn_pi (f := fun _ : G.edgeSet => (Set.univ : Set (ZMod 2)))).symm
    rw [joint]
    have counts := (transport G).2.2.1
    have hc : Fintype.card (Set.range (edgeDifferential G)) =
        2 ^ (Fintype.card V - Fintype.card G.ConnectedComponent) := by
      simpa only [Nat.card_eq_fintype_card] using counts
    rw [Measure.real, uniformOn_univ, Measure.count_apply (Set.toFinite _).measurableSet]
    suffices (2 : ℝ) ^ (Fintype.card V - Fintype.card G.ConnectedComponent) /
        2 ^ G.edgeSet.ncard = (2 ^ Nat.card D)⁻¹ by
      simpa [Set.encard, ENat.card_eq_coe_fintype_card, ZMod.card, hc,
        ENNReal.toReal_div] using this
    have he : G.edgeSet.ncard = Fintype.card G.edgeSet := by
      change Nat.card G.edgeSet = _
      exact Nat.card_eq_fintype_card
    rw [he, hm, pow_add]
    field_simp
  · simp only [zpow_neg, zpow_natCast]


#print axioms finite_graph_cycle_space

end D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
