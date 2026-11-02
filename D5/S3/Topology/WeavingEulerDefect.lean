/- GID: D5/S3/Topology/WeavingEulerDefect
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingEulerDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite]
   utility: none
   digest: Monotone Euler defect saturates the actual mixed-state circle identity. -/

import D5.S3.Topology.ColoredMatchingSwitchConsumer
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Interval

/-! The spanning rank includes every isolated uniform circle. A single-edge
quotient classifier proves the rank increments, and monotone Euler defect
with equal empty and full endpoints gives the arbitrary-state circle count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.WeavingEulerDefect
noncomputable section
attribute [local instance] Classical.propDecidable

open D5.S3.Topology.WeavingDiagramPorts
open D5.S3.Topology.WeavingMixedComponents

/- The one-edge quotient proof is private and is consumed below on the
literal reference graph. Its carrier is the full vertex type throughout. -/

private def collapse {A : Type*} (a b x : A) : A := if x = b then a else x

private theorem collapse_same {A : Type*} (a x : A) : collapse a a x = x := by
  by_cases h : x = a <;> simp [collapse, h]

private theorem collapse_ends {A : Type*} (a b : A) :
    collapse a b a = collapse a b b := by
  by_cases h : a = b <;> simp [collapse, h]

private theorem collapse_eq_iff {A : Type*} (a b x y : A) :
    collapse a b x = collapse a b y ↔
      x = y ∨ (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
  by_cases hx : x = b <;> by_cases hy : y = b <;>
    simp_all [collapse] <;> aesop

/-- A classifier for the actual quotient after one edge is added. -/
private theorem sup_edge_reachable_classifier {V : Type*} (G : SimpleGraph V)
    (a b x y : V) :
    (G ⊔ SimpleGraph.edge a b).Reachable x y ↔
      collapse (G.connectedComponentMk a) (G.connectedComponentMk b)
          (G.connectedComponentMk x) =
        collapse (G.connectedComponentMk a) (G.connectedComponentMk b)
          (G.connectedComponentMk y) := by
  let H := G ⊔ SimpleGraph.edge a b
  let f := fun u => collapse (G.connectedComponentMk a)
    (G.connectedComponentMk b) (G.connectedComponentMk u)
  have hstep {u v : V} (h : H.Adj u v) : f u = f v := by
    rcases h with h | h
    · exact congrArg (collapse (G.connectedComponentMk a) (G.connectedComponentMk b))
        (SimpleGraph.ConnectedComponent.sound h.reachable)
    · rcases (SimpleGraph.edge_adj a b u v).mp h with ⟨h, _⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact collapse_ends _ _
      · exact (collapse_ends _ _).symm
  have hab : H.Reachable a b := by
    by_cases h : a = b
    · subst b; exact .rfl
    · exact (show H.Adj a b from Or.inr
        ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, h⟩)).reachable
  have to_a (u : V)
      (hu : G.connectedComponentMk u = G.connectedComponentMk a ∨
        G.connectedComponentMk u = G.connectedComponentMk b) : H.Reachable u a := by
    rcases hu with hu | hu
    · exact (SimpleGraph.ConnectedComponent.exact hu).mono le_sup_left
    · exact ((SimpleGraph.ConnectedComponent.exact hu).mono le_sup_left).trans hab.symm
  constructor
  · intro h
    have hr := (SimpleGraph.reachable_iff_reflTransGen (G := H) x y).mp h
    clear h
    induction hr with
    | refl => rfl
    | tail _ huv ih => exact ih.trans (hstep huv)
  · intro h
    rcases (collapse_eq_iff _ _ _ _).mp h with h | ⟨hx, hy⟩
    · exact (SimpleGraph.ConnectedComponent.exact h).mono le_sup_left
    · exact (to_a x hx).trans (to_a y hy).symm

/-- Equal old endpoint components leave the quotient unchanged; distinct
ones remove exactly one class. Components disjoint from the edge survive. -/
private theorem sup_edge_component_card {V : Type*} [Finite V]
    (G : SimpleGraph V) (a b : V) :
    (G.connectedComponentMk a = G.connectedComponentMk b →
      Nat.card (G ⊔ SimpleGraph.edge a b).ConnectedComponent =
        Nat.card G.ConnectedComponent) ∧
    (G.connectedComponentMk a ≠ G.connectedComponentMk b →
      Nat.card (G ⊔ SimpleGraph.edge a b).ConnectedComponent + 1 =
        Nat.card G.ConnectedComponent) := by
  let H := G ⊔ SimpleGraph.edge a b
  let ca := G.connectedComponentMk a
  let cb := G.connectedComponentMk b
  have hker := sup_edge_reachable_classifier G a b
  constructor
  · intro heq
    have hold {x y : V} (h : H.Reachable x y) :
        G.connectedComponentMk x = G.connectedComponentMk y := by
      have hc := (hker x y).mp h
      rw [heq, collapse_same, collapse_same] at hc
      exact hc
    let F : H.ConnectedComponent → G.ConnectedComponent :=
      Quot.lift G.connectedComponentMk (fun _ _ h => hold h)
    have hF : Function.Bijective F := by
      constructor
      · intro C D
        induction C using SimpleGraph.ConnectedComponent.ind with
        | h x =>
          induction D using SimpleGraph.ConnectedComponent.ind with
          | h y =>
            intro he
            exact SimpleGraph.ConnectedComponent.sound
              ((SimpleGraph.ConnectedComponent.exact he).mono le_sup_left)
      · intro C
        obtain ⟨x, hx⟩ := C.exists_rep
        exact ⟨H.connectedComponentMk x, hx⟩
    exact Nat.card_congr (Equiv.ofBijective F hF)
  · intro hne
    let F : H.ConnectedComponent → {C : G.ConnectedComponent // C ≠ cb} :=
      Quot.lift (fun x => ⟨collapse ca cb (G.connectedComponentMk x), by
        by_cases hx : G.connectedComponentMk x = cb
        · dsimp only [collapse]
          rw [if_pos hx]
          exact hne
        · simpa only [collapse, if_neg hx] using hx⟩)
        (fun x y h => Subtype.ext ((hker x y).mp h))
    have hF : Function.Bijective F := by
      constructor
      · intro C D
        induction C using SimpleGraph.ConnectedComponent.ind with
        | h x =>
          induction D using SimpleGraph.ConnectedComponent.ind with
          | h y =>
            intro he
            exact SimpleGraph.ConnectedComponent.sound
              ((hker x y).mpr (congrArg Subtype.val he))
      · intro C
        obtain ⟨x, hx⟩ := C.val.exists_rep
        refine ⟨H.connectedComponentMk x, Subtype.ext ?_⟩
        change collapse ca cb (G.connectedComponentMk x) = C.val
        change G.connectedComponentMk x = C.val at hx
        rw [hx]
        exact if_neg C.property
    have hc := Nat.card_congr (Equiv.ofBijective F hF)
    have hs := Nat.card_congr (Equiv.sumCompl (fun C : G.ConnectedComponent => C = cb))
    haveI : Subsingleton {C : G.ConnectedComponent // C = cb} := ⟨by
      rintro ⟨C, hC⟩ ⟨D, hD⟩
      exact Subtype.ext (hC.trans hD.symm)⟩
    have hone : Nat.card {C : G.ConnectedComponent // C = cb} = 1 :=
      Nat.card_of_subsingleton ⟨cb, rfl⟩
    rw [Nat.card_sum, hone] at hs
    change 1 + Nat.card {C : G.ConnectedComponent // C ≠ cb} =
      Nat.card G.ConnectedComponent at hs
    change Nat.card H.ConnectedComponent + 1 = Nat.card G.ConnectedComponent
    omega

/-- Rank of the actual spanning quotient. -/
def q (P : Parameters) (p : ℕ) (hp : p < 2) (S : Finset (Crossing P)) : ℕ :=
  Nat.card (Circle P p) - Nat.card (referenceGraph P p hp S).ConnectedComponent

theorem reference_component_card_le (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    Nat.card (referenceGraph P p hp S).ConnectedComponent ≤ Nat.card (Circle P p) :=
  Nat.card_le_card_of_surjective (referenceGraph P p hp S).connectedComponentMk
    (fun C => C.exists_rep)

/-- In particular the Nat subtraction defining q has no underflow. -/
theorem q_add_component_card (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    q P p hp S + Nat.card (referenceGraph P p hp S).ConnectedComponent =
      Nat.card (Circle P p) :=
  Nat.sub_add_cancel (reference_component_card_le P p hp S)

theorem referenceGraph_insert (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) :
    referenceGraph P p hp (insert z S) = referenceGraph P p hp S ⊔
      SimpleGraph.edge (edgeEnds P p z.1 z.2).1 (edgeEnds P p z.1 z.2).2 := by
  ext u v
  constructor
  · rintro ⟨a, ha, h⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · right
      apply (SimpleGraph.edge_adj _ _ u v).mpr
      refine ⟨h, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact edge_endpoints_distinct P p hp _ _
      · exact (edge_endpoints_distinct P p hp _ _).symm
    · exact Or.inl ⟨a, ha, h⟩
  · rintro (⟨a, ha, h⟩ | h)
    · exact ⟨a, Finset.mem_insert_of_mem ha, h⟩
    · exact ⟨z, Finset.mem_insert_self _ _, ((SimpleGraph.edge_adj _ _ u v).mp h).1⟩

theorem q_insert_of_same (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P)
    (h : (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).1 =
      (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).2) :
    q P p hp (insert z S) = q P p hp S := by
  have hc := (sup_edge_component_card (referenceGraph P p hp S)
    (edgeEnds P p z.1 z.2).1 (edgeEnds P p z.1 z.2).2).1 h
  rw [← referenceGraph_insert P p hp S z] at hc
  simp only [q, hc]

theorem q_insert_of_different (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P)
    (h : (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).1 ≠
      (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).2) :
    q P p hp (insert z S) = q P p hp S + 1 := by
  have hc := (sup_edge_component_card (referenceGraph P p hp S)
    (edgeEnds P p z.1 z.2).1 (edgeEnds P p z.1 z.2).2).2 h
  rw [← referenceGraph_insert P p hp S z] at hc
  have hold := q_add_component_card P p hp S
  have hnew := q_add_component_card P p hp (insert z S)
  omega

theorem q_insert_eq_or (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) :
    q P p hp (insert z S) = q P p hp S ∨
      q P p hp (insert z S) = q P p hp S + 1 := by
  by_cases h : (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).1 =
      (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).2
  · exact Or.inl (q_insert_of_same P p hp S z h)
  · exact Or.inr (q_insert_of_different P p hp S z h)

theorem q_insert_add_one_iff (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) :
    q P p hp (insert z S) = q P p hp S + 1 ↔
      (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).1 ≠
        (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).2 := by
  constructor
  · intro h heq
    have := q_insert_of_same P p hp S z heq
    omega
  · exact q_insert_of_different P p hp S z

private theorem endpoint_component_iff_dart (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) :
    ((referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).1 ≠
      (referenceGraph P p hp S).connectedComponentMk (edgeEnds P p z.1 z.2).2) ↔
    (dartComponent P p hp S (z.1, z.2, .tl) ≠
      dartComponent P p hp S (z.1, z.2, if cup p z.2 then .bl else .tr)) := by
  by_cases h : cup p z.2 <;> simp [edgeEnds, dartComponent, h]

/-- Euler defect, with every subtraction performed in Int. -/
def Delta (P : Parameters) (p : ℕ) (hp : p < 2) (S : Finset (Crossing P)) : ℤ :=
  (Nat.card (Circle P p) : ℤ) + (S.card : ℤ) - 2 * (q P p hp S : ℤ) -
    (Nat.card (MixedCircle P p S) : ℤ)

theorem Delta_insert_of_rank_add_one (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) (hz : z ∉ S)
    (hq : q P p hp (insert z S) = q P p hp S + 1) :
    Delta P p hp (insert z S) = Delta P p hp S := by
  have hd := (q_insert_add_one_iff P p hp S z).mp hq
  have hc := (mixed_insert_circle_count P p hp S z hz).2
    ((endpoint_component_iff_dart P p hp S z).mp hd)
  simp only [Delta, Finset.card_insert_of_notMem hz, hq, Nat.cast_add, Nat.cast_one]
  omega

theorem Delta_insert_of_rank_same (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) (hz : z ∉ S)
    (hq : q P p hp (insert z S) = q P p hp S) :
    Delta P p hp S ≤ Delta P p hp (insert z S) := by
  have hc := (abs_le.mp (mixed_insert_circle_count P p hp S z hz).1).2
  simp only [Delta, Finset.card_insert_of_notMem hz, hq, Nat.cast_add, Nat.cast_one]
  omega

theorem Delta_le_insert (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) (hz : z ∉ S) :
    Delta P p hp S ≤ Delta P p hp (insert z S) := by
  rcases q_insert_eq_or P p hp S z with hq | hq
  · exact Delta_insert_of_rank_same P p hp S z hz hq
  · exact le_of_eq (Delta_insert_of_rank_add_one P p hp S z hz hq).symm

theorem Delta_monotone (P : Parameters) (p : ℕ) (hp : p < 2) :
    Monotone (Delta P p hp) := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro S z hz
  exact Delta_le_insert P p hp S z hz

theorem q_empty (P : Parameters) (p : ℕ) (hp : p < 2) : q P p hp ∅ = 0 := by
  have hG : referenceGraph P p hp ∅ = ⊥ := by ext u v; simp [referenceGraph]
  have hc : Nat.card (⊥ : SimpleGraph (Circle P p)).ConnectedComponent =
      Nat.card (Circle P p) := by
    symm
    apply Nat.card_eq_of_bijective (⊥ : SimpleGraph (Circle P p)).connectedComponentMk
    constructor
    · intro u v h
      exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.exact h)
    · intro C; exact C.exists_rep
  simp only [q, hG, hc, Nat.sub_self]

theorem Delta_empty (P : Parameters) (p : ℕ) (hp : p < 2) : Delta P p hp ∅ = 0 := by
  unfold Delta
  rw [q_empty, mixed_empty_card]
  simp

theorem circle_card_pos (P : Parameters) (p : ℕ) : 0 < Nat.card (Circle P p) := by
  letI : Nonempty (Circle P p) := ⟨circle P p (0, ⟨0, by have := P.hn; omega⟩, .tl)⟩
  exact Nat.card_pos

theorem mixed_card_pos (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) :
    0 < Nat.card (MixedCircle P p S) := by
  letI : Nonempty (MixedCircle P p S) :=
    ⟨mixedCircle P p S (0, ⟨0, by have := P.hn; omega⟩, .tl)⟩
  exact Nat.card_pos

theorem q_univ (P : Parameters) (p : ℕ) (hp : p < 2) :
    q P p hp Finset.univ = Nat.card (Circle P p) - 1 := by
  let G := referenceGraph P p hp Finset.univ
  haveI : Subsingleton G.ConnectedComponent :=
    (referenceGraph_connected P p hp).preconnected.subsingleton_connectedComponent
  have hc : Nat.card G.ConnectedComponent = 1 :=
    Nat.card_of_subsingleton
      (G.connectedComponentMk (circle P p (0, ⟨0, by have := P.hn; omega⟩, .tl)))
  exact congrArg (fun k => Nat.card (Circle P p) - k) hc

theorem crossing_card (P : Parameters) :
    (Finset.univ : Finset (Crossing P)).card = P.n * P.m := by
  simp [Crossing, Fintype.card_prod, Nat.mul_comm]

/-- Exact complementary uniform count, including both outer-strand classes. -/
theorem circle_card_add_complement (P : Parameters) (p : ℕ) (hp : p < 2) :
    Nat.card (Circle P p) + Nat.card (Circle P (1 - p)) = P.n * P.m + 2 := by
  have hd : P.n % 2 ≤ 1 := by omega
  have hn : P.n = 2 * ((P.n - P.n % 2) / 2) + P.n % 2 := by omega
  have he : P.n * P.m =
      2 * (((P.n - P.n % 2) / 2) * P.m) + P.n % 2 * P.m := by
    calc
      P.n * P.m = (2 * ((P.n - P.n % 2) / 2) + P.n % 2) * P.m :=
        congrArg (fun x => x * P.m) hn
      _ = _ := by ring
  have hm : (((P.n - P.n % 2) / 2) + P.n % 2) * P.m =
      ((P.n - P.n % 2) / 2) * P.m + P.n % 2 * P.m := by ring
  have hp' : p = 0 ∨ p = 1 := by omega
  rcases hp' with rfl | rfl <;>
    norm_num only [Nat.sub_zero, Nat.sub_self] <;>
    rw [odd_circle_count, even_circle_count] <;> omega

theorem Delta_univ (P : Parameters) (p : ℕ) (hp : p < 2) :
    Delta P p hp Finset.univ = 0 := by
  have hv := circle_card_pos P p
  have hs := circle_card_add_complement P p hp
  simp only [Delta, q_univ, mixed_univ_card, crossing_card]
  omega

/-- Saturation on the entire finite subset lattice. -/
theorem Delta_eq_zero (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) : Delta P p hp S = 0 := by
  have hlo := Delta_monotone P p hp (Finset.empty_subset S)
  have hhi := Delta_monotone P p hp (Finset.subset_univ S)
  rw [Delta_empty] at hlo
  rw [Delta_univ] at hhi
  exact le_antisymm hhi hlo

/-- The literal arbitrary-state circle count, in Int to expose exactness. -/
theorem mixed_circle_count (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    (Nat.card (MixedCircle P p S) : ℤ) =
      (Nat.card (Circle P p) : ℤ) + (S.card : ℤ) - 2 * (q P p hp S : ℤ) := by
  have h := Delta_eq_zero P p hp S
  unfold Delta at h
  omega

/-- An equivalent subtraction-free natural-number equality. -/
theorem mixed_circle_count_nat (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    Nat.card (MixedCircle P p S) + 2 * q P p hp S =
      Nat.card (Circle P p) + S.card := by
  have h := mixed_circle_count P p hp S
  omega

theorem mixed_circle_exponent (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    0 ≤ (Nat.card (Circle P p) : ℤ) - 1 + (S.card : ℤ) - 2 * (q P p hp S : ℤ) ∧
    (Nat.card (MixedCircle P p S) : ℤ) - 1 =
      (Nat.card (Circle P p) : ℤ) - 1 + (S.card : ℤ) - 2 * (q P p hp S : ℤ) := by
  have h := mixed_circle_count P p hp S
  have hc := mixed_card_pos P p S
  constructor <;> omega

/-- Only after saturation do we conclude that a weaving switch is nonzero. -/
theorem mixed_insert_exact (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) (hz : z ∉ S) :
    (Nat.card (MixedCircle P p (insert z S)) : ℤ) -
        (Nat.card (MixedCircle P p S) : ℤ) =
      1 - 2 * ((q P p hp (insert z S) : ℤ) - (q P p hp S : ℤ)) ∧
    ((Nat.card (MixedCircle P p (insert z S)) : ℤ) -
      (Nat.card (MixedCircle P p S) : ℤ) = 1 ∨
     (Nat.card (MixedCircle P p (insert z S)) : ℤ) -
      (Nat.card (MixedCircle P p S) : ℤ) = -1) := by
  have hold := mixed_circle_count P p hp S
  have hnew := mixed_circle_count P p hp (insert z S)
  rw [Finset.card_insert_of_notMem hz, Nat.cast_add, Nat.cast_one] at hnew
  constructor
  · omega
  · rcases q_insert_eq_or P p hp S z with hq | hq
    · left; omega
    · right; omega

end
end D5.S3.Topology.WeavingEulerDefect
