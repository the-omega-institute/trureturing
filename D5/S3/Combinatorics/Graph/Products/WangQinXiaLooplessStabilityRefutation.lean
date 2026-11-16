/- GID: D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.claim; result=D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.result; claim=D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.claim
   digest: A stable loopless family has nontrivially unstable pairs with the four-vertex path. -/

/-
question_answered: https://github.com/the-omega-institute/trureturing/issues/24204 (Tier 3; Refuted).
admission_basis: escape-witness
escape_witness: loopless_family_stable_nontrivially_unstable, through gamma_stable /
  tf_diagonal / diamond_action and gamma_coprime / independent_bound.
The neighborhood-inclusion diamonds force the same index and bit action on both
permutations of a two-fold automorphism. An independent-set injection bounds
cardinality by m + 2 and excludes the two-vertex common factor, with loops allowed.
The four-vertex factor would make gamma bipartite. These steps hold uniformly for m >= 3.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The source's product and auxiliary looped graphs use the existing dirProd and LoopGraph
owners without replacement definitions. The claim retains the source predicates verbatim.
Direct frozen dependency identities (same-delivery helpers expanded):
D1: D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.LoopGraph
  declaration statement_id: sha256:8d478617a74986706263f120e9926ae17b04d21aceec950cd0ceaa1db074a76d
D2: D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.LoopGraph.edge
  declaration statement_id: sha256:82338b92e59b4374fd8ddabf3fafc0dea79c2d32f5133f19f89610515dbc27af
D3: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.dirProd
  declaration statement_id: sha256:4e00f0c64e9d082383b225b783d1e971e947f09fea65d918317ec234a59e04c5
D4: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.dirProd._proof_1
  declaration statement_id: sha256:685a286d2880f9fe7d764e8d47036c4ef8a3ce63a30bb98476da5d7ce51f0b5c
D5: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.dirProd._proof_2
  declaration statement_id: sha256:f47b82008f754846a419746ec2fb4e7f7b4645e314132cbd73de37173b71fada
Generated dirProd proof constants, when listed, have report inclusion flags
recorded with the dependency table. No module pin is used as a declaration identity.
proof_shape: TwinFree: bind-only; escape_witness: none;
  consumers: Nontrivial, gamma_twin_free, omega_twin_free; Direct frozen dependencies: none.
proof_shape: Coprime: bind-only; escape_witness: none;
  consumers: Nontrivial, gamma_coprime; Direct frozen dependencies: D1, D2.
proof_shape: StablePair: bind-only; escape_witness: none;
  consumers: StableGraph, claim, pair_unstable, loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: D3.
proof_shape: StableGraph: bind-only; escape_witness: none;
  consumers: claim, gamma_stable, loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: D3.
proof_shape: Nontrivial: bind-only; escape_witness: none;
  consumers: claim, loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: D1, D2.
proof_shape: claim: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: D1, D2, D3.
proof_shape: gamma: bind-only; escape_witness: none;
  consumers: neighbor_subset_iff, gamma_twin_free, gamma_connected, gamma_not_bipartite, diamond_action, tf_diagonal, mix_adj, mixer, pair_unstable, independent_bound, gamma_stable, gamma_coprime, loopless_family_stable_nontrivially_unstable, result; Direct frozen dependencies: none.
proof_shape: omegaGraph: bind-only; escape_witness: none;
  consumers: omegaAdjDecidable, omega_bipartite, omega_twin_free, omega_connected, mix_adj, mixer, pair_unstable, omega_two_factor_unlooped, gamma_coprime, loopless_family_stable_nontrivially_unstable, result; Direct frozen dependencies: none.
proof_shape: omegaAdjDecidable: bind-only; escape_witness: none;
  consumers: omega_connected, omega_two_factor_unlooped, gamma_coprime; Direct frozen dependencies: none.
proof_shape: A: bind-only; escape_witness: none;
  consumers: diamond_action, tf_diagonal, pair_unstable; Direct frozen dependencies: none.
proof_shape: B: bind-only; escape_witness: none;
  consumers: neighbor_subset_iff, diamond_action, tf_diagonal; Direct frozen dependencies: none.
proof_shape: C: bind-only; escape_witness: none;
  consumers: neighbor_subset_iff, diamond_action; Direct frozen dependencies: none.
proof_shape: D: bind-only; escape_witness: none;
  consumers: neighbor_subset_iff, gamma_connected, gamma_not_bipartite, diamond_action, tf_diagonal, independent_bound, gamma_stable; Direct frozen dependencies: none.
proof_shape: neighbor_subset_iff: content; escape_witness: neighbor_subset_iff;
  consumers: gamma_twin_free, diamond_action; Direct frozen dependencies: none.
proof_shape: gamma_twin_free: content; escape_witness: neighbor_subset_iff;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: none.
proof_shape: gamma_connected: bind-only; escape_witness: none;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: none.
proof_shape: gamma_not_bipartite: bind-only; escape_witness: none;
  consumers: gamma_coprime, loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: none.
proof_shape: omega_bipartite: bind-only; escape_witness: none;
  consumers: gamma_coprime, loopless_family_stable_nontrivially_unstable, result; Direct frozen dependencies: none.
proof_shape: omega_twin_free: bind-only; escape_witness: none;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: none.
proof_shape: tf_order: bind-only; escape_witness: none;
  consumers: tf_diagonal; Direct frozen dependencies: none.
proof_shape: diamond_action: content; escape_witness: diamond_action;
  consumers: tf_diagonal; Direct frozen dependencies: none.
proof_shape: tf_diagonal: content; escape_witness: diamond_action;
  consumers: gamma_stable; Direct frozen dependencies: none.
proof_shape: omega_connected: bind-only; escape_witness: none;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: none.
proof_shape: mix: bind-only; escape_witness: none;
  consumers: mix_involutive, mix_adj, mixer; Direct frozen dependencies: none.
proof_shape: mix_involutive: bind-only; escape_witness: none;
  consumers: mixer; Direct frozen dependencies: none.
proof_shape: mix_adj: bind-only; escape_witness: none;
  consumers: mixer; Direct frozen dependencies: D3, D4, D5.
proof_shape: mixer: bind-only; escape_witness: none;
  consumers: pair_unstable; Direct frozen dependencies: D3, D4, D5.
proof_shape: pair_unstable: bind-only; escape_witness: none;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: D3, D4, D5.
proof_shape: independent_bound: content; escape_witness: independent_bound;
  consumers: gamma_coprime; Direct frozen dependencies: none.
proof_shape: gamma_stable: content; escape_witness: tf_diagonal;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: D3, D4, D5.
proof_shape: omega_two_factor_unlooped: bind-only; escape_witness: none;
  consumers: gamma_coprime; Direct frozen dependencies: D1, D2.
proof_shape: gamma_coprime: content; escape_witness: independent_bound;
  consumers: loopless_family_stable_nontrivially_unstable; Direct frozen dependencies: D1, D2.
proof_shape: loopless_family_stable_nontrivially_unstable: content; escape_witness: gamma_stable, gamma_coprime;
  consumers: result; Direct frozen dependencies: D1, D2, D3, D4, D5.
proof_shape: result: content; escape_witness: loopless_family_stable_nontrivially_unstable;
  consumers: settles claim; Direct frozen dependencies: D1, D2, D3, D4, D5.
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
import D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Products.WangQinXiaLooplessStabilityRefutation

open D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap (dirProd)
open D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization (LoopGraph)

/-- No two distinct vertices have the same open neighborhood. -/
def TwinFree {V : Type} (G : SimpleGraph V) : Prop :=
  Function.Injective G.neighborSet

/-- No common direct factor of order greater than one, even with loops allowed.
The factor and both cofactors use the existing finite symmetric-relation owner LoopGraph.
RelIso is Mathlib's relation isomorphism, also underlying SimpleGraph.Iso. -/
def Coprime {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ¬ ∃ (d a b : ℕ) (F : LoopGraph d) (G' : LoopGraph a) (H' : LoopGraph b),
    1 < d ∧
      Nonempty (RelIso G.Adj
        (fun x y : Fin a × Fin d => G'.edge x.1 y.1 ∧ F.edge x.2 y.2)) ∧
      Nonempty (RelIso H.Adj
        (fun x y : Fin b × Fin d => H'.edge x.1 y.1 ∧ F.edge x.2 y.2))

/-- Every automorphism of the categorical product acts componentwise. -/
def StablePair {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ f : dirProd G H ≃g dirProd G H,
    ∃ (α : G ≃g G) (β : H ≃g H),
      ∀ p : V × W, f p = (α p.1, β p.2)

/-- The stability of G is the stability of (G,K₂). -/
def StableGraph {V : Type} (G : SimpleGraph V) : Prop :=
  StablePair G (⊤ : SimpleGraph (Fin 2))

/-- Definition 1.1: coprime connected twin-free graphs, exactly one bipartite. -/
def Nontrivial {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Coprime G H ∧ G.Connected ∧ H.Connected ∧ TwinFree G ∧ TwinFree H ∧
    ((G.IsBipartite ∧ ¬ H.IsBipartite) ∨ (¬ G.IsBipartite ∧ H.IsBipartite))

/-- Conjecture 1.3, over all finite undirected loopless graphs. -/
def claim : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W]
    (Gamma : SimpleGraph V) (Sigma : SimpleGraph W),
    Nontrivial Gamma Sigma → Sigma.IsBipartite → (StablePair Gamma Sigma ↔ StableGraph Gamma)

private def gamma (m : ℕ) : SimpleGraph (Fin m × Bool × Bool) where
  Adj u v := u.1 ≠ v.1 ∧ (u.2.1 = true ∨ v.2.2 = true) ∧ (v.2.1 = true ∨ u.2.2 = true)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def omegaGraph : SimpleGraph (Bool × Bool) where
  Adj u v := u.1 ≠ v.1 ∧ (u.2 = true ∨ v.2 = true)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance omegaAdjDecidable : DecidableRel omegaGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private abbrev A {m : ℕ} (i : Fin m) : (Fin m × Bool × Bool) := (i, false, false)
private abbrev B {m : ℕ} (i : Fin m) : (Fin m × Bool × Bool) := (i, false, true)
private abbrev C {m : ℕ} (i : Fin m) : (Fin m × Bool × Bool) := (i, true, false)
private abbrev D {m : ℕ} (i : Fin m) : (Fin m × Bool × Bool) := (i, true, true)

private theorem neighbor_subset_iff {m : ℕ} (hm : 3 ≤ m) (u v : (Fin m × Bool × Bool)) :
    (gamma m).neighborSet u ⊆ (gamma m).neighborSet v ↔
      u.1 = v.1 ∧ (u.2.1 = true → v.2.1 = true) ∧
        (u.2.2 = true → v.2.2 = true) := by
  constructor
  · intro h
    have hi : u.1 = v.1 := by
      by_contra hn
      have hx : (gamma m).Adj u (D v.1) := ⟨hn, Or.inr rfl, Or.inl rfl⟩
      exact (h hx).1 rfl
    obtain ⟨j, hju, _⟩ := Fin.exists_ne_and_ne_of_two_lt u.1 u.1 (by omega)
    have ha := fun hx => h (show (gamma m).Adj u (B j) from
      ⟨Ne.symm hju, Or.inr rfl, Or.inr hx⟩)
    have hb := fun hx => h (show (gamma m).Adj u (C j) from
      ⟨Ne.symm hju, Or.inl hx, Or.inl rfl⟩)
    exact ⟨hi, fun hx => (hb hx).2.1.resolve_right Bool.false_ne_true,
      fun hx => (ha hx).2.2.resolve_left Bool.false_ne_true⟩
  · rintro ⟨hi, ha, hb⟩ w ⟨hidx, had, hcb⟩
    refine ⟨by simpa [← hi] using hidx, ?_, ?_⟩
    · exact had.elim (fun h => Or.inl (ha h)) Or.inr
    · exact hcb.elim Or.inl (fun h => Or.inr (hb h))

private theorem gamma_twin_free {m : ℕ} (hm : 3 ≤ m) : TwinFree (gamma m) := by
  intro u v h
  have huv := (neighbor_subset_iff hm u v).mp (by rw [h])
  have hvu := (neighbor_subset_iff hm v u).mp (by rw [h])
  apply Prod.ext huv.1
  apply Prod.ext
  · cases hu : u.2.1 <;> cases hv : v.2.1 <;> simp_all
  · cases hu : u.2.2 <;> cases hv : v.2.2 <;> simp_all

private theorem gamma_connected {m : ℕ} (hm : 3 ≤ m) : (gamma m).Connected := by
  let i : Fin m := ⟨0, by omega⟩
  have hd : ∀ j k : Fin m, (gamma m).Reachable (D j) (D k) := by
    intro j k
    by_cases h : j = k
    · subst k; exact .rfl
    · exact (show (gamma m).Adj (D j) (D k) from ⟨h, Or.inl rfl, Or.inl rfl⟩).reachable
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨D i, ?_⟩
  intro u
  obtain ⟨j, hju, _⟩ := Fin.exists_ne_and_ne_of_two_lt u.1 u.1 (by omega)
  exact (hd i j).trans (show (gamma m).Adj (D j) u from
    ⟨hju, Or.inl rfl, Or.inr rfl⟩).reachable

private theorem gamma_not_bipartite {m : ℕ} (hm : 3 ≤ m) : ¬ (gamma m).IsBipartite := by
  rintro ⟨c, hc⟩
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  let k : Fin m := ⟨2, by omega⟩
  have h₁ : c (D i) ≠ c (D j) := hc (show (gamma m).Adj (D i) (D j) from
    ⟨by intro he; have := congrArg Fin.val he; simp [i,j] at this, Or.inl rfl, Or.inl rfl⟩)
  have h₂ : c (D i) ≠ c (D k) := hc (show (gamma m).Adj (D i) (D k) from
    ⟨by intro he; have := congrArg Fin.val he; simp [i,k] at this, Or.inl rfl, Or.inl rfl⟩)
  have h₃ : c (D j) ≠ c (D k) := hc (show (gamma m).Adj (D j) (D k) from
    ⟨by intro he; have := congrArg Fin.val he; simp [j,k] at this, Or.inl rfl, Or.inl rfl⟩)
  have := (c (D i)).isLt
  have := (c (D j)).isLt
  have := (c (D k)).isLt
  omega

private theorem omega_bipartite : omegaGraph.IsBipartite := by
  refine ⟨fun u => if u.1 then 1 else 0, ?_⟩
  intro u v h
  rcases u with ⟨s, a⟩; rcases v with ⟨t, b⟩
  cases s <;> cases t <;> simp_all [omegaGraph]

private theorem omega_twin_free : TwinFree omegaGraph := by
  intro u v h
  have hx : ∀ w, omegaGraph.Adj u w ↔ omegaGraph.Adj v w :=
    fun w => Set.ext_iff.mp h w
  rcases u with ⟨s, a⟩; rcases v with ⟨t, b⟩
  cases s <;> cases a <;> cases t <;> cases b <;>
    simp_all [omegaGraph]

private theorem tf_order {V : Type} (G : SimpleGraph V) (α β : Equiv.Perm V)
    (h : ∀ u v, G.Adj u v ↔ G.Adj (α u) (β v)) (u v : V) :
    G.neighborSet u ⊆ G.neighborSet v ↔
      G.neighborSet (α u) ⊆ G.neighborSet (α v) := by
  constructor
  · intro huv w hw
    obtain ⟨z, rfl⟩ := β.surjective w
    exact (h v z).mp (huv ((h u z).mpr hw))
  · intro huv w hw
    exact (h v w).mpr (huv ((h u w).mp hw))

private theorem diamond_action {m : ℕ} (hm : 3 ≤ m) (e : Equiv.Perm (Fin m × Bool × Bool))
    (ho : ∀ u v, (gamma m).neighborSet u ⊆ (gamma m).neighborSet v ↔
      (gamma m).neighborSet (e u) ⊆ (gamma m).neighborSet (e v)) :
    ∃ (p : Fin m → Fin m) (ε : Fin m → Bool), ∀ i,
      e (A i) = A (p i) ∧ e (B i) = (p i, ε i, !(ε i)) ∧
      e (C i) = (p i, !(ε i), ε i) ∧ e (D i) = D (p i) := by
  have hmin (i : Fin m) (u : (Fin m × Bool × Bool))
      (h : (gamma m).neighborSet u ⊆ (gamma m).neighborSet (A i)) : u = A i := by
    obtain ⟨j, a, b⟩ := u
    have hh := (neighbor_subset_iff hm (j,a,b) (A i)).mp h
    apply Prod.ext hh.1
    apply Prod.ext
    · cases a
      · rfl
      · exact False.elim (Bool.false_ne_true (hh.2.1 rfl))
    · cases b
      · rfl
      · exact False.elim (Bool.false_ne_true (hh.2.2 rfl))
  have hmax (i : Fin m) (u : (Fin m × Bool × Bool))
      (h : (gamma m).neighborSet (D i) ⊆ (gamma m).neighborSet u) : u = D i := by
    obtain ⟨j, a, b⟩ := u
    have hh := (neighbor_subset_iff hm (D i) (j,a,b)).mp h
    exact Prod.ext hh.1.symm (Prod.ext (hh.2.1 rfl) (hh.2.2 rfl))
  have hA (i : Fin m) : e (A i) = A (e (A i)).1 := by
    have hl : (gamma m).neighborSet (A (e (A i)).1) ⊆ (gamma m).neighborSet (e (A i)) :=
      (neighbor_subset_iff hm _ _).mpr ⟨rfl, by simp, by simp⟩
    have hh := hmin i (e.symm (A (e (A i)).1)) ((ho _ _).mpr (by simpa using hl))
    simpa using (congrArg e hh).symm
  have hD (i : Fin m) : e (D i) = D (e (D i)).1 := by
    have hl : (gamma m).neighborSet (e (D i)) ⊆ (gamma m).neighborSet (D (e (D i)).1) :=
      (neighbor_subset_iff hm _ _).mpr ⟨rfl, by simp, by simp⟩
    have hh := hmax i (e.symm (D (e (D i)).1)) ((ho _ _).mpr (by simpa using hl))
    simpa using (congrArg e hh).symm
  let p : Fin m → Fin m := fun i => (e (A i)).1
  have hidx (u : (Fin m × Bool × Bool)) : (e u).1 = p u.1 := by
    have hh := (ho (A u.1) u).mp ((neighbor_subset_iff hm _ _).mpr
      ⟨rfl, by simp, by simp⟩)
    exact ((neighbor_subset_iff hm _ _).mp hh).1.symm
  have hd (i : Fin m) : e (D i) = D (p i) := by rw [hD i, hidx (D i)]
  have hb (i : Fin m) : (e (B i)).2.2 = !(e (B i)).2.1 := by
    have h₁ : e (B i) ≠ e (A i) := fun h => by have := e.injective h; cases this
    have h₂ : e (B i) ≠ e (D i) := fun h => by have := e.injective h; cases this
    rw [hA i] at h₁
    rw [hd i] at h₂
    have hi := hidx (B i)
    cases ha : (e (B i)).2.1 <;> cases hb : (e (B i)).2.2 <;>
      simp [Prod.ext_iff, hi, ha, hb, p] at h₁ h₂ ⊢
  refine ⟨p, fun i => (e (B i)).2.1, ?_⟩
  intro i
  have hbi : e (B i) = (p i, (e (B i)).2.1, !(e (B i)).2.1) := by
    exact Prod.ext (hidx _) (Prod.ext rfl (hb i))
  have hci : e (C i) = (p i, !(e (B i)).2.1, (e (B i)).2.1) := by
    have h₁ : e (C i) ≠ e (A i) := fun h => by have := e.injective h; cases this
    have h₂ : e (C i) ≠ e (D i) := fun h => by have := e.injective h; cases this
    have h₃ : e (C i) ≠ e (B i) := fun h => by have := e.injective h; cases this
    rw [hA i] at h₁
    rw [hd i] at h₂
    rw [hbi] at h₃
    have hi := hidx (C i)
    cases hε : (e (B i)).2.1 <;> cases ha : (e (C i)).2.1 <;>
      cases hb : (e (C i)).2.2 <;> simp [Prod.ext_iff, hi, ha, hb, hε, p] at h₁ h₂ h₃ ⊢
  exact ⟨hA i, hbi, hci, hd i⟩

private theorem tf_diagonal {m : ℕ} (hm : 3 ≤ m) (α β : Equiv.Perm (Fin m × Bool × Bool))
    (h : ∀ u v, (gamma m).Adj u v ↔ (gamma m).Adj (α u) (β v)) : α = β := by
  have hs : ∀ u v, (gamma m).Adj u v ↔ (gamma m).Adj (β u) (α v) := by
    intro u v
    rw [(gamma m).adj_comm u v, h v u, (gamma m).adj_comm]
  obtain ⟨p, ε, hp⟩ := diamond_action hm α (tf_order (gamma m) α β h)
  obtain ⟨q, δ, hq⟩ := diamond_action hm β (tf_order (gamma m) β α hs)
  have hpq (i : Fin m) : p i = q i := by
    by_contra hn
    have hh : (gamma m).Adj (α (A i)) (β (D i)) := by
      rw [(hp i).1, (hq i).2.2.2]
      exact ⟨hn, Or.inr rfl, Or.inl rfl⟩
    exact ((h _ _).mpr hh).1 rfl
  have hε (i j : Fin m) (hij : i ≠ j) : ε i = δ j := by
    have hh := (h (B i) (B j)).mp ⟨hij, Or.inr rfl, Or.inr rfl⟩
    rw [(hp i).2.1, (hq j).2.1] at hh
    cases he : ε i <;> cases hd : δ j <;> simp [gamma, he, hd] at hh ⊢
  have heq (i j : Fin m) : ε i = ε j := by
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    exact (hε i k hki.symm).trans (hε j k hkj.symm).symm
  have hd (i : Fin m) : ε i = δ i := by
    obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
    exact (heq i j).trans (hε j i hji)
  apply Equiv.ext
  rintro ⟨i,a,b⟩
  cases a <;> cases b
  · simp only [(hp i).1, (hq i).1, hpq i]
  · simp only [(hp i).2.1, (hq i).2.1, hpq i, hd i]
  · simp only [(hp i).2.2.1, (hq i).2.2.1, hpq i, hd i]
  · simp only [(hp i).2.2.2, (hq i).2.2.2, hpq i]

private theorem omega_connected : omegaGraph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(false,true), ?_⟩
  rintro ⟨s,a⟩
  cases s <;> cases a
  · exact (show omegaGraph.Adj (false,true) (true,true) from by decide).reachable.trans
      (show omegaGraph.Adj (true,true) (false,false) from by decide).reachable
  · exact .rfl
  · exact (show omegaGraph.Adj (false,true) (true,false) from by decide).reachable
  · exact (show omegaGraph.Adj (false,true) (true,true) from by decide).reachable

private def mix {m : ℕ} (p : (Fin m × Bool × Bool) × (Bool × Bool)) : (Fin m × Bool × Bool) × (Bool × Bool) :=
  if p.2.1 then ((p.1.1,p.2.2,p.1.2.2),(true,p.1.2.1))
  else ((p.1.1,p.1.2.1,p.2.2),(false,p.1.2.2))

private theorem mix_involutive {m : ℕ} : Function.Involutive (@mix m) := by
  rintro ⟨⟨t,a,b⟩,s,i⟩
  cases s <;> rfl

private theorem mix_adj {m : ℕ} (p q : (Fin m × Bool × Bool) × (Bool × Bool)) :
    (dirProd (gamma m) omegaGraph).Adj (mix p) (mix q) ↔
      (dirProd (gamma m) omegaGraph).Adj p q := by
  rcases p with ⟨⟨t,a,b⟩,s,i⟩
  rcases q with ⟨⟨u,c,d⟩,r,j⟩
  cases s <;> cases r <;>
    simp [mix, dirProd, gamma, omegaGraph, and_assoc, and_comm, and_left_comm, or_comm]

private def mixer (m : ℕ) : dirProd (gamma m) omegaGraph ≃g dirProd (gamma m) omegaGraph where
  toFun := mix
  invFun := mix
  left_inv := mix_involutive
  right_inv := mix_involutive
  map_rel_iff' := mix_adj _ _

private theorem pair_unstable {m : ℕ} (hm : 3 ≤ m) : ¬ StablePair (gamma m) omegaGraph := by
  intro h
  obtain ⟨α,β,hf⟩ := h (mixer m)
  let t : Fin m := ⟨0, by omega⟩
  have h₀ := congrArg (fun p : (Fin m × Bool × Bool) × (Bool × Bool) => p.1.2.2)
    (hf (A t, (false,false)))
  have h₁ := congrArg (fun p : (Fin m × Bool × Bool) × (Bool × Bool) => p.1.2.2)
    (hf (A t, (false,true)))
  change false = (α (A t)).2.2 at h₀
  change true = (α (A t)).2.2 at h₁
  exact Bool.false_ne_true (h₀.trans h₁.symm)

private theorem independent_bound {m : ℕ} (hm : 3 ≤ m) (S : Finset (Fin m × Bool × Bool))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ (gamma m).Adj u v) : S.card ≤ m + 2 := by
  classical
  by_cases hD : ∃ i : Fin m, D i ∈ S
  · obtain ⟨i,hi⟩ := hD
    have hidx (u : (Fin m × Bool × Bool)) (hu : u ∈ S) : u.1 = i := by
      by_contra hn
      exact hS u hu (D i) hi ⟨hn, Or.inr rfl, Or.inl rfl⟩
    have hinj : Function.Injective (fun u : S => u.val.2) := by
      intro u v h
      apply Subtype.ext
      exact Prod.ext ((hidx u u.property).trans (hidx v v.property).symm) h
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hc
    omega
  · have hno (i : Fin m) : D i ∉ S := fun h => hD ⟨i,h⟩
    let tag : (Fin m × Bool × Bool) → Fin m ⊕ Bool := fun u =>
      if u.2.1 = false ∧ u.2.2 = false then Sum.inl u.1 else Sum.inr u.2.1
    have hinj : Function.Injective (fun u : S => tag u.val) := by
      rintro ⟨⟨i,a,b⟩,hu⟩ ⟨⟨j,c,d⟩,hv⟩ ht
      apply Subtype.ext
      have hn := hS (i,a,b) hu (j,c,d) hv
      have hni := hno i
      have hnj := hno j
      clear hS hno hD
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp_all [tag, gamma]
    have hc := Fintype.card_le_of_injective _ hinj
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_bool] using hc

private theorem gamma_stable {m : ℕ} (hm : 3 ≤ m) : StableGraph (gamma m) := by
  classical
  intro f
  let i : Fin m := ⟨0, by omega⟩
  have hcol (u v : (Fin m × Bool × Bool)) (s t : Fin 2) (huv : (gamma m).Adj u v) (hst : s ≠ t) :
      (f (u,s)).2 ≠ (f (v,t)).2 :=
    (f.map_rel_iff.mpr (show (dirProd (gamma m) (⊤ : SimpleGraph (Fin 2))).Adj
      (u,s) (v,t) from ⟨huv,hst⟩)).2
  have hside (u v : (Fin m × Bool × Bool)) (s : Fin 2) : (f (u,s)).2 = (f (v,s)).2 := by
    obtain ⟨j,hju,hjv⟩ := Fin.exists_ne_and_ne_of_two_lt u.1 v.1 (by omega)
    let t : Fin 2 := if s = 0 then 1 else 0
    have hst : s ≠ t := by dsimp [t]; split <;> omega
    have hu := hcol u (D j) s t ⟨hju.symm, Or.inr rfl, Or.inl rfl⟩ hst
    have hv := hcol v (D j) s t ⟨hjv.symm, Or.inr rfl, Or.inl rfl⟩ hst
    have := (f (u,s)).2.isLt
    have := (f (v,s)).2.isLt
    have := (f (D j,t)).2.isLt
    omega
  let b : Fin 2 → Fin 2 := fun s => (f (D i,s)).2
  have hb : Function.Injective b := by
    intro s t h
    by_contra hn
    obtain ⟨j,hji,_⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
    have hh := hcol (D i) (D j) s t ⟨hji.symm, Or.inl rfl, Or.inl rfl⟩ hn
    rw [hside (D j) (D i) t] at hh
    exact hh h
  let βe : Equiv.Perm (Fin 2) := Equiv.ofBijective b ⟨hb,Finite.surjective_of_injective hb⟩
  let a : Fin 2 → (Fin m × Bool × Bool) → (Fin m × Bool × Bool) := fun s u => (f (u,s)).1
  have ha (s : Fin 2) : Function.Injective (a s) := by
    intro u v huv
    have hh : f (u,s) = f (v,s) := Prod.ext huv (hside u v s)
    exact congrArg Prod.fst (f.injective hh)
  let e : Fin 2 → Equiv.Perm (Fin m × Bool × Bool) := fun s =>
    Equiv.ofBijective (a s) ⟨ha s,Finite.surjective_of_injective (ha s)⟩
  have hf (u : (Fin m × Bool × Bool)) (s : Fin 2) : f (u,s) = (e s u, βe s) :=
    Prod.ext rfl (hside u (D i) s)
  have ht : ∀ u v, (gamma m).Adj u v ↔ (gamma m).Adj (e 0 u) (e 1 v) := by
    intro u v
    have hh := f.map_rel_iff (a := (u,0)) (b := (v,1))
    rw [hf u 0,hf v 1] at hh
    have hβ : βe 0 ≠ βe 1 := fun h => by have := βe.injective h; omega
    simpa [dirProd,hβ] using hh.symm
  have heq := tf_diagonal hm (e 0) (e 1) ht
  let α : gamma m ≃g gamma m :=
    { toEquiv := e 0
      map_rel_iff' := by
        intro u v
        simpa only [← heq] using (ht u v).symm }
  let β : (⊤ : SimpleGraph (Fin 2)) ≃g (⊤ : SimpleGraph (Fin 2)) :=
    { toEquiv := βe
      map_rel_iff' := by
        intro s t
        exact not_congr βe.injective.eq_iff }
  refine ⟨α,β,?_⟩
  rintro ⟨u,s⟩
  rw [hf u s]
  apply Prod.ext
  · change e s u = e 0 u
    fin_cases s
    · rfl
    · exact congrArg (fun k : Equiv.Perm (Fin m × Bool × Bool) => k u) heq.symm
  · rfl

private theorem omega_two_factor_unlooped (J F : LoopGraph 2)
    (e : RelIso omegaGraph.Adj
      (fun x y : Fin 2 × Fin 2 => J.edge x.1 y.1 ∧ F.edge x.2 y.2)) :
    ∃ z, ¬ F.edge z z := by
  classical
  by_contra hn
  push Not at hn
  have hJ (a : Fin 2) : ¬ J.edge a a := by
    intro ha
    have hh := e.symm.map_rel_iff.mpr
      (show J.edge (a,0).1 (a,0).1 ∧ F.edge (a,0).2 (a,0).2 from ⟨ha,hn 0⟩)
    exact omegaGraph.irrefl hh
  have hleaf (q : Fin 2 × Fin 2)
      (hq : J.edge (e (false,false)).1 q.1 ∧ F.edge (e (false,false)).2 q.2) :
      q = e (true,true) := by
    have hh : omegaGraph.Adj (false,false) (e.symm q) := by
      simpa using e.symm.map_rel_iff.mpr hq
    have hp : e.symm q = (true,true) := by
      have hs : (e.symm q).1 = true := by
        cases hside : (e.symm q).1
        · exact False.elim (hh.1 hside.symm)
        · rfl
      exact Prod.ext hs (hh.2.resolve_left Bool.false_ne_true)
    simpa using congrArg e hp
  have hln := e.map_rel_iff.mpr
    (show omegaGraph.Adj (false,false) (true,true) from by decide)
  have hnt := e.map_rel_iff.mpr
    (show omegaGraph.Adj (true,true) (false,true) from by decide)
  have hxy : (e (false,false)).2 = (e (true,true)).2 := by
    have hh := congrArg (fun p : Fin 2 × Fin 2 => p.2)
      (hleaf ((e (true,true)).1,(e (false,false)).2) ⟨hln.1,hn _⟩)
    exact hh
  have hab : (e (false,false)).1 ≠ (e (true,true)).1 := by
    intro hh
    exact hJ _ (by simpa only [hh] using hln.1)
  have hbc : (e (true,true)).1 ≠ (e (false,true)).1 := by
    intro hh
    exact hJ _ (by simpa only [hh] using hnt.1)
  have hac : (e (false,false)).1 = (e (false,true)).1 := by
    have := (e (false,false)).1.isLt
    have := (e (true,true)).1.isLt
    have := (e (false,true)).1.isLt
    omega
  have hzy : (e (false,true)).2 = (e (true,true)).2 := by
    have hh := congrArg (fun p : Fin 2 × Fin 2 => p.2)
      (hleaf ((e (true,true)).1,(e (false,true)).2)
        ⟨hln.1,by simpa only [hxy] using hnt.2⟩)
    exact hh
  have he : e (false,false) = e (false,true) := Prod.ext hac (hxy.trans hzy.symm)
  have hf := congrArg Prod.snd (e.injective he)
  exact Bool.false_ne_true hf

private theorem gamma_coprime {m : ℕ} (hm : 3 ≤ m) : Coprime (gamma m) omegaGraph := by
  classical
  rintro ⟨d,a,b,F,J,K,hd,⟨eG⟩,⟨eO⟩⟩
  have hGcard : m * 4 = a * d := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] using
      Fintype.card_congr eG.toEquiv
  have hOcard : b * d = 4 := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] using
      (Fintype.card_congr eO.toEquiv).symm
  have hb : 0 < b := by nlinarith
  have hdle : d ≤ 4 := by nlinarith
  have hdcases : d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hdcases with h2 | h3 | h4
  · subst d
    have hb2 : b = 2 := by omega
    subst b
    obtain ⟨z,hz⟩ := omega_two_factor_unlooped K F eO
    let f : Fin a → (Fin m × Bool × Bool) := fun x => eG.symm (x,z)
    have hfinj : Function.Injective f := by
      intro x y h
      have hh := congrArg eG h
      simpa [f] using congrArg Prod.fst hh
    let S : Finset (Fin m × Bool × Bool) := Finset.univ.image f
    have hScard : S.card = a := by
      simp only [S,Finset.card_image_of_injective _ hfinj,Finset.card_univ,
        Fintype.card_fin]
    have hS : ∀ u ∈ S, ∀ v ∈ S, ¬ (gamma m).Adj u v := by
      intro u hu v hv huv
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hv
      have hh := eG.map_rel_iff.mpr huv
      exact hz (by simpa [f] using hh.2)
    have hbound := independent_bound hm S hS
    rw [hScard] at hbound
    omega
  · subst d
    omega
  · subst d
    have hb1 : b = 1 := by omega
    subst b
    have hK : K.edge 0 0 := by
      have hh := (eO.map_rel_iff.mpr
        (show omegaGraph.Adj (false,false) (true,true) from by decide)).1
      have h₁ : (eO (false,false)).1 = 0 := Subsingleton.elim _ _
      have h₂ : (eO (true,true)).1 = 0 := Subsingleton.elim _ _
      simpa only [h₁,h₂] using hh
    obtain ⟨c⟩ := omega_bipartite
    let col : (Fin m × Bool × Bool) → Fin 2 := fun u => c (eO.symm (0,(eG u).2))
    have hcolor : (gamma m).IsBipartite := by
      refine ⟨SimpleGraph.Coloring.mk col ?_⟩
      intro u v huv
      apply c.valid
      apply eO.symm.map_rel_iff.mpr
      exact ⟨hK,(eG.map_rel_iff.mpr huv).2⟩
    exact gamma_not_bipartite hm hcolor

private theorem loopless_family_stable_nontrivially_unstable (m : ℕ) (hm : 3 ≤ m) :
    StableGraph (gamma m) ∧ Nontrivial (gamma m) omegaGraph ∧
      ¬ StablePair (gamma m) omegaGraph := by
  refine ⟨gamma_stable hm, ?_, pair_unstable hm⟩
  exact ⟨gamma_coprime hm, gamma_connected hm, omega_connected,
    gamma_twin_free hm, omega_twin_free, Or.inr ⟨gamma_not_bipartite hm,omega_bipartite⟩⟩

theorem result : ¬ claim := by
  intro h
  have hf := loopless_family_stable_nontrivially_unstable 3 (by decide)
  exact hf.2.2 ((h (Fin 3 × Bool × Bool) (Bool × Bool) (gamma 3) omegaGraph hf.2.1 omega_bipartite).mpr hf.1)

end D5.S3.Combinatorics.Graph.Products.WangQinXiaLooplessStabilityRefutation
