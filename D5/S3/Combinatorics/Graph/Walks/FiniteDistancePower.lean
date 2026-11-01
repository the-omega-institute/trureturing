/- GID: D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/FiniteDistancePower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum]
   utility: none
   digest: Finite walks and maximal independent sets transport through disconnected distance powers. -/
import D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation
import D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
import D5.S3.Combinatorics.Graph.Products.CayleyCharacterization
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finset.Sigma

set_option autoImplicit false

namespace FiniteDistancePower

open SimpleGraph
open WellCoveredPowerCliqueProduct (IsMaximalIndep WellCovered power WCP)
open MatchingCliqueCycle (spectrum)
open D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)

variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The first faithful power is the original graph, including for disconnected graphs. -/
theorem power_one : graphPower G 1 = G := by
  ext u v
  change (u ≠ v ∧ G.edist u v ≤ (1 : ℕ∞)) ↔ G.Adj u v
  rw [G.edist_le_one_iff_adj_or_eq]
  exact ⟨fun h => h.2.resolve_right h.1, fun h => ⟨h.ne,Or.inl h⟩⟩

/-- A graph isomorphism transports actual independent dominating vertex sets. -/
theorem maximal_image_iso [DecidableEq V] [DecidableEq W] (e : G ≃g H)
    (I : Finset V) (hI : IsMaximalIndep G I) :
    IsMaximalIndep H (I.image e) := by
  constructor
  · intro u hu v hv hne ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact hI.1 x hx y hy (fun he => hne (congrArg e he)) (e.map_adj_iff.mp ha)
  · intro v hv
    have hv' : e.symm v ∉ I := by
      intro hm
      exact hv (Finset.mem_image.mpr ⟨e.symm v,hm,by simp⟩)
    obtain ⟨u,hu,ha⟩ := hI.2 (e.symm v) hv'
    refine ⟨e u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,?_⟩
    simpa using e.toHom.map_adj ha

/-- Spectrum transport retains cardinalities and constructs both directions on native vertices. -/
theorem spectrum_iso [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : G ≃g H) : spectrum G = spectrum H := by
  ext k
  constructor
  · rintro ⟨I,hI,hcard⟩
    exact ⟨I.image e,maximal_image_iso e I hI,by
      rw [Finset.card_image_of_injective _ e.injective,hcard]⟩
  · rintro ⟨I,hI,hcard⟩
    exact ⟨I.image e.symm,maximal_image_iso e.symm I hI,by
      rw [Finset.card_image_of_injective _ e.symm.injective,hcard]⟩

/-- The existing extended-distance power is exactly bounded finite-walk adjacency. -/
theorem power_adj_iff_walk (d : ℕ) (u v : V) :
    (graphPower G d).Adj u v ↔ u ≠ v ∧ ∃ p : G.Walk u v, p.length ≤ d := by
  constructor
  · rintro ⟨hne, hdist⟩
    have hfinite : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hdist
    obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top hfinite
    exact ⟨hne, p, by exact_mod_cast hp.le.trans hdist⟩
  · rintro ⟨hne, p, hp⟩
    exact ⟨hne, p.edist_le.trans (by exact_mod_cast hp)⟩

/-- Isomorphisms of faithful powers come from length-preserving maps of finite walks. -/
def powerIso (e : G ≃g H) (d : ℕ) : graphPower G d ≃g graphPower H d where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    rw [power_adj_iff_walk,power_adj_iff_walk]
    constructor
    · rintro ⟨hne,p,hp⟩
      refine ⟨fun h => hne (congrArg e h),?_,?_⟩
      · exact (p.map e.symm.toHom).copy (by simp) (by simp)
      · simpa using hp
    · rintro ⟨hne,p,hp⟩
      exact ⟨fun h => hne (e.injective h),p.map e.toHom,by simpa using hp⟩

/-- No positive power changes which vertices have a finite joining walk. -/
theorem power_reachable_iff {d : ℕ} (hd : 1 ≤ d) (u v : V) :
    (graphPower G d).Reachable u v ↔ G.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl _
    | @cons x y z hxy p ih =>
      obtain ⟨_, q, _⟩ := (power_adj_iff_walk d x y).mp hxy
      exact (show G.Reachable x y from ⟨q⟩).trans ih
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl _
    | @cons x y z hxy p ih =>
      have hp : (graphPower G d).Adj x y :=
        (power_adj_iff_walk d x y).mpr ⟨hxy.ne, hxy.toWalk, by simpa using hd⟩
      exact hp.reachable.trans ih

/-- On a connected graph the frozen natural-distance supplier has identical adjacency. -/
theorem power_eq_connected (hc : G.Connected) (d : ℕ) : graphPower G d = power G d := by
  ext u v
  change (u ≠ v ∧ G.edist u v ≤ (d : ℕ∞)) ↔ (u ≠ v ∧ G.dist u v ≤ d)
  rw [← (hc u v).coe_dist_eq_edist]
  simp only [ENat.natCast_le_natCast]

private theorem walk_stays {s : Set V}
    (hclosed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)
    {u v : V} (p : G.Walk u v) (hu : u ∈ s) : ∀ x ∈ p.support, x ∈ s := by
  induction p with
  | nil => simpa using hu
  | @cons u v w huv p ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact ih (hclosed hu huv) x hx

/-- Every walk stays in an adjacency-closed block, so inducing loses no finite paths. -/
theorem power_induce (s : Set V)
    (hclosed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) (d : ℕ) :
    graphPower (G.induce s) d = (graphPower G d).induce s := by
  ext u v
  rw [power_adj_iff_walk]
  change (u ≠ v ∧ ∃ p : (G.induce s).Walk u v, p.length ≤ d) ↔
    (graphPower G d).Adj u.val v.val
  rw [power_adj_iff_walk]
  constructor
  · rintro ⟨hne, p, hp⟩
    refine ⟨fun h => hne (Subtype.ext h), p.map (Embedding.induce s).toHom, ?_⟩
    exact (p.length_map (Embedding.induce s).toHom).le.trans hp
  · rintro ⟨hne, p, hp⟩
    have hs := walk_stays hclosed p u.property
    refine ⟨fun h => hne (congrArg Subtype.val h), p.induce s hs, ?_⟩
    have hlen := congrArg Walk.length (p.map_induce hs)
    rw [Walk.length_map] at hlen
    exact hlen.le.trans hp

section Partition

variable {ι : Type} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (b : V → ι)

/-- Restriction retains the actual vertices of a block, with their membership proofs. -/
noncomputable def restrict (I : Finset V) (i : ι) : Finset {v : V // b v = i} := by
  classical
  exact I.subtype (fun v => b v = i)

/-- Assembly is the union of the vertex images of the chosen block sets. -/
noncomputable def assemble (S : ∀ i : ι, Finset {v : V // b v = i}) : Finset V := by
  classical
  exact Finset.univ.biUnion (fun i => (S i).image Subtype.val)

private theorem restrict_assemble (S : ∀ i : ι, Finset {v : V // b v = i}) (i : ι) :
    restrict b (assemble b S) i = S i := by
  classical
  ext v
  simp only [restrict, assemble, Finset.mem_subtype, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, u, hu, huv⟩
    have hji : j = i := u.property.symm.trans ((congrArg b huv).trans v.property)
    subst j
    have huv' : u = v := Subtype.ext huv
    simpa [huv'] using hu
  · intro hv
    exact ⟨i, v, hv, rfl⟩

private theorem card_partition (I : Finset V) :
    I.card = ∑ i : ι, (restrict b I i).card := by
  classical
  simpa only [restrict, Finset.card_subtype] using
    (Finset.card_eq_sum_card_fiberwise (f := b) (s := I) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _))

/-- Inclusion maximality is exactly maximality on each adjacency-closed block. -/
theorem maximal_partition
    (hblock : ∀ ⦃u v⦄, G.Adj u v → b u = b v) (I : Finset V) :
    IsMaximalIndep G I ↔
      ∀ i : ι, IsMaximalIndep (G.induce {v | b v = i}) (restrict b I i) := by
  classical
  constructor
  · intro hI i
    constructor
    · intro u hu v hv hne ha
      exact hI.1 u.val (by simpa [restrict] using hu)
        v.val (by simpa [restrict] using hv) (fun h => hne (Subtype.ext h)) ha
    · intro v hv
      obtain ⟨u, hu, ha⟩ := hI.2 v.val (by simpa [restrict] using hv)
      have hub : b u = i := (hblock ha).symm.trans v.property
      exact ⟨⟨u, hub⟩, by simpa [restrict] using hu, ha⟩
  · intro hI
    constructor
    · intro u hu v hv hne ha
      let u' : {v : V // b v = b u} := ⟨u, rfl⟩
      let v' : {v : V // b v = b u} := ⟨v, (hblock ha).symm⟩
      exact (hI (b u)).1 u' (by simpa [restrict, u'] using hu)
        v' (by simpa [restrict, v'] using hv)
        (fun h => hne (congrArg Subtype.val h)) ha
    · intro v hv
      let v' : {w : V // b w = b v} := ⟨v, rfl⟩
      obtain ⟨u, hu, ha⟩ := (hI (b v)).2 v' (by simpa [restrict, v'] using hv)
      exact ⟨u.val, by simpa [restrict] using hu, ha⟩

/-- The spectrum is the full Minkowski sum, with both restriction and vertex-set assembly. -/
theorem spectrum_partition
    (hblock : ∀ ⦃u v⦄, G.Adj u v → b u = b v) (n : ℕ) :
    n ∈ spectrum G ↔ ∃ k : ι → ℕ,
      (∀ i, k i ∈ spectrum (G.induce {v | b v = i})) ∧ ∑ i, k i = n := by
  classical
  constructor
  · rintro ⟨I, hI, hcard⟩
    refine ⟨fun i => (restrict b I i).card, ?_, (card_partition b I).symm.trans hcard⟩
    intro i
    exact ⟨restrict b I i, (maximal_partition b hblock I).mp hI i, rfl⟩
  · rintro ⟨k, hk, hsum⟩
    choose S hS hcard using hk
    refine ⟨assemble b S, ?_, ?_⟩
    · apply (maximal_partition b hblock _).mpr
      intro i
      rw [restrict_assemble]
      exact hS i
    · rw [card_partition b]
      simp_rw [restrict_assemble, hcard]
      exact hsum

/-- A finite union is well-covered exactly when every adjacency-closed block is. -/
theorem wellCovered_partition
    (hblock : ∀ ⦃u v⦄, G.Adj u v → b u = b v) :
    WellCovered G ↔ ∀ i : ι, WellCovered (G.induce {v | b v = i}) := by
  classical
  constructor
  · intro hG i J K hJ hK
    have hex (j : ι) : ∃ S : Finset {v : V // b v = j},
        IsMaximalIndep (G.induce {v | b v = j}) S := by
      obtain ⟨S, hS⟩ := (G.induce {v | b v = j}).maximumIndepSet_exists
      exact ⟨S, (CayleySquare.maximal_iff _ _).mpr (hS.isMaximalIndepSet S)⟩
    choose S hS using hex
    let SJ := Function.update S i J
    let SK := Function.update S i K
    have hSJ : ∀ j, IsMaximalIndep (G.induce {v | b v = j}) (SJ j) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [SJ] using hJ
      · simpa [SJ, hji] using hS j
    have hSK : ∀ j, IsMaximalIndep (G.induce {v | b v = j}) (SK j) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [SK] using hK
      · simpa [SK, hji] using hS j
    have hAJ : IsMaximalIndep G (assemble b SJ) :=
      (maximal_partition b hblock _).mpr (by simpa only [restrict_assemble] using hSJ)
    have hAK : IsMaximalIndep G (assemble b SK) :=
      (maximal_partition b hblock _).mpr (by simpa only [restrict_assemble] using hSK)
    have hcard := hG _ _ hAJ hAK
    simp_rw [card_partition b, restrict_assemble] at hcard
    have hrest : ∑ j ∈ Finset.univ.erase i, (SJ j).card =
        ∑ j ∈ Finset.univ.erase i, (SK j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [SJ, SK, Finset.ne_of_mem_erase hj]
    have hsumJ := Finset.sum_erase_add (s := Finset.univ)
      (f := fun j => (SJ j).card) (Finset.mem_univ i)
    have hsumK := Finset.sum_erase_add (s := Finset.univ)
      (f := fun j => (SK j).card) (Finset.mem_univ i)
    rw [← hsumJ, ← hsumK, hrest] at hcard
    simpa [SJ, SK] using Nat.add_left_cancel hcard
  · intro h I J hI hJ
    rw [card_partition b I, card_partition b J]
    apply Finset.sum_congr rfl
    intro i _
    exact h i _ _ ((maximal_partition b hblock I).mp hI i)
      ((maximal_partition b hblock J).mp hJ i)

/-- Each positive finite-distance power restricts to the corresponding native block power. -/
theorem power_partition
    (hblock : ∀ ⦃u v⦄, G.Adj u v → b u = b v) (d : ℕ) :
    WellCovered (graphPower G d) ↔
      ∀ i : ι, WellCovered (graphPower (G.induce {v | b v = i}) d) := by
  classical
  have hwalk {u v : V} (p : G.Walk u v) : b u = b v := by
    induction p with
    | nil => rfl
    | @cons u v w huv p ih => exact (hblock huv).trans ih
  have hpblock : ∀ ⦃u v⦄, (graphPower G d).Adj u v → b u = b v := by
    intro u v huv
    obtain ⟨_, p, _⟩ := (power_adj_iff_walk d u v).mp huv
    exact hwalk p
  rw [wellCovered_partition b hpblock]
  apply forall_congr'
  intro i
  rw [power_induce]
  intro u v hu huv
  exact (hblock huv).symm.trans hu

end Partition

section Components

variable [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- The component quotient is preserved by every positive faithful distance power. -/
def componentEquiv {d : ℕ} (hd : 1 ≤ d) :
    (graphPower G d).ConnectedComponent ≃ G.ConnectedComponent where
  toFun := Quot.map id (fun u v h => (power_reachable_iff hd u v).mp h)
  invFun := Quot.map id (fun u v h => (power_reachable_iff hd u v).mpr h)
  left_inv c := by
    refine Quot.inductionOn c ?_
    intro v
    rfl
  right_inv c := by
    refine Quot.inductionOn c ?_
    intro v
    rfl

/-- Native component supports inherit exactly the existing connected power semantics. -/
theorem wellCovered_power_components (d : ℕ) :
    WellCovered (graphPower G d) ↔
      ∀ C : G.ConnectedComponent, WellCovered (power C.toSimpleGraph d) := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [power_partition G.connectedComponentMk
    (fun {_ _} h => ConnectedComponent.connectedComponentMk_eq_of_adj h)]
  apply forall_congr'
  intro C
  exact congrArg WellCovered (power_eq_connected C.connected_toSimpleGraph d) |>.to_iff

/-- All positive powers are well-covered exactly when each native component is WCP. -/
theorem all_powers_components :
    (∀ d : ℕ, 1 ≤ d → WellCovered (graphPower G d)) ↔
      ∀ C : G.ConnectedComponent, WCP C.toSimpleGraph := by
  constructor
  · intro h C
    exact ⟨C.connected_toSimpleGraph, fun d hd => (wellCovered_power_components d).mp (h d hd) C⟩
  · intro h d hd
    exact (wellCovered_power_components d).mpr (fun C => (h C).2 d hd)

variable [Fintype G.ConnectedComponent] [DecidableEq G.ConnectedComponent]

/-- The same complete Minkowski formula holds at each positive faithful power. -/
theorem spectrum_power_components {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    n ∈ spectrum (graphPower G d) ↔ ∃ k : G.ConnectedComponent → ℕ,
      (∀ C, k C ∈ spectrum (power C.toSimpleGraph d)) ∧ ∑ C, k C = n := by
  have hb : ∀ ⦃u v⦄, (graphPower G d).Adj u v →
      G.connectedComponentMk u = G.connectedComponentMk v := by
    intro u v h
    exact ConnectedComponent.sound ((power_reachable_iff hd u v).mp h.reachable)
  rw [spectrum_partition G.connectedComponentMk hb]
  apply exists_congr
  intro k
  apply and_congr_left
  intro _
  apply forall_congr'
  intro C
  have hc : graphPower C.toSimpleGraph d = (graphPower G d).induce C.supp :=
    power_induce C.supp (fun {_ _} hu h => C.mem_supp_of_adj_mem_supp hu h) d
  change k C ∈ spectrum ((graphPower G d).induce C.supp) ↔
    k C ∈ spectrum (power C.toSimpleGraph d)
  rw [← hc, power_eq_connected C.connected_toSimpleGraph]
  rfl

end Components

end FiniteDistancePower
