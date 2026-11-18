/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.claim; result=D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.result; claim=D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.claim
   digest: The four-vertex path followed by the star refutes the ordered connected forcing crossing. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree

/-! The mandatory low-index block in Problem 5.3 fails at singleton sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite

/-- Connectivity is required only of the initially induced subgraph. -/
def connectedForcing {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected ∧ IsZeroForcing G (S : Set V)

/-- The number of actual cardinality-i connected zero forcing subsets. -/
noncomputable def coefficient {V : Type*} [Fintype V] (G : SimpleGraph V) (i : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset V => S.card = i ∧ connectedForcing G S).card

/-- The source's number of degree-one vertices, including all finite tree orders. -/
noncomputable def leafCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card {v : V // Nat.card {w : V // G.Adj v w} = 1}

/-- The complete fixed ordered assertion of Mukherjee--Ray, Problem 5.3. -/
def claim : Prop :=
  ∀ (n p q : ℕ) (V W : Type) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    G.IsTree → H.IsTree → Fintype.card V = n → Fintype.card W = n →
    leafCount G = p → leafCount H = q →
    ∃ l : ℤ, 1 ≤ l ∧ l ≤ (n : ℤ) ∧
      ∀ i : ℤ, (1 ≤ i ∧ i ≤ l → coefficient G i.toNat ≤ coefficient H i.toNat) ∧
        (l + 1 ≤ i ∧ i ≤ (n : ℤ) → coefficient H i.toNat ≤ coefficient G i.toNat)

private def star : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

private instance : DecidableRel star.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ = 0 ∨ _ = 0)))

private theorem singleton_connected {V : Type*}
    (G : SimpleGraph V) (a : V) : (G.induce (({a} : Finset V) : Set V)).Connected := by
  classical
  have : Nonempty {v : V // v ∈ (({a} : Finset V) : Set V)} := ⟨⟨a, by simp⟩⟩
  have : Subsingleton {v : V // v ∈ (({a} : Finset V) : Set V)} :=
    ⟨fun x y => Subtype.ext (by
      have hx : x.val = a := by simpa using x.property
      have hy : y.val = a := by simpa using y.property
      exact hx.trans hy.symm)⟩
  exact Connected.of_subsingleton

private theorem path_singleton (a : Fin 4) :
    IsZeroForcing (pathGraph 4) (({a} : Finset (Fin 4)) : Set _) ↔ a = 0 ∨ a = 3 := by
  constructor
  · intro hz
    by_contra ha
    have hc : ∀ a : Fin 4, ¬ (a = 0 ∨ a = 3) →
        ∃ (F : Finset (Fin 4)) (v : Fin 4),
          IsFort (pathGraph 4) F ∧ Disjoint ({a} : Finset _) F ∧ v ∈ F := by
      simp only [IsFort, finiteNeighbors, pathGraph_adj]
      decide
    obtain ⟨F, v, hf, hd, hv⟩ := hc a ha
    exact IsFort.not_black_of_disjoint _ _ _ hf hd hv (hz v)
  · rintro (rfl | rfl)
    · have h0 : Black (pathGraph 4) (({0} : Finset (Fin 4)) : Set _) 0 := .init (by simp)
      have h1 : Black (pathGraph 4) (({0} : Finset (Fin 4)) : Set _) 1 := by
        apply Black.force h0 (by decide)
        intro x hx hne
        fin_cases x <;> simp_all [pathGraph_adj]
      have h2 : Black (pathGraph 4) (({0} : Finset (Fin 4)) : Set _) 2 := by
        apply Black.force h1 (by decide)
        intro x hx hne
        fin_cases x <;> simp_all [pathGraph_adj]
      have h3 : Black (pathGraph 4) (({0} : Finset (Fin 4)) : Set _) 3 := by
        apply Black.force h2 (by decide)
        intro x hx hne
        fin_cases x <;> simp_all [pathGraph_adj]
      intro v
      fin_cases v <;> assumption
    · have h3 : Black (pathGraph 4) (({3} : Finset (Fin 4)) : Set _) 3 := .init (by simp)
      have h2 : Black (pathGraph 4) (({3} : Finset (Fin 4)) : Set _) 2 := by
        apply Black.force h3 (by decide)
        intro x hx hne
        fin_cases x <;> simp_all [pathGraph_adj]
      have h1 : Black (pathGraph 4) (({3} : Finset (Fin 4)) : Set _) 1 := by
        apply Black.force h2 (by decide)
        intro x hx hne
        fin_cases x <;> simp_all [pathGraph_adj]
      have h0 : Black (pathGraph 4) (({3} : Finset (Fin 4)) : Set _) 0 := by
        apply Black.force h1 (by decide)
        intro x hx hne
        fin_cases x <;> simp_all [pathGraph_adj]
      intro v
      fin_cases v <;> assumption

private theorem star_singleton (a : Fin 4) :
    ¬ IsZeroForcing star (({a} : Finset (Fin 4)) : Set _) := by
  have hc : ∀ a : Fin 4, ∃ (F : Finset (Fin 4)) (v : Fin 4),
      IsFort star F ∧ Disjoint ({a} : Finset _) F ∧ v ∈ F := by
    simp only [IsFort, finiteNeighbors, star]
    decide
  obtain ⟨F, v, hf, hd, hv⟩ := hc a
  intro hz
  exact IsFort.not_black_of_disjoint _ _ _ hf hd hv (hz v)

/-- The source's published path/star pair violates the mandatory size-one comparison. -/
theorem result : ¬ claim := by
  classical
  intro h
  have ht : star.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    constructor
    · apply Connected.of_isUniversal (v := 0)
      intro v hv
      exact ⟨hv, Or.inl rfl⟩
    · rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card]
      decide
  have hp : coefficient (pathGraph 4) 1 = 2 := by
    have he : (Finset.univ.filter fun S : Finset (Fin 4) =>
        S.card = 1 ∧ connectedForcing (pathGraph 4) S) = {{0}, {3}} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hc, hz⟩
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        rcases (path_singleton a).mp hz.2 with rfl | rfl <;> simp
      · rintro (rfl | rfl) <;>
          exact ⟨by decide, singleton_connected _ _, (path_singleton _).mpr (by simp)⟩
    simp [coefficient, he]
  have hs : coefficient star 1 = 0 := by
    have he : (Finset.univ.filter fun S : Finset (Fin 4) =>
        S.card = 1 ∧ connectedForcing star S) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hm
      obtain ⟨hc, hz⟩ := (Finset.mem_filter.mp hm).2
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      exact star_singleton a hz.2
    simp [coefficient, he]
  obtain ⟨l, hl, hln, hi⟩ := h 4 (leafCount (pathGraph 4)) (leafCount star)
    (Fin 4) (Fin 4) (pathGraph 4) star (isTree_pathGraph_add_one 3) ht rfl rfl rfl rfl
  have bad := (hi 1).1 ⟨by decide, hl⟩
  norm_num [hp, hs] at bad

#print axioms result

end D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation
