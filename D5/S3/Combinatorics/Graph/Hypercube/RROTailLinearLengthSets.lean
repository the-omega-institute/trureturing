/- GID: D5/S3/Combinatorics/Graph/Hypercube/RROTailLinearLengthSets
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/RROTailLinearLengthSets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boolean cube fibres have linear word length and common-prefix edge contacts. -/

import D5.S3.Combinatorics.Graph.Hypercube

noncomputable section

namespace D5.S3.Combinatorics.Graph.Hypercube.RROTailLinearLengthSets

open scoped Classical
open D5.S3.Combinatorics.Graph.Hypercube

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev Vertex (k : ℕ) := Fin k → Bool
abbrev Cube (k : ℕ) := hypercube k
abbrev Edge (k : ℕ) := ↥((Cube k).edgeFinset)

def appendBit {m : ℕ} (p : Fin m → Bool) (b : Bool) : Fin (m + 1) → Bool :=
  Fin.lastCases b p

@[simp] theorem appendBit_castSucc {m : ℕ} (p : Fin m → Bool) (b : Bool) (i : Fin m) :
    appendBit p b i.castSucc = p i := by
  exact Fin.lastCases_castSucc i

@[simp] theorem appendBit_last {m : ℕ} (p : Fin m → Bool) (b : Bool) :
    appendBit p b (Fin.last m) = b := by
  exact Fin.lastCases_last

def vertexRank {k : ℕ} : Vertex k → Fin (Fintype.card (Vertex k)) :=
  Fintype.equivFin (Vertex k)

def endpointBit {k : ℕ} (x y : Vertex k) : Bool :=
  decide (vertexRank x < vertexRank y)

lemma endpointBit_swap {k : ℕ} {x y : Vertex k} (hxy : x ≠ y) :
    endpointBit x y ≠ endpointBit y x := by
  unfold endpointBit
  have hr : vertexRank x ≠ vertexRank y := by
    intro h
    exact hxy ((Fintype.equivFin (Vertex k)).injective h)
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · simp [hlt, not_lt_of_ge hlt.le]
  · simp [hgt, not_lt_of_ge hgt.le]

lemma edge_card (k : ℕ) : Fintype.card (Edge k) = k * 2 ^ (k - 1) := by
  rw [show Fintype.card (Edge k) = (Cube k).edgeFinset.card by
    exact Fintype.card_coe _]
  exact hypercube_edge_count k

lemma prefix_card_le (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card (Edge k) ≤ Fintype.card (Fin (k - 1 + Nat.clog 2 k) → Bool) := by
  rw [edge_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hpow : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by decide) k
  have hmul := Nat.mul_le_mul_right (2 ^ (k - 1)) hpow
  rw [← pow_add] at hmul
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul

def prefixEmbedding (k : ℕ) (hk : 1 ≤ k) :
    Edge k ↪ (Fin (k - 1 + Nat.clog 2 k) → Bool) := by
  let hcard := prefix_card_le k hk
  let eFin := Fintype.equivFin (Edge k)
  let pFin := Fintype.equivFin (Fin (k - 1 + Nat.clog 2 k) → Bool)
  exact
    { toFun := fun e => pFin.symm (Fin.castLE hcard (eFin e))
      inj' := by
        intro a b hab
        apply eFin.injective
        apply Fin.castLE_injective hcard
        exact (pFin.symm).injective hab }

def edgeOfNeighbor {k : ℕ} {x : Vertex k} (y : (Cube k).neighborSet x) : Edge k :=
  ⟨s(x, y.1), (SimpleGraph.mem_edgeFinset).2
    ((SimpleGraph.mem_edgeSet (Cube k)).2 ((SimpleGraph.mem_neighborSet (Cube k) x y.1).mp y.2))⟩

lemma edgeOfNeighbor_injective {k : ℕ} {x : Vertex k} :
    Function.Injective (edgeOfNeighbor (x := x)) := by
  intro y z h
  apply Subtype.ext
  have hs : s(x, y.1) = s(x, z.1) := congrArg Subtype.val h
  rcases (Sym2.eq_iff.mp hs) with h | h
  · exact h.2
  · have hxy : x = z.1 := h.1
    have hyx : y.1 = x := h.2
    exact False.elim ((Cube k).loopless.irrefl x (by simpa [hxy, hyx] using
      ((SimpleGraph.mem_neighborSet (Cube k) x y.1).mp y.2)))

def fibreWord {k : ℕ} (hk : 1 ≤ k) (x : Vertex k)
    (y : (Cube k).neighborSet x) : Fin (k - 1 + Nat.clog 2 k + 1) → Bool :=
  appendBit (prefixEmbedding k hk (edgeOfNeighbor y)) (endpointBit x y.1)

def fibre (k : ℕ) (hk : 1 ≤ k) (x : Vertex k) :
    Finset (Fin (k - 1 + Nat.clog 2 k + 1) → Bool) :=
  (Finset.univ : Finset ((Cube k).neighborSet x)).image (fibreWord hk x)

lemma neighbour_ne {k : ℕ} {x : Vertex k} (y : (Cube k).neighborSet x) : y.1 ≠ x := by
  intro h
  exact (Cube k).loopless.irrefl x (by simpa [h] using
    ((SimpleGraph.mem_neighborSet (Cube k) x y.1).mp y.2))

lemma fibreWord_injective {k : ℕ} (hk : 1 ≤ k) (x : Vertex k) :
    Function.Injective (fibreWord hk x) := by
  intro y z h
  have hp : prefixEmbedding k hk (edgeOfNeighbor y) =
      prefixEmbedding k hk (edgeOfNeighbor z) := by
    apply funext
    intro i
    simpa [fibreWord] using congrFun h i.castSucc
  have he : edgeOfNeighbor y = edgeOfNeighbor z :=
    (prefixEmbedding k hk).injective hp
  exact edgeOfNeighbor_injective he

lemma fibre_card {k : ℕ} (hk : 1 ≤ k) (x : Vertex k) : (fibre k hk x).card = k := by
  rw [fibre, Finset.card_image_of_injective _ (fibreWord_injective hk x)]
  change Fintype.card ((Cube k).neighborSet x) = k
  rw [SimpleGraph.card_neighborSet_eq_degree, (hypercube_regular k).degree_eq]

def contact (m : ℕ) (u v : Fin (m + 1) → Bool) : Prop :=
  ∃ p : Fin m → Bool,
    (u = appendBit p false ∧ v = appendBit p true) ∨
      (u = appendBit p true ∧ v = appendBit p false)

lemma fibre_contact {k : ℕ} (hk : 1 ≤ k) {x y : Vertex k}
    (hxy : (Cube k).Adj x y) :
    ∃ u ∈ fibre k hk x, ∃ v ∈ fibre k hk y,
      contact (k - 1 + Nat.clog 2 k) u v := by
  let yx : (Cube k).neighborSet x := ⟨y, (SimpleGraph.mem_neighborSet (Cube k) x y).2 hxy⟩
  let xy : (Cube k).neighborSet y := ⟨x, (SimpleGraph.mem_neighborSet (Cube k) y x).2 ((Cube k).symm.symm x y hxy)⟩
  refine ⟨fibreWord hk x yx, ?_, fibreWord hk y xy, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨yx, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨xy, Finset.mem_univ _, rfl⟩
  · refine ⟨prefixEmbedding k hk (edgeOfNeighbor yx), ?_⟩
    have hedge : edgeOfNeighbor xy = edgeOfNeighbor yx := by
      apply Subtype.ext
      apply (Sym2.eq_iff).2
      exact Or.inr ⟨rfl, rfl⟩
    by_cases hlt : vertexRank x < vertexRank y
    · right
      constructor
      · change appendBit (prefixEmbedding k hk (edgeOfNeighbor yx)) (endpointBit x y) = _
        simp [endpointBit, hlt]
      · have hnot : ¬ vertexRank y < vertexRank x := not_lt_of_ge hlt.le
        change appendBit (prefixEmbedding k hk (edgeOfNeighbor xy)) (endpointBit y x) = _
        rw [hedge]
        simp [endpointBit, hlt, hnot]
    · left
      have hne : vertexRank x ≠ vertexRank y := by
        intro h
        change (Fintype.equivFin (Vertex k)) x = (Fintype.equivFin (Vertex k)) y at h
        exact neighbour_ne yx ((Fintype.equivFin (Vertex k)).injective h.symm)
      have hgt : vertexRank y < vertexRank x := lt_of_le_of_ne
        (le_of_not_gt hlt) hne.symm
      constructor
      · change appendBit (prefixEmbedding k hk (edgeOfNeighbor yx)) (endpointBit x y) = _
        simp [endpointBit, hlt, hgt]
      · change appendBit (prefixEmbedding k hk (edgeOfNeighbor xy)) (endpointBit y x) = _
        rw [hedge]
        simp [endpointBit, hlt, hgt]

theorem proposition_36_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (fibres : Vertex k → Finset (Fin (k - 1 + Nat.clog 2 k + 1) → Bool)),
      k - 1 + Nat.clog 2 k + 1 = k + Nat.clog 2 k ∧
      (∀ x, (fibres x).card = k) ∧
      (∀ ⦃x y⦄, x ≠ y → Disjoint (fibres x) (fibres y)) ∧
      (∀ ⦃x y⦄, (Cube k).Adj x y →
        ∃ u ∈ fibres x, ∃ v ∈ fibres y,
          contact (k - 1 + Nat.clog 2 k) u v) := by
  classical
  refine ⟨fibre k hk, by omega, ?_, ?_, ?_⟩
  · intro x
    exact fibre_card hk x
  · intro x y hxy
    rw [Finset.disjoint_left]
    intro w hx hy
    rcases Finset.mem_image.mp hx with ⟨u, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨v, _, hword⟩
    have hp : prefixEmbedding k hk (edgeOfNeighbor u) =
        prefixEmbedding k hk (edgeOfNeighbor v) := by
      apply funext
      intro i
      simpa [fibreWord] using (congrFun hword i.castSucc).symm
    have he : edgeOfNeighbor u = edgeOfNeighbor v := (prefixEmbedding k hk).injective hp
    have hs : s(x, u.1) = s(y, v.1) := congrArg Subtype.val he
    rcases (Sym2.eq_iff.mp hs) with h | h
    · exact hxy (h.1 ▸ rfl)
    · have hbit := congrFun hword (Fin.last (k - 1 + Nat.clog 2 k))
      have hne := endpointBit_swap (neighbour_ne u)
      apply hne
      simpa [fibreWord, h.1, h.2] using hbit
  · intro x y hxy
    exact fibre_contact hk hxy

end D5.S3.Combinatorics.Graph.Hypercube.RROTailLinearLengthSets
