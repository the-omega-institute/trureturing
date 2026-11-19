import D5.S3.Combinatorics.Graph.Hypercube
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TriplePartitionOrbits

/-! Simultaneous normalization of two Gray placements by a single cube symmetry. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm

open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open Q9TriplePartitionOrbits (standardLabels secondLabels classify_triple_partitions)

abbrev Vertex := Fin 9 → Bool

/-- From the center, a point differs in two or three coordinates, with at
most one differing coordinate in each of the three blocks. -/
def Fits (block : Fin 9 → Fin 3) (center x : Vertex) : Prop :=
  (∀ b, (univ.filter (fun i => block i = b ∧ x i ≠ center i)).card ≤ 1) ∧
    2 ≤ hammingDist x center

instance (block : Fin 9 → Fin 3) (center x : Vertex) : Decidable (Fits block center x) :=
  inferInstanceAs (Decidable (_ ∧ _))

def placement (block : Fin 9 → Fin 3) (center : Vertex) : Finset Vertex :=
  univ.filter (Fits block center)

@[simp] theorem mem_placement {block : Fin 9 → Fin 3} {center x : Vertex} :
    x ∈ placement block center ↔ Fits block center x := by
  simp [placement]

def origin : Vertex := fun _ => false

/-- Read coordinates in the order specified by `σ`, using differences from
the center as the new Boolean coordinates. -/
def normalize (σ : Equiv.Perm (Fin 9)) (center : Vertex) : Vertex ≃ Vertex where
  toFun x i := x (σ i) != center (σ i)
  invFun x i := x (σ.symm i) != center i
  left_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    cases x i <;> cases center i <;> rfl
  right_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply]
    cases x i <;> cases center (σ i) <;> rfl

private theorem count_reindex {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Equiv.Perm I) (P : I → Prop) [DecidablePred P] :
    ((univ : Finset I).filter (fun i => P (σ i))).card = (univ.filter P).card := by
  apply card_bij (fun i _ => σ i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact σ.injective hij
  · intro j hj
    exact ⟨σ.symm j, mem_filter.mpr ⟨mem_univ _, by simpa using (mem_filter.mp hj).2⟩,
      σ.apply_symm_apply j⟩

private theorem normalize_ne (σ : Equiv.Perm (Fin 9)) (center x y : Vertex) (i : Fin 9) :
    normalize σ center x i ≠ normalize σ center y i ↔ x (σ i) ≠ y (σ i) := by
  change ((x (σ i) != center (σ i)) ≠ (y (σ i) != center (σ i))) ↔ _
  cases x (σ i) <;> cases y (σ i) <;> cases center (σ i) <;> decide

/-- The same coordinate change preserves every Hamming distance. -/
theorem normalize_hammingDist (σ : Equiv.Perm (Fin 9)) (center x y : Vertex) :
    hammingDist (normalize σ center x) (normalize σ center y) = hammingDist x y := by
  unfold hammingDist
  simp_rw [normalize_ne]
  exact count_reindex σ (fun i => x i ≠ y i)

private theorem normalize_center (σ : Equiv.Perm (Fin 9)) (center : Vertex) :
    normalize σ center center = origin := by
  funext i
  change (center (σ i) != center (σ i)) = false
  cases center (σ i) <;> rfl

/-- Reindexing a placement reindexes its center and its coordinate blocks. -/
theorem normalize_placement
    (σ : Equiv.Perm (Fin 9)) (p : Equiv.Perm (Fin 3))
    (block standard : Fin 9 → Fin 3) (hblock : ∀ i, block (σ i) = p (standard i))
    (base center : Vertex) :
    (placement block center).map (normalize σ base).toEmbedding =
      placement standard (normalize σ base center) := by
  have hcount (x : Vertex) (b : Fin 3) :
      (univ.filter (fun i => standard i = b ∧
        normalize σ base x i ≠ normalize σ base center i)).card =
      (univ.filter (fun i => block i = p b ∧ x i ≠ center i)).card := by
    rw [← count_reindex σ (fun i => block i = p b ∧ x i ≠ center i)]
    simp_rw [hblock, p.injective.eq_iff, normalize_ne]
  ext y
  obtain ⟨x, rfl⟩ := (normalize σ base).surjective y
  simp only [mem_map, Equiv.toEmbedding_apply, Equiv.apply_eq_iff_eq, exists_eq_right,
    mem_placement, Fits, hcount, normalize_hammingDist]
  constructor
  · rintro ⟨h, hd⟩
    exact ⟨fun b => h (p b), hd⟩
  · rintro ⟨h, hd⟩
    refine ⟨fun b => ?_, hd⟩
    obtain ⟨i, rfl⟩ := p.surjective b
    exact h i

/-- Two Gray placements can be normalized simultaneously. Their first
center becomes the origin, the relative center stays free, and their blocks
become one of the five pairs from the intersection-matrix classification. -/
theorem normalize_pair
    (first second : Fin 9 → Fin 3) (c d : Vertex)
    (hfirst : ∀ b, (univ.filter (fun i => first i = b)).card = 3)
    (hsecond : ∀ b, (univ.filter (fun i => second i = b)).card = 3) :
    ∃ (e : hypercube 9 ≃g hypercube 9) (k : Fin 5) (t : Vertex),
      (∀ x y, hammingDist (e x) (e y) = hammingDist x y) ∧
      (placement first c).map e.toEquiv.toEmbedding = placement standardLabels origin ∧
      (placement second d).map e.toEquiv.toEmbedding = placement (secondLabels k) t := by
  obtain ⟨k, p, q, σ, h⟩ := classify_triple_partitions first second hfirst hsecond
  let e : hypercube 9 ≃g hypercube 9 :=
    { toEquiv := normalize σ c
      map_rel_iff' := by
        intro x y
        change hammingDist (normalize σ c x) (normalize σ c y) = 1 ↔ hammingDist x y = 1
        rw [normalize_hammingDist] }
  refine ⟨e, k, normalize σ c d, normalize_hammingDist σ c, ?_, ?_⟩
  · simpa only [e, normalize_center] using
      normalize_placement σ p first standardLabels (fun i => (h i).1) c c
  · exact normalize_placement σ q second (secondLabels k) (fun i => (h i).2) c d

#print axioms normalize_pair

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm
