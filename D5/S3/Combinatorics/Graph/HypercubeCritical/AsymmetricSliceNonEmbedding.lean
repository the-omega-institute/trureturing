/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding.claim
   digest: The preregistered asymmetric 24-vertex slice has no finite induced cube embedding. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.Grind

/-! The explicit asymmetric slice has no induced embedding in any finite cube.
This refutes one candidate arising in the 48-vertex component analysis. The actual
parameter classification and the original 258-point Problem 2 are not settled here. -/

set_option autoImplicit false
-- Utility metadata above requires full declaration handles on one line.
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q flip)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

-- Labels: 0 X1, 1 X2, 2 Y1, 3 Y2, 4 a, 5 b, 6 c, 7 d, 8 e, 9 f,
-- 10 low0, 11 low1, 12 low2, 13 low3, 14 low4, 15 low5, 16 low6,
-- 17 u, 18 v, 19 x1, 20 x2, 21 y1, 22 y2, 23 z.
private def edges : List (Fin 24 × Fin 24) :=
  [(23,17),(23,18),(4,17),(4,19),(5,17),(5,20),(6,18),(6,21),
   (7,18),(7,22),(8,19),(8,21),(9,20),(9,22),(0,19),(1,20),
   (2,21),(3,22),(10,4),(10,3),(11,3),(11,2),(12,2),(12,5),
   (13,6),(13,1),(14,1),(14,0),(15,0),(15,7),(16,8),(16,9)]

private def graph : SimpleGraph (Fin 24) where
  Adj a b := a ≠ b ∧ ((a,b) ∈ edges ∨ (b,a) ∈ edges)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a,b) ∈ edges ∨ (b,a) ∈ edges)))

/-- The actual existence obligation, over all finite dimensions, including zero. -/
def claim : Prop :=
  ∃ n : ℕ, ∃ f : Fin 24 → (Fin n → Bool),
    Function.Injective f ∧
      ∀ a b, graph.Adj a b ↔ (hypercube n).Adj (f a) (f b)

private theorem crossing_flip {n : ℕ} {x y : Q n} {i : Fin n}
    (hxy : (hypercube n).Adj x y) (hc : x i ≠ y i) : y = flip x i := by
  obtain ⟨j, rfl⟩ := adjacent_exists_flip hxy
  have hji : j = i := by
    by_contra h
    exact hc (by simp [BalancedCriticalSpectrum.flip, Ne.symm h])
  subst j
  rfl

private theorem flip_adj_iff {n : ℕ} (x y : Q n) (i : Fin n) :
    (hypercube n).Adj (flip x i) (flip y i) ↔ (hypercube n).Adj x y := by
  classical
  change (Finset.univ.filter (fun j => flip x i j ≠ flip y i j)).card = 1 ↔
    (Finset.univ.filter (fun j => x j ≠ y j)).card = 1
  have hs : Finset.univ.filter (fun j => flip x i j ≠ flip y i j) =
      Finset.univ.filter (fun j => x j ≠ y j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip]
    · simp [BalancedCriticalSpectrum.flip, h]
  rw [hs]

-- A clause consists of two actual graph edges, written with useful orientations.
private abbrev Clause := (Fin 24 × Fin 24) × (Fin 24 × Fin 24)

private def valid (p : Clause) : Prop :=
  graph.Adj p.1.1 p.1.2 ∧ graph.Adj p.2.1 p.2.2 ∧
    ((p.1.2 = p.2.1 ∧ p.1.1 ≠ p.2.2) ∨
      (graph.Adj p.1.2 p.2.1 ∧ ¬ graph.Adj p.1.1 p.2.2))

private instance (p : Clause) : Decidable (valid p) := by
  unfold valid
  infer_instance

private def clause (c : Fin 24 → Bool) (p : Clause) : Bool :=
  (c p.1.1 == c p.1.2) || (c p.2.1 == c p.2.2)

-- Only sufficiency is used: neither minimality nor completeness is assumed.
private def paths : List Clause :=
  [((13,1),(1,20)), ((12,2),(2,21)), ((13,6),(6,18)),
   ((13,6),(6,21)), ((18,6),(6,21)), ((16,8),(8,19)),
   ((16,9),(9,22)), ((2,12),(12,5)), ((5,17),(17,23)),
   ((0,19),(19,4)), ((1,20),(20,5)), ((1,20),(20,9)),
   ((2,21),(21,8)), ((3,22),(22,7)), ((17,23),(23,18)),
   ((17,23),(18,6)), ((10,4),(17,23)), ((19,4),(17,23)),
   ((17,4),(19,0)), ((12,5),(17,23)), ((20,5),(17,23)),
   ((12,5),(20,1)), ((17,5),(20,1)), ((13,6),(18,23)),
   ((21,6),(18,23)), ((13,6),(21,2)), ((15,7),(18,23)),
   ((22,7),(18,23)), ((18,7),(22,3)), ((16,8),(21,2)),
   ((16,9),(20,1)), ((13,1),(20,9)), ((12,2),(21,6)),
   ((12,2),(21,8)), ((3,10),(4,17)), ((2,12),(5,17)),
   ((2,12),(5,20)), ((1,13),(6,18)), ((1,13),(6,21)),
   ((6,13),(1,20)), ((0,15),(7,18)), ((9,16),(8,19)),
   ((8,16),(9,22))]

private theorem paths_valid : paths.all (fun p => decide (valid p)) = true := by
  decide +kernel

private def cnf (c : Fin 24 → Bool) : Bool := paths.all (clause c)

private theorem clause_necessary {n : ℕ} (f : Fin 24 → Q n)
    (hf : Function.Injective f)
    (he : ∀ a b, graph.Adj a b ↔ (hypercube n).Adj (f a) (f b))
    (i : Fin n) (p : Clause) (hp : valid p) :
    clause (fun a => f a i) p = true := by
  rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change graph.Adj a b ∧ graph.Adj c d ∧
    ((b = c ∧ a ≠ d) ∨ (graph.Adj b c ∧ ¬ graph.Adj a d)) at hp
  change ((f a i == f b i) || (f c i == f d i)) = true
  by_cases h1 : f a i = f b i
  · simp [h1]
  by_cases h2 : f c i = f d i
  · simp [h2]
  exfalso
  obtain ⟨hab, hcd, hshape⟩ := hp
  have hba : f a = flip (f b) i :=
    crossing_flip ((he a b).mp hab).symm (Ne.symm h1)
  have hdc : f d = flip (f c) i := crossing_flip ((he c d).mp hcd) h2
  rcases hshape with ⟨hbc, had⟩ | ⟨hbc, had⟩
  · apply had
    apply hf
    rw [hba, hdc, hbc]
  · apply had
    apply (he a d).mpr
    rw [hba, hdc]
    exact (flip_adj_iff (f b) (f c) i).mpr ((he b c).mp hbc)

private theorem cnf_necessary {n : ℕ} (f : Fin 24 → Q n)
    (hf : Function.Injective f)
    (he : ∀ a b, graph.Adj a b ↔ (hypercube n).Adj (f a) (f b))
    (i : Fin n) : cnf (fun a => f a i) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  exact clause_necessary f hf he i p
    (of_decide_eq_true ((List.all_eq_true.mp paths_valid) p hp))

-- A finite propositional implication, with ordinary kernel proof terms from grind.
-- Static path reduction exposes the Boolean constraints directly.
private theorem cut_parity (c : Fin 24 → Bool) (h : cnf c = true) :
    Bool.xor (Bool.xor (c 17 != c 23) (c 1 != c 20)) (c 12 != c 2) = false := by
  simp only [cnf, paths, clause, List.all_cons, List.all_nil] at h
  grind

private theorem edge_color {n : ℕ} {x y : Q n} {j : Fin n}
    (h : y = flip x j) (i : Fin n) : (x i != y i) = decide (i = j) := by
  subst y
  by_cases hij : i = j
  · subst i
    cases hx : x j <;> simp [BalancedCriticalSpectrum.flip_apply_same, hx]
  · simp [BalancedCriticalSpectrum.flip, hij]

/-- The explicit saved 24-vertex, 32-edge graph has no induced embedding in any Qn. -/
theorem result : ¬ claim := by
  rintro ⟨n, f, hf, he⟩
  obtain ⟨i, hi⟩ := adjacent_exists_flip
    ((he 17 23).mp (by decide +kernel : graph.Adj 17 23))
  obtain ⟨j, hj⟩ := adjacent_exists_flip
    ((he 1 20).mp (by decide +kernel : graph.Adj 1 20))
  obtain ⟨k, hk⟩ := adjacent_exists_flip
    ((he 12 2).mp (by decide +kernel : graph.Adj 12 2))
  have hp (t : Fin n) :
      Bool.xor (Bool.xor (decide (t = i)) (decide (t = j)))
        (decide (t = k)) = false := by
    have h := cut_parity (fun a => f a t) (cnf_necessary f hf he t)
    rw [edge_color hi t, edge_color hj t, edge_color hk t] at h
    exact h
  by_cases hij : i = j
  · have h := hp k
    simp [hij] at h
  · have hik : i = k := by
      by_contra hik
      have h := hp i
      simp [hij, hik] at h
    subst k
    have hji : j ≠ i := Ne.symm hij
    have h := hp j
    simp [hji] at h

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding
