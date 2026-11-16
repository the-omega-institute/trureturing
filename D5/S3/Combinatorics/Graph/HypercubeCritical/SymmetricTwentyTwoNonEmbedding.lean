/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding.claim
   digest: The explicit 22-vertex symmetric-parameter candidate has no finite induced cube embedding. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.Grind

/-! This explicit 22-vertex, 29-edge graph has no induced embedding in any
finite cube. The full (11,11;4,4) parameter classification and the original
258-point problem remain separate obligations. -/

set_option autoImplicit false
-- Utility metadata above requires full declaration handles on one line.
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoNonEmbedding

open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q flip)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private crossing_flip flip_adj_iff edge_color from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

-- Labels 0..10: 02, 03, 05, 12, 13, 14, 15, 24, 34, 35, 45.
-- Labels 11..21: the matching vertices 01|24|35, 02|13|45, 02|14|35,
-- 02|15|34, 03|12|45, 03|14|25, 03|15|24, 04|12|35, 05|12|34,
-- 05|13|24, 05|14|23, in that order.
private def edges : List (Fin 22 × Fin 22) :=
  [(0,12),(0,13),(0,14),(1,15),(1,16),(1,17),
   (2,19),(2,20),(2,21),(3,15),(3,18),(3,19),
   (4,12),(4,20),(5,13),(5,16),(5,21),(6,14),
   (6,17),(7,11),(7,17),(7,20),(8,14),(8,19),
   (9,11),(9,13),(9,18),(10,12),(10,15)]

private def graph : SimpleGraph (Fin 22) where
  Adj a b := a ≠ b ∧ ((a,b) ∈ edges ∨ (b,a) ∈ edges)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a,b) ∈ edges ∨ (b,a) ∈ edges)))

/-- The actual existence obligation, over all finite dimensions, including zero. -/
def claim : Prop :=
  ∃ n : ℕ, ∃ f : Fin 22 → (Fin n → Bool),
    Function.Injective f ∧
      ∀ a b, graph.Adj a b ↔ (hypercube n).Adj (f a) (f b)

-- A clause consists of two actual graph edges, written with useful orientations.
private abbrev Clause := (Fin 22 × Fin 22) × (Fin 22 × Fin 22)

private def valid (p : Clause) : Prop :=
  graph.Adj p.1.1 p.1.2 ∧ graph.Adj p.2.1 p.2.2 ∧
    ((p.1.2 = p.2.1 ∧ p.1.1 ≠ p.2.2) ∨
      (graph.Adj p.1.2 p.2.1 ∧ ¬ graph.Adj p.1.1 p.2.2))

private instance (p : Clause) : Decidable (valid p) := by
  unfold valid
  infer_instance

private def clause (c : Fin 22 → Bool) (p : Clause) : Bool :=
  (c p.1.1 == c p.1.2) || (c p.2.1 == c p.2.2)

-- Fifty two-edge and eighty-four three-edge path clauses.
-- Only sufficiency is used; the proof does not assume a cut or mask catalog.
private def paths : List Clause :=
  [((12,0),(0,13)), ((12,0),(0,14)), ((0,12),(12,4)), ((0,12),(4,20)),
   ((12,0),(13,5)), ((12,0),(14,6)), ((12,0),(14,8)), ((12,0),(13,9)),
   ((0,12),(12,10)), ((0,12),(10,15)), ((13,0),(0,14)), ((13,0),(12,4)),
   ((0,13),(13,5)), ((0,13),(5,16)), ((0,13),(5,21)), ((13,0),(14,6)),
   ((13,0),(14,8)), ((0,13),(9,11)), ((0,13),(13,9)), ((0,13),(9,18)),
   ((13,0),(12,10)), ((14,0),(12,4)), ((14,0),(13,5)), ((0,14),(14,6)),
   ((0,14),(6,17)), ((0,14),(14,8)), ((0,14),(8,19)), ((14,0),(13,9)),
   ((14,0),(12,10)), ((15,1),(1,16)), ((15,1),(1,17)), ((1,15),(15,3)),
   ((1,15),(3,18)), ((1,15),(3,19)), ((15,1),(16,5)), ((15,1),(17,6)),
   ((15,1),(17,7)), ((1,15),(10,12)), ((1,15),(15,10)), ((16,1),(1,17)),
   ((16,1),(15,3)), ((1,16),(5,13)), ((1,16),(16,5)), ((1,16),(5,21)),
   ((16,1),(17,6)), ((16,1),(17,7)), ((16,1),(15,10)), ((17,1),(15,3)),
   ((17,1),(16,5)), ((1,17),(6,14)), ((1,17),(17,6)), ((1,17),(7,11)),
   ((1,17),(17,7)), ((1,17),(7,20)), ((17,1),(15,10)), ((19,2),(2,20)),
   ((19,2),(2,21)), ((2,19),(3,15)), ((2,19),(3,18)), ((2,19),(19,3)),
   ((19,2),(20,4)), ((19,2),(21,5)), ((19,2),(20,7)), ((2,19),(8,14)),
   ((2,19),(19,8)), ((20,2),(2,21)), ((20,2),(19,3)), ((2,20),(4,12)),
   ((2,20),(20,4)), ((20,2),(21,5)), ((2,20),(7,11)), ((2,20),(7,17)),
   ((2,20),(20,7)), ((20,2),(19,8)), ((21,2),(19,3)), ((21,2),(20,4)),
   ((2,21),(5,13)), ((2,21),(5,16)), ((2,21),(21,5)), ((21,2),(20,7)),
   ((21,2),(19,8)), ((15,3),(3,18)), ((15,3),(3,19)), ((15,3),(19,8)),
   ((15,3),(18,9)), ((3,15),(10,12)), ((3,15),(15,10)), ((18,3),(3,19)),
   ((18,3),(19,8)), ((3,18),(9,11)), ((3,18),(9,13)), ((3,18),(18,9)),
   ((18,3),(15,10)), ((3,19),(8,14)), ((3,19),(19,8)), ((19,3),(18,9)),
   ((19,3),(15,10)), ((12,4),(4,20)), ((12,4),(20,7)), ((4,12),(12,10)),
   ((4,12),(10,15)), ((4,20),(7,11)), ((4,20),(7,17)), ((4,20),(20,7)),
   ((20,4),(12,10)), ((13,5),(5,16)), ((13,5),(5,21)), ((5,13),(9,11)),
   ((5,13),(13,9)), ((5,13),(9,18)), ((16,5),(5,21)), ((16,5),(13,9)),
   ((21,5),(13,9)), ((14,6),(6,17)), ((14,6),(17,7)), ((6,14),(14,8)),
   ((6,14),(8,19)), ((6,17),(7,11)), ((6,17),(17,7)), ((6,17),(7,20)),
   ((17,6),(14,8)), ((11,7),(7,17)), ((11,7),(7,20)), ((7,11),(11,9)),
   ((7,11),(9,13)), ((7,11),(9,18)), ((17,7),(7,20)), ((17,7),(11,9)),
   ((20,7),(11,9)), ((14,8),(8,19)), ((11,9),(9,13)), ((11,9),(9,18)),
   ((13,9),(9,18)), ((12,10),(10,15))]

private theorem paths_valid : paths.all (fun p => decide (valid p)) = true := by
  decide +kernel

private def cnf (c : Fin 22 → Bool) : Bool := paths.all (clause c)

private theorem clause_necessary {n : ℕ} (f : Fin 22 → Q n)
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

private theorem cnf_necessary {n : ℕ} (f : Fin 22 → Q n)
    (hf : Function.Injective f)
    (he : ∀ a b, graph.Adj a b ↔ (hypercube n).Adj (f a) (f b))
    (i : Fin n) : cnf (fun a => f a i) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  exact clause_necessary f hf he i p
    (of_decide_eq_true ((List.all_eq_true.mp paths_valid) p hp))

-- A finite propositional implication, with ordinary kernel proof terms from grind.
-- Static path reduction exposes the Boolean constraints directly.
private theorem cut_parity (c : Fin 22 → Bool) (h : cnf c = true) :
    Bool.xor (Bool.xor (c 0 != c 12) (c 5 != c 16)) (c 9 != c 18) = false := by
  simp only [cnf, paths, clause, List.all_cons, List.all_nil] at h
  grind

/-- The explicit saved 22-vertex, 29-edge graph has no induced embedding in any Qn. -/
theorem result : ¬ claim := by
  rintro ⟨n, f, hf, he⟩
  obtain ⟨i, hi⟩ := adjacent_exists_flip
    ((he 0 12).mp (by decide +kernel : graph.Adj 0 12))
  obtain ⟨j, hj⟩ := adjacent_exists_flip
    ((he 5 16).mp (by decide +kernel : graph.Adj 5 16))
  obtain ⟨k, hk⟩ := adjacent_exists_flip
    ((he 9 18).mp (by decide +kernel : graph.Adj 9 18))
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

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoNonEmbedding
