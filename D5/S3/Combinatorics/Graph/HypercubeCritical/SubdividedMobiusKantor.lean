/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor.claim
   digest: The subdivided Mobius-Kantor slice has no finite induced cube embedding. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.Grind

/-! The graph obtained by subdividing all eight rungs between the step-one
and step-three eight-cycles has no induced embedding in any finite cube.
This is one structural branch of the (12,12;4,4) Q9 slice candidate; the general
slice exclusion and the external f2(Q9) problem remain open. -/

set_option autoImplicit false
-- Utility metadata above requires full declaration handles on one line.
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SubdividedMobiusKantor

open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q flip)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private crossing_flip flip_adj_iff edge_color from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

-- Two eight-cycles have steps one and three. Each matching rung is subdivided.
private def edges : List (Fin 24 × Fin 24) :=
  [(0,1), (1,2), (2,3), (3,4), (4,5), (5,6), (6,7), (7,0), (8,11), (9,12), (10,13), (11,14), (12,15), (13,8), (14,9), (15,10), (0,16), (1,17), (2,18), (3,19), (4,20), (5,21), (6,22), (7,23), (8,16), (9,17), (10,18), (11,19), (12,20), (13,21), (14,22), (15,23)]

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

-- These real two-edge and three-edge paths suffice; no cut catalog is assumed.
private def paths : List Clause :=
  [((0,1),(1,2)), ((0,1),(2,3)), ((1,0),(7,6)), ((1,0),(0,7)),
   ((1,0),(0,16)), ((0,1),(1,17)), ((0,1),(2,18)), ((1,0),(7,23)),
   ((1,0),(16,8)), ((0,1),(17,9)), ((1,2),(2,3)), ((1,2),(3,4)),
   ((2,1),(0,7)), ((2,1),(0,16)), ((2,1),(1,17)), ((1,2),(2,18)),
   ((1,2),(3,19)), ((2,1),(17,9)), ((1,2),(18,10)), ((2,3),(3,4)),
   ((2,3),(4,5)), ((3,2),(1,17)), ((3,2),(2,18)), ((2,3),(3,19)),
   ((2,3),(4,20)), ((3,2),(18,10)), ((2,3),(19,11)), ((3,4),(4,5)),
   ((3,4),(5,6)), ((4,3),(2,18)), ((4,3),(3,19)), ((3,4),(4,20)),
   ((3,4),(5,21)), ((4,3),(19,11)), ((3,4),(20,12)), ((4,5),(5,6)),
   ((4,5),(6,7)), ((5,4),(3,19)), ((5,4),(4,20)), ((4,5),(5,21)),
   ((4,5),(6,22)), ((5,4),(20,12)), ((4,5),(21,13)), ((5,6),(6,7)),
   ((5,6),(7,0)), ((6,5),(4,20)), ((6,5),(5,21)), ((5,6),(6,22)),
   ((5,6),(7,23)), ((6,5),(21,13)), ((5,6),(22,14)), ((6,7),(7,0)),
   ((6,7),(0,16)), ((7,6),(5,21)), ((7,6),(6,22)), ((6,7),(7,23)),
   ((7,6),(22,14)), ((6,7),(23,15)), ((7,0),(0,16)), ((7,0),(1,17)),
   ((0,7),(6,22)), ((0,7),(7,23)), ((7,0),(16,8)), ((0,7),(23,15)),
   ((11,8),(13,10)), ((8,11),(11,14)), ((11,8),(8,13)), ((8,11),(14,9)),
   ((11,8),(16,0)), ((8,11),(19,3)), ((11,8),(8,16)), ((8,11),(11,19)),
   ((11,8),(13,21)), ((8,11),(14,22)), ((12,9),(14,11)), ((9,12),(12,15)),
   ((12,9),(9,14)), ((9,12),(15,10)), ((12,9),(17,1)), ((9,12),(20,4)),
   ((12,9),(9,17)), ((9,12),(12,20)), ((12,9),(14,22)), ((9,12),(15,23)),
   ((13,10),(15,12)), ((10,13),(13,8)), ((13,10),(10,15)), ((13,10),(18,2)),
   ((10,13),(21,5)), ((10,13),(8,16)), ((13,10),(10,18)), ((10,13),(13,21)),
   ((13,10),(15,23)), ((14,11),(8,13)), ((11,14),(14,9)), ((14,11),(19,3)),
   ((11,14),(22,6)), ((14,11),(8,16)), ((11,14),(9,17)), ((14,11),(11,19)),
   ((11,14),(14,22)), ((15,12),(9,14)), ((12,15),(15,10)), ((15,12),(20,4)),
   ((12,15),(23,7)), ((15,12),(9,17)), ((12,15),(10,18)), ((15,12),(12,20)),
   ((12,15),(15,23)), ((8,13),(10,15)), ((13,8),(16,0)), ((8,13),(21,5)),
   ((13,8),(8,16)), ((8,13),(10,18)), ((13,8),(11,19)), ((8,13),(13,21)),
   ((14,9),(17,1)), ((9,14),(22,6)), ((14,9),(9,17)), ((9,14),(11,19)),
   ((14,9),(12,20)), ((9,14),(14,22)), ((15,10),(18,2)), ((10,15),(23,7)),
   ((15,10),(10,18)), ((10,15),(12,20)), ((15,10),(13,21)), ((10,15),(15,23)),
   ((16,0),(1,17)), ((16,0),(7,23)), ((0,16),(16,8)), ((17,1),(2,18)),
   ((1,17),(17,9)), ((18,2),(3,19)), ((2,18),(18,10)), ((19,3),(4,20)),
   ((3,19),(19,11)), ((20,4),(5,21)), ((4,20),(20,12)), ((21,5),(6,22)),
   ((5,21),(21,13)), ((22,6),(7,23)), ((6,22),(22,14)), ((7,23),(23,15)),
   ((16,8),(11,19)), ((16,8),(13,21)), ((17,9),(12,20)), ((17,9),(14,22)),
   ((18,10),(13,21)), ((18,10),(15,23)), ((19,11),(14,22)), ((20,12),(15,23))]

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
    Bool.xor (Bool.xor (c 0 != c 1) (c 3 != c 19)) (c 10 != c 18) = false := by
  simp only [cnf, paths, clause, List.all_cons, List.all_nil] at h
  grind

/-- The subdivided Mobius-Kantor graph has no induced embedding in any Qn. -/
theorem result : ¬ claim := by
  rintro ⟨n, f, hf, he⟩
  obtain ⟨i, hi⟩ := adjacent_exists_flip
    ((he 0 1).mp (by decide +kernel : graph.Adj 0 1))
  obtain ⟨j, hj⟩ := adjacent_exists_flip
    ((he 3 19).mp (by decide +kernel : graph.Adj 3 19))
  obtain ⟨k, hk⟩ := adjacent_exists_flip
    ((he 10 18).mp (by decide +kernel : graph.Adj 10 18))
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

end D5.S3.Combinatorics.Graph.HypercubeCritical.SubdividedMobiusKantor
