/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.claim; result=D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.result; claim=D5/S3/Combinatorics/Graph/ComponentPacking/HausmannQuestion54Refutation.claim
   digest: GP(7,2) refutes the independent-side component-order-three partition assertion. -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Graph.ComponentPacking.HausmannQuestion54Refutation

/-- A five-cycle exists and no shorter odd simple cycle exists. -/
def OddGirthFive {V : Type*} (G : SimpleGraph V) : Prop :=
  (∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 5) ∧
  ∀ (v : V) (w : G.Walk v v), w.IsCycle → Odd w.length → 5 ≤ w.length

/-- Component order counts all vertices, including singleton components. -/
def SmallComponents {V : Type*} (G : SimpleGraph V) (R : Set V) : Prop :=
  ∀ C : (G.induce R).ConnectedComponent, Nat.card C.supp ≤ 3

/-- The full universal assertion in Hausmann Question 5.4, without a size cutoff.
The finite presentations and their decidable instances impose no graph restriction. -/
def claim : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
  (∀ v, G.degree v ≤ 3) → OddGirthFive G →
  ∃ L R : Set V, Disjoint L R ∧ L ∪ R = Set.univ ∧
    G.IsIndepSet L ∧ SmallComponents G R

private def edges : Finset (Fin 14 × Fin 14) :=
  {(0,1), (0,6), (0,7), (1,2), (1,8), (2,3), (2,9), (3,4), (3,10), (4,5), (4,11), (5,6), (5,12), (6,13), (7,9), (7,12), (8,10), (8,13), (9,11), (10,12), (11,13)}

private def counterGraph : SimpleGraph (Fin 14) where
  Adj i j := (i,j) ∈ edges ∨ (j,i) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i h; fin_cases i <;> simp [edges] at h⟩

private instance : DecidableRel counterGraph.Adj :=
  inferInstanceAs (DecidableRel (fun i j => (i,j) ∈ edges ∨ (j,i) ∈ edges))

/-- The exhaustive independent-set split produces four distinct residual vertices
in a single tree. Each newly added vertex has an earlier neighbour. -/
private theorem four_obstruction (L : Set (Fin 14)) (hL : counterGraph.IsIndepSet L) :
    ∃ a b c d : Fin 14, a ∉ L ∧ b ∉ L ∧ c ∉ L ∧ d ∉ L ∧
      [a,b,c,d].Nodup ∧ counterGraph.Adj a b ∧
      (counterGraph.Adj a c ∨ counterGraph.Adj b c) ∧
      (counterGraph.Adj a d ∨ counterGraph.Adj b d ∨ counterGraph.Adj c d) := by
  classical
  exact Classical.byCases (p := 0 ∈ L) (fun h0 =>
    Classical.byCases (p := 2 ∈ L) (fun h2 =>
      Classical.byCases (p := 4 ∈ L) (fun h4 =>
        Classical.byCases (p := 8 ∈ L) (fun h8 =>
          ⟨5,6,13,11, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h8 =>
          Classical.byCases (p := 10 ∈ L) (fun h10 =>
            ⟨5,6,12,7, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h10 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h10 =>
            ⟨1,8,10,3, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h8, h10, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h4 =>
        Classical.byCases (p := 5 ∈ L) (fun h5 =>
          Classical.byCases (p := 8 ∈ L) (fun h8 =>
            ⟨3,4,10,12, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h8 =>
            Classical.byCases (p := 10 ∈ L) (fun h10 =>
              Classical.byCases (p := 11 ∈ L) (fun h11 =>
                ⟨1,8,13,6, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h10 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h11 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h11 =>
                ⟨3,4,11,9, (fun hu => hL h10 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), h11, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h10 =>
              ⟨1,8,10,3, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h8, h10, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h5 =>
          ⟨3,4,5,6, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h4, h5, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h2 =>
      Classical.byCases (p := 3 ∈ L) (fun h3 =>
        Classical.byCases (p := 5 ∈ L) (fun h5 =>
          Classical.byCases (p := 8 ∈ L) (fun h8 =>
            Classical.byCases (p := 9 ∈ L) (fun h9 =>
              ⟨4,11,13,6, (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h9 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h9 =>
              ⟨1,2,9,7, (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), h9, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h8 =>
            ⟨1,2,8,10, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), h8, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h5 =>
          Classical.byCases (p := 8 ∈ L) (fun h8 =>
            ⟨4,5,6,13, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), h5, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h8 =>
            ⟨1,2,8,10, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), h8, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h3 =>
        Classical.byCases (p := 4 ∈ L) (fun h4 =>
          Classical.byCases (p := 8 ∈ L) (fun h8 =>
            ⟨1,2,3,10, (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), h2, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h8 =>
            ⟨1,2,3,8, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), h2, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), h8, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h4 =>
          ⟨1,2,3,4, (fun hu => hL h0 hu (by decide +kernel) (by decide +kernel)), h2, h3, h4, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)))) (fun h0 =>
    Classical.byCases (p := 1 ∈ L) (fun h1 =>
      Classical.byCases (p := 3 ∈ L) (fun h3 =>
        Classical.byCases (p := 5 ∈ L) (fun h5 =>
          Classical.byCases (p := 7 ∈ L) (fun h7 =>
            Classical.byCases (p := 11 ∈ L) (fun h11 =>
              ⟨0,6,13,8, (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h11 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h11 =>
              ⟨2,9,11,4, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), h11, (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h7 =>
            ⟨0,6,7,12, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), h7, (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h5 =>
          Classical.byCases (p := 6 ∈ L) (fun h6 =>
            Classical.byCases (p := 7 ∈ L) (fun h7 =>
              ⟨4,5,12,10, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h7 =>
              Classical.byCases (p := 9 ∈ L) (fun h9 =>
                ⟨4,5,11,13, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h9 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h9 =>
                ⟨0,7,9,2, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), h7, h9, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h6 =>
            ⟨0,6,5,4, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), h6, h5, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h3 =>
        Classical.byCases (p := 4 ∈ L) (fun h4 =>
          Classical.byCases (p := 6 ∈ L) (fun h6 =>
            Classical.byCases (p := 7 ∈ L) (fun h7 =>
              ⟨2,3,9,11, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h7 =>
              Classical.byCases (p := 9 ∈ L) (fun h9 =>
                Classical.byCases (p := 10 ∈ L) (fun h10 =>
                  ⟨0,7,12,5, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h9 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h10 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h10 =>
                  ⟨2,3,10,8, (fun hu => hL h9 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), h10, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h9 =>
                ⟨0,7,9,2, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), h7, h9, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h6 =>
            Classical.byCases (p := 7 ∈ L) (fun h7 =>
              ⟨0,6,5,12, (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), h6, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h7 =>
              ⟨0,6,5,7, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), h6, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), h7, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h4 =>
          Classical.byCases (p := 5 ∈ L) (fun h5 =>
            Classical.byCases (p := 7 ∈ L) (fun h7 =>
              ⟨2,3,4,9, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), h3, (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h7 =>
              ⟨0,6,7,12, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), h7, (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h5 =>
            ⟨2,3,4,5, (fun hu => hL h1 hu (by decide +kernel) (by decide +kernel)), h3, h4, h5, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)))) (fun h1 =>
      Classical.byCases (p := 2 ∈ L) (fun h2 =>
        Classical.byCases (p := 4 ∈ L) (fun h4 =>
          Classical.byCases (p := 6 ∈ L) (fun h6 =>
            Classical.byCases (p := 7 ∈ L) (fun h7 =>
              Classical.byCases (p := 8 ∈ L) (fun h8 =>
                ⟨3,10,12,5, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h8 =>
                ⟨0,1,8,13, (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h8, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h7 =>
              ⟨0,1,7,9, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h7, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h6 =>
            ⟨0,1,6,5, h0, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h6, (fun hu => hL h4 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h4 =>
          Classical.byCases (p := 5 ∈ L) (fun h5 =>
            Classical.byCases (p := 7 ∈ L) (fun h7 =>
              Classical.byCases (p := 8 ∈ L) (fun h8 =>
                ⟨0,1,6,13, (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h8 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h8 =>
                ⟨0,1,6,8, (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), h8, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h7 =>
              ⟨0,1,6,7, h0, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), h7, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h5 =>
            Classical.byCases (p := 6 ∈ L) (fun h6 =>
              Classical.byCases (p := 7 ∈ L) (fun h7 =>
                ⟨3,4,5,12, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h4, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h7 =>
                ⟨0,1,7,9, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h7, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h6 =>
              ⟨0,1,6,5, h0, (fun hu => hL h2 hu (by decide +kernel) (by decide +kernel)), h6, h5, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)))) (fun h2 =>
        Classical.byCases (p := 3 ∈ L) (fun h3 =>
          Classical.byCases (p := 5 ∈ L) (fun h5 =>
            ⟨0,1,2,6, h0, h1, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h5 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h5 =>
            Classical.byCases (p := 6 ∈ L) (fun h6 =>
              Classical.byCases (p := 7 ∈ L) (fun h7 =>
                ⟨0,1,2,9, (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), h1, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), (fun hu => hL h7 hu (by decide +kernel) (by decide +kernel)), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩) (fun h7 =>
                ⟨0,1,2,7, (fun hu => hL h6 hu (by decide +kernel) (by decide +kernel)), h1, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), h7, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)) (fun h6 =>
              ⟨0,1,2,6, h0, h1, (fun hu => hL h3 hu (by decide +kernel) (by decide +kernel)), h6, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))) (fun h3 =>
          ⟨0,1,2,3, h0, h1, h2, h3, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩))))

private theorem residual_large (L R : Set (Fin 14))
    (hU : L ∪ R = Set.univ) (hL : counterGraph.IsIndepSet L) :
    ¬ SmallComponents counterGraph R := by
  classical
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hn,hab,hac,had⟩ := four_obstruction L hL
  have toR (v : Fin 14) (hv : v ∉ L) : v ∈ R := by
    have : v ∈ L ∪ R := by rw [hU]; trivial
    exact this.resolve_left hv
  let aa : R := ⟨a,toR a ha⟩
  let bb : R := ⟨b,toR b hb⟩
  let cc : R := ⟨c,toR c hc⟩
  let dd : R := ⟨d,toR d hd⟩
  let C := (counterGraph.induce R).connectedComponentMk aa
  have ma : aa ∈ C.supp := rfl
  have step {x y : R} (hx : x ∈ C.supp) (hxy : counterGraph.Adj x.val y.val) :
      y ∈ C.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hxy).mp hx
  have mb : bb ∈ C.supp := step ma hab
  have mc : cc ∈ C.supp := hac.elim (fun h => step (y := cc) ma h) (fun h => step (y := cc) mb h)
  have md : dd ∈ C.supp := had.elim (fun h => step (y := dd) ma h)
    (fun h => h.elim (fun h => step (y := dd) mb h) (fun h => step (y := dd) mc h))
  let f : Fin 4 → C.supp := ![⟨aa,ma⟩,⟨bb,mb⟩,⟨cc,mc⟩,⟨dd,md⟩]
  have inj : Function.Injective f := by
    have hn' : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
      simpa [List.nodup_cons, and_assoc] using hn
    intro i j hij
    have he : (f i).val.val = (f j).val.val := congrArg (fun x => x.val.val) hij
    fin_cases i <;> fin_cases j <;> simp_all [f,aa,bb,cc,dd]
  have lower : 4 ≤ Nat.card C.supp := by
    simpa using Nat.card_le_card_of_injective f inj
  intro small
  have := small C
  omega

private theorem legal :
    (∀ v, counterGraph.degree v ≤ 3) ∧ OddGirthFive counterGraph := by
  have deg : ∀ v, counterGraph.degree v ≤ 3 := by
    intro v
    fin_cases v <;> decide +kernel
  have triangle : ∀ a b c : Fin 14,
      counterGraph.Adj a b → counterGraph.Adj a c → ¬ counterGraph.Adj b c := by
    decide +kernel
  have no3 : ¬ ∃ s : Finset (Fin 14), counterGraph.IsNClique 3 s := by
    rintro ⟨s,hs⟩
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := counterGraph.is3Clique_iff.mp hs
    exact triangle a b c hab hac hbc
  let w : counterGraph.Walk 0 0 :=
    .cons (v := 1) (by decide +kernel) (.cons (v := 2) (by decide +kernel)
      (.cons (v := 9) (by decide +kernel) (.cons (v := 7) (by decide +kernel)
        (.cons (by decide +kernel) .nil))))
  have hw : w.IsCycle := by
    refine { edges_nodup := ?_, ne_nil := ?_, support_nodup := ?_ }
    · decide +kernel
    · intro h
      have := congrArg SimpleGraph.Walk.length h
      simp [w] at this
    · decide +kernel
  refine ⟨deg,⟨⟨0,w,hw,rfl⟩,?_⟩⟩
  intro v p hp ho
  by_contra h
  have h3 : p.length = 3 := by
    have := hp.three_le_length
    rcases ho with ⟨k,hk⟩
    omega
  exact no3 (counterGraph.is3Clique_iff_exists_cycle_length_three.mpr ⟨v,p,hp,h3⟩)

/-- The full assertion fails on the explicit GP(7,2), without extra input restrictions. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨L,R,_,hU,hL,hR⟩ := h (Fin 14) counterGraph legal.1 legal.2
  exact residual_large L R hU hL hR

end D5.S3.Combinatorics.Graph.ComponentPacking.HausmannQuestion54Refutation
