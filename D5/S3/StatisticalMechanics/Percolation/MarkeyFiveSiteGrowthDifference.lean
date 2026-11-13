/- GID: D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Markey five-site growth and the Shannon count difference. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22020
admission_basis: open-problem-resolution (#21459; Proved)
escape_witness: none; settling result
MarkeyA400701.claim: proof_shape: bind-only; direct frozen dependencies: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step [sha256:5a85730fe2249682225863142e1fa30ab23690687b206b92f78abd4b727f1d51]; escape_witness: none; consumers: MarkeyA400701.result.
WindowTransport.coordinates_injective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: WindowTransport.finite_state, WindowTransport.lattice_shape_count.
WindowTransport.window_adj: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: WindowTransport.finite_state.
WindowTransport.grown_bounds: proof_shape: content; direct frozen dependencies: none; escape_witness: none; consumers: WindowTransport.finite_state, WindowTransport.lattice_shape_count.
WindowTransport.window_surjective: proof_shape: bind-only; direct frozen dependencies: none; escape_witness: none; consumers: WindowTransport.finite_state, WindowTransport.lattice_shape_count.
WindowTransport.mem_step_two: proof_shape: bind-only; direct frozen dependencies: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step [sha256:5a85730fe2249682225863142e1fa30ab23690687b206b92f78abd4b727f1d51]; escape_witness: none; consumers: WindowTransport.finite_state.
WindowTransport.finite_state: proof_shape: content; direct frozen dependencies: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step [sha256:5a85730fe2249682225863142e1fa30ab23690687b206b92f78abd4b727f1d51]; escape_witness: none; consumers: WindowTransport.lattice_shape_count.
WindowTransport.lattice_shape_count: proof_shape: content; direct frozen dependencies: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step [sha256:5a85730fe2249682225863142e1fa30ab23690687b206b92f78abd4b727f1d51], D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: MarkeyA400701.result.
MarkeyA400701.result: proof_shape: content; direct frozen dependencies: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.step [sha256:5a85730fe2249682225863142e1fa30ab23690687b206b92f78abd4b727f1d51], D5/S3/Arith/ModularForms/CubicThetaLattice.normTripling [sha256:11f6f8cd3bb1d570e95e134e5f6edd135af14526a2e24eed508377d2ba92ad6c]; escape_witness: none; consumers: settling result.
-/
import D5.S3.Geometry.ShannonFixedRadiusCircleVertices
import D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap


/-! Exact lattice growth and circle-vertex identities. -/
noncomputable section
namespace D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference
open D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth
open D5.S3.Geometry.ShannonFixedRadiusCircleVertices

namespace MarkeyA400701
/-- OEIS A400701's conjectured relation, at the identical iteration index n > 1. -/
def claim : Prop :=
  ∀ (a b : (EuclideanSpace ℝ (Fin 2))), a ≠ b → ∀ (n : ℕ), 1 < n →
    D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.latticeCount n = D5.S3.Geometry.ShannonFixedRadiusCircleVertices.ShannonA374338.vertexCount a b n + 4 * n + 7

end MarkeyA400701


namespace WindowTransport
open scoped Classical
open Finset
open D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap

private theorem coordinates_injective (n : ℕ) : Function.Injective (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n) := by
  rintro ⟨x,y⟩ ⟨u,v⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates] at hx hy
  apply Prod.ext
  · apply Fin.ext
    change x.val = u.val
    omega
  · apply Fin.ext
    change y.val = v.val
    omega

private theorem window_adj (n : ℕ) (p q : (Fin (2*n+7) × Fin (2*n+3))) :
    (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.windowGraph n).Adj p q ↔
      D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n q-D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p ∈ D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.directions := by
  rw [D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.windowGraph,SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne,h|h⟩
    · exact h
    · simpa only [neg_sub] using (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.CircleGrowth.directions_neg _).mpr h
  · intro h
    refine ⟨?_,Or.inl h⟩
    rintro rfl
    norm_num [D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.directions,Prod.ext_iff] at h

private theorem grown_bounds (m t : ℕ) (p : (ℤ × ℤ)) (hp : p ∈ D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.grown m t) :
    -(t:ℤ) ≤ p.1 ∧ p.1 ≤ (m:ℤ)-1+t ∧ -(t:ℤ) ≤ p.2 ∧ p.2 ≤ t := by
  induction t generalizing p with
  | zero =>
    simp only [D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.grown,D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.initial,Set.mem_setOf_eq] at hp
    omega
  | succ t ih =>
    rcases hp with hp|hp
    · have h := ih p hp
      push_cast
      omega
    · obtain ⟨d,hd,e,he,hde,h1,h2⟩ := hp
      have h := ih (p+d) h1
      simp only [D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.directions,mem_insert,mem_singleton] at hd
      rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [Prod.fst_add,Prod.snd_add] at h <;> push_cast <;> omega

private theorem window_surjective (n : ℕ) (p : (ℤ × ℤ))
    (hp : -(n:ℤ) ≤ p.1 ∧ p.1 ≤ 4+n ∧ -(n:ℤ) ≤ p.2 ∧ p.2 ≤ n) :
    ∃ q : (Fin (2*n+7) × Fin (2*n+3)), D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n q=p := by
  refine ⟨(⟨(p.1+n+1).toNat,by omega⟩,⟨(p.2+n+1).toNat,by omega⟩),?_⟩
  apply Prod.ext <;> dsimp [D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates] <;> omega

private theorem mem_step_two {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (p : V) :
    p ∈ step G 2 A ↔ p ∈ A ∨ ∃ q ∈ A, ∃ r ∈ A, q ≠ r ∧ G.Adj p q ∧ G.Adj p r := by
  simp only [step,mem_union,mem_filter,mem_univ,true_and]
  rw [show (2 ≤ (G.neighborFinset p ∩ A).card) ↔
      1 < (G.neighborFinset p ∩ A).card by omega,one_lt_card]
  simp only [mem_inter,SimpleGraph.mem_neighborFinset]
  constructor
  · rintro (h|⟨q,⟨hq,hqa⟩,r,⟨hr,hra⟩,hne⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q,hqa,r,hra,hne,hq,hr⟩
  · rintro (h|⟨q,hq,r,hr,hne,ha,hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q,⟨ha,hq⟩,r,⟨hb,hr⟩,hne⟩

private theorem finite_state (n t : ℕ) (ht : t ≤ n) (p : (Fin (2*n+7) × Fin (2*n+3))) :
    p ∈ (step (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.windowGraph n) 2)^[t] (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.seed n) ↔
      D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p ∈ D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.grown 5 t := by
  classical
  induction t generalizing p with
  | zero =>
    simp only [Function.iterate_zero_apply,D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.seed,mem_filter,mem_univ,true_and,
      D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.grown,D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.initial,Set.mem_setOf_eq]
    omega
  | succ t ih =>
    rw [Function.iterate_succ_apply',mem_step_two]
    change (_ ∨ _) ↔ (_ ∨ _)
    constructor
    · rintro (h|⟨q,hq,r,hr,hne,ha,hb⟩)
      · exact Or.inl ((ih (by omega) p).mp h)
      · refine Or.inr ⟨D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n q-D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p,
          (window_adj n p q).mp ha,
          D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n r-D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p,
          (window_adj n p r).mp hb,?_,?_,?_⟩
        · exact fun h => hne (coordinates_injective n ((sub_left_inj).mp h))
        · simpa using (ih (by omega) q).mp hq
        · simpa using (ih (by omega) r).mp hr
    · rintro (h|⟨d,hd,e,he,hne,hq,hr⟩)
      · exact Or.inl ((ih (by omega) p).mpr h)
      · have hqb := grown_bounds 5 t _ hq
        have hrb := grown_bounds 5 t _ hr
        obtain ⟨q,heq⟩ := window_surjective n (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p+d) (by omega)
        obtain ⟨r,her⟩ := window_surjective n (D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p+e) (by omega)
        refine Or.inr ⟨q,(ih (by omega) q).mpr (heq.symm ▸ hq),
          r,(ih (by omega) r).mpr (her.symm ▸ hr),?_,?_,?_⟩
        · intro h
          subst r
          exact hne (add_left_cancel (heq.symm.trans her))
        · apply (window_adj n p q).mpr
          rw [heq,add_sub_cancel_left]
          exact hd
        · apply (window_adj n p r).mpr
          rw [her,add_sub_cancel_left]
          exact he

private theorem lattice_shape_count (n : ℕ) (hn : 2 ≤ n) :
    D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.latticeCount n = (D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.shape 5 n).card := by
  classical
  unfold D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.latticeCount
  apply card_bij (fun p _ => D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.MarkeyA400701.coordinates n p)
  · intro p hp
    have h := (finite_state n n (by omega) p).mp hp
    rw [D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.grown_coe 5 n (Or.inr rfl) hn] at h
    exact h
  · intro p hp q hq he
    exact coordinates_injective n he
  · intro q hq
    have hg : q ∈ D5.S3.StatisticalMechanics.Percolation.TriangularTwoNeighborGrowth.AxialGrowth.grown 5 n := by
      rw [D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.grown_coe 5 n (Or.inr rfl) hn]
      exact hq
    have hb := grown_bounds 5 n q hg
    obtain ⟨p,hp⟩ := window_surjective n q (by simpa using hb)
    refine ⟨p,(finite_state n n (by omega) p).mpr (hp.symm ▸ hg),hp⟩

end WindowTransport

namespace MarkeyA400701

theorem result : claim := by
  intro a b hab n hn
  rw [WindowTransport.lattice_shape_count n (by omega),D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.count_difference]
  have hc := D5.S3.Geometry.ShannonFixedRadiusCircleVertices.ShannonA374338.result a b hab
  have hh : (D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.shape 2 n).card = D5.S3.Geometry.ShannonFixedRadiusCircleVertices.ShannonA374338.vertexCount a b n := by
    rw [D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexShapeCounts.shape_card]
    rw [show 2-1+2*n=2*n+1 by omega]
    have hmod : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hmod with hm|hm|hm
    · obtain ⟨k,rfl⟩ : ∃ k, n=3*k := ⟨n/3,by omega⟩
      rw [D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexCounts.polygon_zero,hc.2.1 _ k (by omega) rfl]
      ring_nf
      omega
    · obtain ⟨k,rfl⟩ : ∃ k, n=3*k+1 := ⟨n/3,by omega⟩
      rw [D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexCounts.polygon_one,hc.1 _ k rfl]
      ring_nf
      omega
    · obtain ⟨k,rfl⟩ : ∃ k, n=3*k+2 := ⟨n/3,by omega⟩
      rw [D5.S3.Geometry.ShannonFixedRadiusCircleVertices.HexCounts.polygon_two,hc.2.2 _ (k+1) (by omega) (by omega)]
      ring_nf
      omega
  rw [hh]

end MarkeyA400701

end D5.S3.StatisticalMechanics.Percolation.MarkeyFiveSiteGrowthDifference
end
