/- GID: D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamDiagram
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Literal counted-edge images and intrinsic endpoint multiplicities at every integer cut. -/
import Mathlib.Data.Fintype.Sigma
import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import D5.S3.ConceptDynamics.Coding.StandardBeamIdentification
import D5.S3.ConceptDynamics.Coding.StandardBeamPushforward

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedMatrixBeamDiagram
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.StandardBeamPushforward
open scoped BigOperators Matrix

private def edgeSigma {n m : ℕ} (M : CountMat n m) :
    Edge M ≃ Σ i : Fin n, Σ j : Fin m, Fin (M i j) where
  toFun e := ⟨e.source, e.target, e.number⟩
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨i, j, q⟩; rfl

private instance countedEdgeFintype {n m : ℕ} (M : CountMat n m) : Fintype (Edge M) :=
  Fintype.ofEquiv (Σ i : Fin n, Σ j : Fin m, Fin (M i j)) (edgeSigma M).symm

abbrev countedGraph {n : ℕ} (M : CountMat n n) : DirectedMultigraph (Fin n) (Edge M) :=
  ⟨Edge.source, Edge.target⟩

private theorem endpointRow_congr {k : ℕ} (M : CountMat k k) (N : ℤ)
    {U V : Set (Path M)} (h : U = V)
    [Finite (Parts (countedGraph M) U N)] [Finite (Parts (countedGraph M) V N)] :
    endpointRow (countedGraph M) U N = endpointRow (countedGraph M) V N := by
  subst V
  rfl

/-- Only a coefficient cast; the row limit remains the existing RowLimit. -/
def integerCounts {n m : ℕ} (M : CountMat n m) : Matrix (Fin n) (Fin m) ℤ :=
  fun i j => (M i j : ℤ)

theorem integerCounts_mul {n m k : ℕ} (R : CountMat n m) (S : CountMat m k) :
    integerCounts (R * S) = integerCounts R * integerCounts S := by
  ext i j
  simp [integerCounts, Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul]

/-- The numbered rectangular outgoing fiber; zero fibers stay empty. -/
abbrev NextR {n m : ℕ} (R : CountMat n m) (u : Fin n) :=
  {e : Edge R // e.source = u}

private def nextEquiv {n m : ℕ} (R : CountMat n m) (u : Fin n) :
    NextR R u ≃ Σ j : Fin m, Fin (R u j) where
  toFun e := by
    rcases e with ⟨⟨i, j, q⟩, h⟩
    change i = u at h
    subst i
    exact ⟨j, q⟩
  invFun e := ⟨⟨u, e.1, e.2⟩, rfl⟩
  left_inv e := by
    rcases e with ⟨⟨i, j, q⟩, h⟩
    change i = u at h
    subst i
    rfl
  right_inv e := by rcases e with ⟨j, q⟩; rfl

private theorem nextEquiv_target {n m : ℕ} (R : CountMat n m) (u : Fin n)
    (e : NextR R u) : (nextEquiv R u e).1 = e.val.target := by
  rcases e with ⟨⟨i, j, q⟩, h⟩
  change i = u at h
  subst i
  rfl

/-- Consumed below by the intrinsic endpoint count of the ACTUAL image. -/
private theorem numberedRow {n m : ℕ} (R : CountMat n m) (u : Fin n) :
    (∑ e : NextR R u, (Pi.single e.val.target (1 : ℤ) : Fin m → ℤ)) =
      (Pi.single u 1) ᵥ* integerCounts R := by
  classical
  have he := Fintype.sum_equiv (nextEquiv R u)
    (fun e => (Pi.single e.val.target (1 : ℤ) : Fin m → ℤ))
    (fun e => (Pi.single e.1 (1 : ℤ) : Fin m → ℤ))
    (fun e => by rw [nextEquiv_target])
  rw [he, Fintype.sum_sigma, Matrix.single_vecMul]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, Matrix.row, integerCounts, eq_comm]

/-- The beam API's adjacency counts each original numbered edge once. -/
theorem adjacency_counted {n : ℕ} (M : CountMat n n) :
    adjacency (countedGraph M) = integerCounts M := by
  funext u j
  have h := congrFun (numberedRow M u) j
  simpa only [StandardBeamEndpointRows.adjacency, StandardBeamGeometry.Out, NextR, countedGraph, Matrix.single_vecMul, Matrix.row, one_smul] using h

private theorem split_injective {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    Function.Injective (split R S) := by
  intro a b h
  let P := {p : Edge R × Edge S // p.1.target = p.2.source}
  have hp : (⟨split R S a, rfl⟩ : P) = ⟨split R S b, rfl⟩ := Subtype.ext h
  have he := congrArg (fun p : P => join R S p.val.1 p.val.2 p.property) hp
  simpa only [join_split] using he

/-- Exact original coding, including both parallel-edge numbers. -/
theorem elementary_split {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : Path (R * S)) (t : ℤ) :
    split S R ((elementaryHomeomorph R S x).val t) =
      ((split R S (x.val t)).2, (split R S (x.val (t + 1))).1) := by
  change split S R (join S R (split R S (x.val t)).2
    (split R S (x.val (t + 1))).1 (x.property t)) = _
  exact split_join S R _ _ _

/-- Inversion uses the PRECEDING output, not the reverse forward coding. -/
theorem elementary_symm_split {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (y : Path (S * R)) (t : ℤ) :
    split R S (((elementaryHomeomorph R S).symm y).val t) =
      ((split S R (y.val (t - 1))).2, (split S R (y.val t)).1) := by
  change split R S (join R S (split S R (y.val (t - 1))).2
    (split S R (y.val t)).1 (by
      simpa only [split_source, split_target, sub_add_cancel] using y.property (t - 1))) = _
  exact split_join R S _ _ _




section ActualRay
variable {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
variable (hB : Essential (countedGraph (S * R)))

private def boundaryEdge (alpha : Path (R * S)) (N : ℤ)
    (r : NextR R (endpoint (countedGraph (R * S)) alpha N)) :
    Out (countedGraph (S * R))
      (endpoint (countedGraph (S * R)) (elementaryHomeomorph R S alpha) (N - 1)) := by
  refine ⟨join S R (split R S (alpha.val N)).2 r.val r.property.symm, ?_⟩
  change (split R S (alpha.val N)).2.source =
    ((elementaryHomeomorph R S alpha).val (N - 1)).target
  have he := congrArg (fun p : Edge S × Edge R => p.2.target)
    (elementary_split R S alpha (N - 1))
  change ((elementaryHomeomorph R S alpha).val (N - 1)).target =
    (split R S (alpha.val (N - 1 + 1))).1.target at he
  rw [sub_add_cancel] at he
  exact he.symm

/-- A full target history with the prescribed target past and one selected R
edge. Only the existing appendOne supplies an arbitrary legal future. -/
def targetCenter (alpha : Path (R * S)) (N : ℤ)
    (r : NextR R (endpoint (countedGraph (R * S)) alpha N)) : Path (S * R) :=
  appendOne (countedGraph (S * R)) hB (elementaryHomeomorph R S alpha) (N - 1)
    (boundaryEdge R S alpha N r)

private theorem targetCenter_past (alpha : Path (R * S)) (N : ℤ)
    (r : NextR R (endpoint (countedGraph (R * S)) alpha N)) (k : ℤ) (hk : k < N) :
    (targetCenter R S hB alpha N r).val k = (elementaryHomeomorph R S alpha).val k :=
  appendOne_past (countedGraph (S * R)) hB _ (N - 1) _ k (by omega)

private theorem targetCenter_edge (alpha : Path (R * S)) (N : ℤ)
    (r : NextR R (endpoint (countedGraph (R * S)) alpha N)) :
    (targetCenter R S hB alpha N r).val N =
      join S R (split R S (alpha.val N)).2 r.val r.property.symm := by
  have he := appendOne_edge (countedGraph (S * R)) hB
    (elementaryHomeomorph R S alpha) (N - 1) (boundaryEdge R S alpha N r)
  simpa only [targetCenter, boundaryEdge, sub_add_cancel] using he

private theorem targetCenter_split (alpha : Path (R * S)) (N : ℤ)
    (r : NextR R (endpoint (countedGraph (R * S)) alpha N)) :
    split S R ((targetCenter R S hB alpha N r).val N) =
      ((split R S (alpha.val N)).2, r.val) := by
  rw [targetCenter_edge, split_join]

theorem targetCenter_endpoint (alpha : Path (R * S)) (N : ℤ)
    (r : NextR R (endpoint (countedGraph (R * S)) alpha N)) :
    endpoint (countedGraph (S * R)) (targetCenter R S hB alpha N r) N = r.val.target := by
  change ((targetCenter R S hB alpha N r).val N).target = _
  rw [targetCenter_edge]
  rfl

/-- Literal equality of actual sets, at EVERY signed cut. The source ray fixes
edges k ≤ N, so the index is r_(N+1), and the TARGET CUT IS STILL N. -/
theorem image_ray (alpha : Path (R * S)) (N : ℤ) :
    elementaryHomeomorph R S '' ray (countedGraph (R * S)) alpha N =
      ⋃ r : NextR R (endpoint (countedGraph (R * S)) alpha N),
        ray (countedGraph (S * R)) (targetCenter R S hB alpha N r) N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let r : NextR R (endpoint (countedGraph (R * S)) alpha N) :=
      ⟨(split R S (x.val (N + 1))).1,
        (x.property N).symm.trans (congrArg Edge.target (hx N le_rfl))⟩
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    intro k hk
    by_cases he : k = N
    · subst k
      apply split_injective S R
      rw [elementary_split, targetCenter_split, hx N le_rfl]
    · rw [targetCenter_past R S hB alpha N r k (by omega)]
      apply split_injective S R
      rw [elementary_split, elementary_split, hx k hk, hx (k + 1) (by omega)]
  · intro hy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
    refine ⟨(elementaryHomeomorph R S).symm y, ?_,
      (elementaryHomeomorph R S).apply_symm_apply y⟩
    intro k hk
    apply split_injective R S
    rw [elementary_symm_split]
    apply Prod.ext
    · rw [hr (k - 1) (by omega),
        targetCenter_past R S hB alpha N r (k - 1) (by omega), elementary_split]
      simp only [sub_add_cancel]
    · by_cases he : k = N
      · subst k
        rw [hr N le_rfl, targetCenter_split]
      · rw [hr k hk, targetCenter_past R S hB alpha N r k (by omega), elementary_split]

/-- Distinct R edge NUMBERS give disjoint target pasts, even when both
endpoints coincide. No endpoint collapse is used. -/
theorem image_ray_disjoint (alpha : Path (R * S)) (N : ℤ)
    (r q : NextR R (endpoint (countedGraph (R * S)) alpha N)) (hrq : r ≠ q) :
    Disjoint (ray (countedGraph (S * R)) (targetCenter R S hB alpha N r) N)
      (ray (countedGraph (S * R)) (targetCenter R S hB alpha N q) N) := by
  apply Set.disjoint_left.mpr
  intro y hyr hyq
  apply hrq
  apply Subtype.ext
  have he := congrArg (split S R) ((hyr N le_rfl).symm.trans (hyq N le_rfl))
  rw [targetCenter_split, targetCenter_split] at he
  exact congrArg Prod.snd he

include hB in
theorem image_ray_atCut (alpha : Path (R * S)) (N : ℤ) :
    AtCut (countedGraph (S * R))
      (elementaryHomeomorph R S '' ray (countedGraph (R * S)) alpha N) N := by
  rw [image_ray R S hB alpha N]
  exact atCut_iUnion _ _ N (fun r => ray_atCut _ hB (targetCenter R S hB alpha N r) N)

/-- Intrinsic endpoint multiplicity of the literal image, not a surrogate
algebraic beam. The finite index keeps empty and parallel-edge fibers. -/
theorem endpointRow_image_ray (alpha : Path (R * S)) (N : ℤ) :
    letI : Finite (Parts (countedGraph (S * R))
      (elementaryHomeomorph R S '' ray (countedGraph (R * S)) alpha N) N) :=
        (image_ray_atCut R S hB alpha N).1
    endpointRow (countedGraph (S * R))
      (elementaryHomeomorph R S '' ray (countedGraph (R * S)) alpha N) N =
        (Pi.single (endpoint (countedGraph (R * S)) alpha N) 1) ᵥ* integerCounts R := by
  letI := (image_ray_atCut R S hB alpha N).1
  letI : Finite (Parts (countedGraph (S * R))
      (⋃ r : NextR R (endpoint (countedGraph (R * S)) alpha N),
        ray (countedGraph (S * R)) (targetCenter R S hB alpha N r) N) N) :=
    (atCut_iUnion _ _ N (fun r => ray_atCut _ hB (targetCenter R S hB alpha N r) N)).1
  rw [endpointRow_congr (S * R) N (image_ray R S hB alpha N)]
  rw [endpointRow_disjointUnion _ hB (targetCenter R S hB alpha N) N
    (image_ray_disjoint R S hB alpha N)]
  simp_rw [targetCenter_endpoint]
  exact numberedRow R _

include hB in
/-- Cross-graph beam closure is proved from the ACTUAL finite ray partition. -/
theorem image_atCut {U : Set (Path (R * S))} {N : ℤ}
    (hU : AtCut (countedGraph (R * S)) U N) :
    AtCut (countedGraph (S * R)) (elementaryHomeomorph R S '' U) N := by
  letI : Finite (Parts (countedGraph (R * S)) U N) := hU.1
  have hp (P : Parts (countedGraph (R * S)) U N) :
      AtCut (countedGraph (S * R)) (elementaryHomeomorph R S '' P.val.val) N := by
    rw [RayAt.set_eq]
    exact image_ray_atCut R S hB _ N
  have he : elementaryHomeomorph R S '' U =
      ⋃ P : Parts (countedGraph (R * S)) U N, elementaryHomeomorph R S '' P.val.val := by
    calc
      _ = elementaryHomeomorph R S ''
          (⋃ P : Parts (countedGraph (R * S)) U N, P.val.val) :=
        congrArg (fun W => elementaryHomeomorph R S '' W) (parts_union _ hU)
      _ = _ := Set.image_iUnion
  rw [he]
  exact atCut_iUnion _ _ N hp

def elementaryImageBeam (U : Beam (countedGraph (R * S))) : Beam (countedGraph (S * R)) :=
  ⟨elementaryHomeomorph R S '' U.val, by
    obtain ⟨N, hN⟩ := U.property
    exact ⟨N, image_atCut R S hB hN⟩⟩

/-- The actual image row formula for every intrinsic finite beam partition.
This is the consumed cross-graph compatibility absent from FullAut's type. -/
theorem endpointRow_image {U : Set (Path (R * S))} {N : ℤ}
    (hU : AtCut (countedGraph (R * S)) U N) :
    letI : Finite (Parts (countedGraph (R * S)) U N) := hU.1
    letI : Finite (Parts (countedGraph (S * R)) (elementaryHomeomorph R S '' U) N) :=
      (image_atCut R S hB hU).1
    endpointRow (countedGraph (S * R)) (elementaryHomeomorph R S '' U) N =
      endpointRow (countedGraph (R * S)) U N ᵥ* integerCounts R := by
  letI : Finite (Parts (countedGraph (R * S)) U N) := hU.1
  letI : Fintype (Parts (countedGraph (R * S)) U N) := Fintype.ofFinite _
  let images (P : Parts (countedGraph (R * S)) U N) :=
    elementaryHomeomorph R S '' P.val.val
  have hp (P : Parts (countedGraph (R * S)) U N) : AtCut (countedGraph (S * R)) (images P) N := by
    dsimp [images]
    rw [RayAt.set_eq]
    exact image_ray_atCut R S hB _ N
  have hd (P Q : Parts (countedGraph (R * S)) U N) (hPQ : P ≠ Q) :
      Disjoint (images P) (images Q) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have he : x = z := (elementaryHomeomorph R S).injective (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (parts_disjoint _ P Q hPQ) hx (he.symm ▸ hz)
  have hset : elementaryHomeomorph R S '' U = ⋃ P, images P := by
    calc
      _ = elementaryHomeomorph R S ''
          (⋃ P : Parts (countedGraph (R * S)) U N, P.val.val) :=
        congrArg (fun W => elementaryHomeomorph R S '' W) (parts_union _ hU)
      _ = _ := Set.image_iUnion
  letI := (image_atCut R S hB hU).1
  letI (P : Parts (countedGraph (R * S)) U N) :
      Finite (Parts (countedGraph (S * R)) (images P) N) := (hp P).1
  have hrow (P : Parts (countedGraph (R * S)) U N) :
      endpointRow (countedGraph (S * R)) (images P) N =
        (Pi.single (RayAt.endpoint (countedGraph (R * S)) P.val) 1) ᵥ* integerCounts R := by
    let alpha := RayAt.representative (countedGraph (R * S)) P.val
    have heq : images P = elementaryHomeomorph R S ''
        ray (countedGraph (R * S)) alpha N :=
      congrArg (fun A => elementaryHomeomorph R S '' A) (RayAt.set_eq _ P.val)
    letI := (image_ray_atCut R S hB alpha N).1
    exact (endpointRow_congr (S * R) N heq).trans
      (endpointRow_image_ray R S hB alpha N)
  letI : Finite (Parts (countedGraph (S * R)) (⋃ P, images P) N) :=
    (atCut_iUnion (countedGraph (S * R)) images N hp).1
  calc
    _ = endpointRow (countedGraph (S * R)) (⋃ P, images P) N :=
      endpointRow_congr (S * R) N hset
    _ = ∑ P : Parts (countedGraph (R * S)) U N,
        endpointRow (countedGraph (S * R)) (images P) N :=
      endpointRow_disjointBeams (countedGraph (S * R)) images N hp hd
    _ = ∑ P : Parts (countedGraph (R * S)) U N,
        (integerCounts R).toLinearMapRight'
          (Pi.single (RayAt.endpoint (countedGraph (R * S)) P.val) 1) := by
      apply Finset.sum_congr rfl
      intro P hP
      exact hrow P
    _ = (integerCounts R).toLinearMapRight'
        (∑ P : Parts (countedGraph (R * S)) U N,
          Pi.single (RayAt.endpoint (countedGraph (R * S)) P.val) 1) := (map_sum _ _ _).symm
    _ = _ := rfl

end ActualRay
end D5.S3.ConceptDynamics.Coding.CountedMatrixBeamDiagram
