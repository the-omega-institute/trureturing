/- GID: D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: An infinite twin-free theta family separates the two equalities. -/

/-
admission_basis: open-problem-resolution (#22167; Proved)
escape_witness: none
utility: none (unbounded theta-family statements and their consumed helpers).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23310
Frozen dependency declarations:
D5/S3/Combinatorics/SpectralGraph/BonettoSignature.mixedMatrix @ sha256:83b85a455c6497f8cddc23a809c3d563e4955257f535213d5fa6a57135be349c
D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.transfer @ sha256:9c75926175b4e0e95c8a5df62503e74ba85b035e570897bfdc462d1888d30f30
D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.MatrixKind.signless @ sha256:6f0b7f661a3953ddbbaae1ee9e3b479743c2eba7348a6a1f0e246bebb02f68bf
D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.sourceMatrix @ sha256:8494c96c2289763860006d56dd8768fdf7477f0c0b187d6e22a611010d1e9331
D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.distance_certificate @ sha256:2ed868feac517a64060ab1dc1f05d5c4edfaf7f3ee530ce3f1d4d0d67b9d7684
Declaration judgements (definitions carry no independent mathematical claim):
longVertex_zero | proof_shape: bind-only | escape_witness: none | consumer: long_neighbors_distinct
longVertex_last | proof_shape: bind-only | escape_witness: none | consumer: thetaLift_long
longVertex_inner | proof_shape: bind-only | escape_witness: none | consumer: thetaLift_long
neighbors_0 | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_0
neighbors_1 | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_1
neighbors_2 | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_2
neighbors_3 | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_3
neighbors_4 | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_4
neighbors_5 | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_5
theta_long_adj | proof_shape: bind-only | escape_witness: none | consumer: neighbors_long
neighbors_long | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_long
long_neighbors_distinct | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_long
mixed_theta_eq | proof_shape: bind-only | escape_witness: none | consumer: theta_operator_row
theta_operator_row | proof_shape: bind-only | escape_witness: none | consumer: eigen_neighbor_equation
eigen_neighbor_equation | proof_shape: bind-only | escape_witness: none | consumer: eigen_row_long
eigen_row_0 | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
eigen_row_1 | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
eigen_row_2 | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
eigen_row_3 | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
eigen_row_4 | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
eigen_row_5 | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
eigen_row_long | proof_shape: bind-only | escape_witness: none | consumer: graphCoordinates
graph_coordinates_exist | proof_shape: bind-only | escape_witness: none | consumer: theta_laplacian_multiplicity_upper
periodSix_recurrence | proof_shape: bind-only | escape_witness: none | consumer: thetaLift_eigen
thetaLiftLinear_apply | proof_shape: bind-only | escape_witness: none | consumer: thetaLift_injective
thetaLift_long | proof_shape: bind-only | escape_witness: none | consumer: thetaLift_eigen
thetaLift_eigen | proof_shape: bind-only | escape_witness: none | consumer: theta_laplacian_multiplicity_lower
thetaLift_injective | proof_shape: bind-only | escape_witness: none | consumer: theta_laplacian_multiplicity_lower
theta_laplacian_multiplicity_lower | proof_shape: bind-only | escape_witness: none | consumer: theta_maximum_multiplicities
theta_laplacian_multiplicity_upper | proof_shape: content | escape_witness: D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.bounded_recurrence_unique | consumer: theta_maximum_multiplicities
source_signless_eq | proof_shape: bind-only | escape_witness: none | consumer: theta_signless_multiplicity_upper
theta_signless_multiplicity_upper | proof_shape: content | escape_witness: D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.bounded_recurrence_unique | consumer: theta_maximum_multiplicities
theta_maximum_multiplicities | proof_shape: content | escape_witness: D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.bounded_recurrence_unique | consumer: result
result | proof_shape: content | escape_witness: D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.bounded_recurrence_unique | consumer: none (settling result)
longVertex | proof_shape: bind-only | escape_witness: none | consumer: longVertex_zero
graphCoordinates | proof_shape: bind-only | escape_witness: none | consumer: graph_coordinates_exist
periodSix | proof_shape: bind-only | escape_witness: none | consumer: thetaLiftLinear_apply
thetaLiftLinear | proof_shape: bind-only | escape_witness: none | consumer: thetaLiftLinear_apply
claim | proof_shape: bind-only | escape_witness: none | consumer: result (statement type)
-/

import D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure
import D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
import D5.S3.Combinatorics.SpectralGraph.BonettoSignature
import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.SpectralGraph.BonettoSignature
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaStructure
open D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
set_option maxHeartbeats 1800000

attribute [local instance] Classical.propDecidable

noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

/-- Long-path index zero is the first terminal; index r and all greater
indices are the second terminal. -/
private def longVertex (r : ℕ) (hr : 2 ≤ r) (j : ℕ) : Fin (r+5) :=
  if j=0 then ⟨0,by omega⟩ else if h : j<r then ⟨j+5,by omega⟩ else ⟨1,by omega⟩

private theorem longVertex_zero (r : ℕ) (hr : 2 ≤ r) :
    longVertex r hr 0 = ⟨0,by omega⟩ := by exact Fin.eq_mk_iff_val_eq.mpr rfl
private theorem longVertex_last (r : ℕ) (hr : 2 ≤ r) :
    longVertex r hr r = ⟨1,by omega⟩ := by simp [longVertex,show r≠0 by omega]
private theorem longVertex_inner (r : ℕ) (hr : 2 ≤ r) (j : ℕ)
    (hj : 0<j) (hjr : j<r) : longVertex r hr j = ⟨j+5,by omega⟩ := by
  simp [longVertex,show j≠0 by omega,hjr]

private theorem neighbors_0 (r : ℕ) (hr : 10 ≤ r) :
    (thetaGraph r (by omega)).neighborFinset ⟨0,by omega⟩ = {⟨2,by omega⟩, ⟨4,by omega⟩, ⟨6,by omega⟩} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  change (thetaEdge r 0 y.val ∨ thetaEdge r y.val 0) ↔ y.val=2 ∨ y.val=4 ∨ y.val=6
  dsimp [thetaEdge]
  omega

private theorem neighbors_1 (r : ℕ) (hr : 10 ≤ r) :
    (thetaGraph r (by omega)).neighborFinset ⟨1,by omega⟩ = {⟨3,by omega⟩, ⟨5,by omega⟩, ⟨r+4,by omega⟩} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  change (thetaEdge r 1 y.val ∨ thetaEdge r y.val 1) ↔ y.val=3 ∨ y.val=5 ∨ y.val=r+4
  dsimp [thetaEdge]
  omega

private theorem neighbors_2 (r : ℕ) (hr : 10 ≤ r) :
    (thetaGraph r (by omega)).neighborFinset ⟨2,by omega⟩ = {⟨0,by omega⟩, ⟨3,by omega⟩} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  change (thetaEdge r 2 y.val ∨ thetaEdge r y.val 2) ↔ y.val=0 ∨ y.val=3
  dsimp [thetaEdge]
  omega

private theorem neighbors_3 (r : ℕ) (hr : 10 ≤ r) :
    (thetaGraph r (by omega)).neighborFinset ⟨3,by omega⟩ = {⟨2,by omega⟩, ⟨1,by omega⟩} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  change (thetaEdge r 3 y.val ∨ thetaEdge r y.val 3) ↔ y.val=2 ∨ y.val=1
  dsimp [thetaEdge]
  omega

private theorem neighbors_4 (r : ℕ) (hr : 10 ≤ r) :
    (thetaGraph r (by omega)).neighborFinset ⟨4,by omega⟩ = {⟨0,by omega⟩, ⟨5,by omega⟩} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  change (thetaEdge r 4 y.val ∨ thetaEdge r y.val 4) ↔ y.val=0 ∨ y.val=5
  dsimp [thetaEdge]
  omega

private theorem neighbors_5 (r : ℕ) (hr : 10 ≤ r) :
    (thetaGraph r (by omega)).neighborFinset ⟨5,by omega⟩ = {⟨4,by omega⟩, ⟨1,by omega⟩} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  change (thetaEdge r 5 y.val ∨ thetaEdge r y.val 5) ↔ y.val=4 ∨ y.val=1
  dsimp [thetaEdge]
  omega

private theorem theta_long_adj (r n y : ℕ) (hn : 6≤n) :
    (thetaEdge r n y ∨ thetaEdge r y n) ↔
      ((n=r+4 ∧ y=1) ∨ y=n+1) ∨ ((y=0 ∧ n=6) ∨ (6≤y ∧ n=y+1)) := by
  simp [thetaEdge,hn,show n≠0 by omega,show n≠1 by omega,
    show n≠2 by omega,show n≠3 by omega,show n≠4 by omega,show n≠5 by omega]

private theorem neighbors_long (r : ℕ) (hr : 10 ≤ r) (j : ℕ)
    (hj : 0<j) (hjr : j<r) :
    (thetaGraph r (by omega)).neighborFinset (longVertex r (by omega) j) =
      {longVertex r (by omega) (j-1),longVertex r (by omega) (j+1)} := by
  classical
  ext y
  have hy := y.isLt
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,theta_adj]
  rw [longVertex_inner r (by omega) j hj hjr]
  change (thetaEdge r (j+5) y.val ∨ thetaEdge r y.val (j+5)) ↔
    y.val=(longVertex r (by omega) (j-1)).val ∨
      y.val=(longVertex r (by omega) (j+1)).val
  rw [theta_long_adj r (j+5) y.val (by omega)]
  by_cases hj1 : j=1
  · subst j
    rw [longVertex_zero,longVertex_inner r (by omega) 2 (by omega) (by omega)]
    change _ ↔ y.val=0 ∨ y.val=7
    omega
  · rw [longVertex_inner r (by omega) (j-1) (by omega) (by omega)]
    by_cases hp : j+1=r
    · rw [hp,longVertex_last]
      change _ ↔ y.val=j-1+5 ∨ y.val=1
      omega
    · rw [longVertex_inner r (by omega) (j+1) (by omega) (by omega)]
      change _ ↔ y.val=j-1+5 ∨ y.val=j+1+5
      omega

private theorem long_neighbors_distinct (r : ℕ) (hr : 10 ≤ r) (j : ℕ)
    (hj : 0<j) (hjr : j<r) :
    longVertex r (by omega) (j-1) ≠ longVertex r (by omega) (j+1) := by
  apply Fin.ne_of_val_ne
  by_cases hj1 : j=1
  · subst j
    have h0 := longVertex_zero r (show 2≤r by omega)
    have h2 := longVertex_inner r (show 2≤r by omega) 2 (by omega) (by omega)
    rw [h0,h2]
    change (0:ℕ) ≠ 7
    omega
  · have hm := longVertex_inner r (show 2≤r by omega) (j-1) (by omega) (by omega)
    rw [hm]
    by_cases hp : j+1=r
    · rw [hp,longVertex_last]
      change j-1+5 ≠ 1
      omega
    · have hplus := longVertex_inner r (show 2≤r by omega) (j+1) (by omega) (by omega)
      rw [hplus]
      change j-1+5 ≠ j+1+5
      omega

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

open Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

private theorem mixed_theta_eq (r : ℕ) (hr : 2 ≤ r) (e : ℝ) :
    mixedMatrix (thetaGraph r hr) (thetaGraph r hr) (1-e) =
      (thetaGraph r hr).degMatrix ℝ - e • (thetaGraph r hr).adjMatrix ℝ := by
  ext i j
  by_cases hij : i = j <;> by_cases ha : (thetaGraph r hr).Adj i j <;>
    simp [mixedMatrix,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,hij,ha]
  <;> ring

private theorem theta_operator_row (r : ℕ) (hr : 2 ≤ r) (e : ℝ)
    (f : Fin (r+5) → ℝ) (v : Fin (r+5)) :
    (mixedMatrix (thetaGraph r hr) (thetaGraph r hr) (1-(e:ℝ)) *ᵥ f) v =
      (thetaGraph r hr).degree v*f v-e*∑ w ∈ (thetaGraph r hr).neighborFinset v, f w := by
  rw [mixed_theta_eq]
  simp [Matrix.sub_mulVec,Matrix.smul_mulVec,
    SimpleGraph.degMatrix_mulVec_apply,SimpleGraph.adjMatrix_mulVec_apply]

private theorem eigen_neighbor_equation (r : ℕ) (hr : 2 ≤ r)
    (e t : ℝ) (he : e^2=1)
    (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r hr) (thetaGraph r hr) (1-(e:ℝ)))) (2-e*t))
    (v : Fin (r+5)) :
    (∑ w ∈ (thetaGraph r hr).neighborFinset v, f w) =
      (t+e*((thetaGraph r hr).degree v-2))*f v := by
  have h := congrFun (Module.End.mem_eigenspace_iff.mp hf) v
  simp only [Matrix.toLin'_apply,theta_operator_row,Pi.smul_apply,smul_eq_mul] at h
  linear_combination -e*h + (t*f v-∑ w ∈ (thetaGraph r hr).neighborFinset v, f w)*he

private theorem eigen_row_0 (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t)) :
    f ⟨2,by omega⟩ + f ⟨4,by omega⟩ + f ⟨6,by omega⟩ = (t+e)*f ⟨0,by omega⟩ := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf ⟨0,by omega⟩
  have hn := neighbors_0 r hr
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,hn] at h
  norm_num [Fin.ext_iff,show r+4≠3 by omega,show r+4≠5 by omega,
    show 3≠r+4 by omega,show 5≠r+4 by omega,add_assoc] at h
  simpa [add_assoc] using h

private theorem eigen_row_1 (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t)) :
    f ⟨3,by omega⟩ + f ⟨5,by omega⟩ + f ⟨r+4,by omega⟩ = (t+e)*f ⟨1,by omega⟩ := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf ⟨1,by omega⟩
  have hn := neighbors_1 r hr
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,hn] at h
  norm_num [Fin.ext_iff,show r+4≠3 by omega,show r+4≠5 by omega,
    show 3≠r+4 by omega,show 5≠r+4 by omega,add_assoc] at h
  simpa [add_assoc] using h

private theorem eigen_row_2 (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t)) :
    f ⟨0,by omega⟩ + f ⟨3,by omega⟩ = t*f ⟨2,by omega⟩ := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf ⟨2,by omega⟩
  have hn := neighbors_2 r hr
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,hn] at h
  norm_num [Fin.ext_iff,show r+4≠3 by omega,show r+4≠5 by omega,
    show 3≠r+4 by omega,show 5≠r+4 by omega,add_assoc] at h
  simpa [add_assoc] using h

private theorem eigen_row_3 (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t)) :
    f ⟨2,by omega⟩ + f ⟨1,by omega⟩ = t*f ⟨3,by omega⟩ := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf ⟨3,by omega⟩
  have hn := neighbors_3 r hr
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,hn] at h
  norm_num [Fin.ext_iff,show r+4≠3 by omega,show r+4≠5 by omega,
    show 3≠r+4 by omega,show 5≠r+4 by omega,add_assoc] at h
  simpa [add_assoc] using h

private theorem eigen_row_4 (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t)) :
    f ⟨0,by omega⟩ + f ⟨5,by omega⟩ = t*f ⟨4,by omega⟩ := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf ⟨4,by omega⟩
  have hn := neighbors_4 r hr
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,hn] at h
  norm_num [Fin.ext_iff,show r+4≠3 by omega,show r+4≠5 by omega,
    show 3≠r+4 by omega,show 5≠r+4 by omega,add_assoc] at h
  simpa [add_assoc] using h

private theorem eigen_row_5 (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t)) :
    f ⟨4,by omega⟩ + f ⟨1,by omega⟩ = t*f ⟨5,by omega⟩ := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf ⟨5,by omega⟩
  have hn := neighbors_5 r hr
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,hn] at h
  norm_num [Fin.ext_iff,show r+4≠3 by omega,show r+4≠5 by omega,
    show 3≠r+4 by omega,show 5≠r+4 by omega,add_assoc] at h
  simpa [add_assoc] using h

private theorem eigen_row_long (r : ℕ) (hr : 10 ≤ r)
    (e t : ℝ) (he : e^2=1) (f : Fin (r+5) → ℝ)
    (hf : f ∈ Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph r (by omega)) (thetaGraph r (by omega)) (1-(e:ℝ)))) (2-e*t))
    (j : ℕ) (hj : 0<j) (hjr : j<r) :
    f (longVertex r (by omega) (j-1)) + f (longVertex r (by omega) (j+1)) =
      t*f (longVertex r (by omega) j) := by
  have h := eigen_neighbor_equation r (by omega) e t he f hf (longVertex r (by omega) j)
  simp only [←SimpleGraph.card_neighborFinset_eq_degree,neighbors_long r hr j hj hjr] at h
  simpa [long_neighbors_distinct r hr j hj hjr] using h

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

private def graphCoordinates (k : ℕ) (hk : 1 ≤ k) (e t : ℝ) (he : e^2=1) :
    ThetaCoordinates
      (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t))
      k t e where
  A := (LinearMap.proj ⟨0,by omega⟩).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  D := (LinearMap.proj ⟨1,by omega⟩).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  B := (LinearMap.proj ⟨2,by omega⟩).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  C := (LinearMap.proj ⟨3,by omega⟩).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  B' := (LinearMap.proj ⟨4,by omega⟩).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  C' := (LinearMap.proj ⟨5,by omega⟩).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  Y j := (LinearMap.proj (longVertex (6*k+4) (by omega) j)).comp (Module.End.eigenspace (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)).subtype
  first := by ext x; simp [longVertex_zero]
  last := by ext x; simp [longVertex_last]
  shortB := by intro x; have h := eigen_row_2 (6*k+4) (by omega) e t he x.val x.property; simpa [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using h.symm
  shortC := by intro x; have h := eigen_row_3 (6*k+4) (by omega) e t he x.val x.property; simpa [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using h.symm
  shortB' := by intro x; have h := eigen_row_4 (6*k+4) (by omega) e t he x.val x.property; simpa [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using h.symm
  shortC' := by intro x; have h := eigen_row_5 (6*k+4) (by omega) e t he x.val x.property; simpa [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using h.symm
  left := by
    intro x
    have h := eigen_row_0 (6*k+4) (by omega) e t he x.val x.property
    simp [longVertex,show 1<6*k+4 by omega] at h ⊢
    linarith
  right := by
    intro x
    have h := eigen_row_1 (6*k+4) (by omega) e t he x.val x.property
    simp [longVertex,show 6*k+3≠0 by omega,show 6*k+3<6*k+4 by omega]
    convert (show x.val ⟨6*k+8,by omega⟩ =
      (t+e)*x.val ⟨1,by omega⟩-x.val ⟨3,by omega⟩-x.val ⟨5,by omega⟩ by linarith) using 1 <;> congr 1 <;> omega
  recurrence := by
    intro j hj x
    have h := eigen_row_long (6*k+4) (by omega) e t he x.val x.property (j+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel,Nat.add_assoc] at h
    dsimp [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
    linarith
  separates := by
    intro x ha hd hb hc hb' hc' hy
    apply Subtype.ext
    funext v
    change x.val v=0
    by_cases hv : v.val<6
    · have hcases : v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 ∨ v.val=4 ∨ v.val=5 := by omega
      rcases hcases with hv|hv|hv|hv|hv|hv
      · have hev : v=⟨0,by omega⟩ := Fin.ext hv
        simpa [hev] using ha
      · have hev : v=⟨1,by omega⟩ := Fin.ext hv
        simpa [hev] using hd
      · have hev : v=⟨2,by omega⟩ := Fin.ext hv
        simpa [hev] using hb
      · have hev : v=⟨3,by omega⟩ := Fin.ext hv
        simpa [hev] using hc
      · have hev : v=⟨4,by omega⟩ := Fin.ext hv
        simpa [hev] using hb'
      · have hev : v=⟨5,by omega⟩ := Fin.ext hv
        simpa [hev] using hc'
    · have hl := v.isLt
      have h := hy (v.val-5) (by omega)
      have heq : longVertex (6*k+4) (by omega) (v.val-5)=v := by
        apply Fin.ext
        simp [longVertex,show v.val-5≠0 by omega,show v.val-5<6*k+4 by omega]
        omega
      simpa [heq] using h

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

private theorem graph_coordinates_exist (k : ℕ) (hk : 1 ≤ k)
    (e t : ℝ) (he : e^2=1) :
    Nonempty (ThetaCoordinates
      (Module.End.eigenspace
        (Matrix.toLin' (mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(e:ℝ)))) (2-e*t)) k t e) :=
  ⟨graphCoordinates k hk e t he⟩

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

/-- The coefficient pattern of the symmetric lambda=1 Laplacian eigenvector. -/
private def periodSix (j : ℕ) : ℝ :=
  if j%6=0 ∨ j%6=1 then 1 else if j%6=3 ∨ j%6=4 then -1 else 0

private theorem periodSix_recurrence (j : ℕ) (hj : 0<j) :
    periodSix (j-1)+periodSix (j+1)=periodSix j := by
  unfold periodSix
  split_ifs <;> norm_num <;> omega

private def thetaLiftLinear (k : ℕ) : (ℝ × ℝ) →ₗ[ℝ] (Fin (6*k+9) → ℝ) :=
  LinearMap.pi fun v =>
    if v.val=0 then LinearMap.fst ℝ ℝ ℝ else
    if v.val=1 then -(LinearMap.fst ℝ ℝ ℝ) else
    if v.val=2 then LinearMap.snd ℝ ℝ ℝ else
    if v.val=3 then LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ else
    if v.val=4 then LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ else
    if v.val=5 then -(LinearMap.snd ℝ ℝ ℝ) else
    periodSix (v.val-5) • LinearMap.fst ℝ ℝ ℝ

private theorem thetaLiftLinear_apply (k : ℕ) (z : ℝ × ℝ) (v : Fin (6*k+9)) :
    thetaLiftLinear k z v =
      if v.val=0 then z.1 else if v.val=1 then -z.1 else
      if v.val=2 then z.2 else if v.val=3 then z.2-z.1 else
      if v.val=4 then z.1-z.2 else if v.val=5 then -z.2 else
      periodSix (v.val-5)*z.1 := by
  dsimp [thetaLiftLinear]
  split_ifs <;> rfl

private theorem thetaLift_long (k : ℕ) (hk : 1≤k) (A B : ℝ) (j : ℕ)
    (hj : j≤6*k+4) :
    thetaLiftLinear k (A,B) (longVertex (6*k+4) (by omega) j)=periodSix j*A := by
  by_cases hz : j=0
  · subst j; simp [longVertex,thetaLiftLinear_apply,periodSix]
  by_cases hi : j<6*k+4
  · rw [longVertex_inner _ (by omega) j (by omega) hi]
    simp [thetaLiftLinear_apply,hz,show j+5≠0 by omega,show j+5≠1 by omega,
      show j+5≠2 by omega,show j+5≠3 by omega,show j+5≠4 by omega,
      show j+5≠5 by omega,show j+5-5=j by omega]
  · have heq : j=6*k+4 := by omega
    subst j
    rw [longVertex_last]
    simp [thetaLiftLinear_apply,periodSix,Nat.add_mod,Nat.mul_mod]

private theorem thetaLift_eigen (k : ℕ) (hk : 1≤k) (A B : ℝ) :
    thetaLiftLinear k (A,B) ∈ Module.End.eigenspace
      (Matrix.toLin' ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ)) 1 := by
  apply Module.End.mem_eigenspace_iff.mpr
  funext v
  simp only [Matrix.toLin'_apply,SimpleGraph.lapMatrix_mulVec_apply,Pi.smul_apply,one_smul]
  have hv := v.isLt
  by_cases hs : v.val<6
  · have hc : v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 ∨ v.val=4 ∨ v.val=5 := by omega
    rcases hc with h|h|h|h|h|h
    all_goals
      simp only [←SimpleGraph.card_neighborFinset_eq_degree]
    · have heq : v=⟨0,by omega⟩ := Fin.ext h
      rw [heq]
      rw [neighbors_0 (6*k+4) (by omega)]
      simp [neighbors_0 (6*k+4) (by omega),thetaLiftLinear_apply,periodSix,Nat.add_mod,Nat.mul_mod]
      <;> ring
    · have heq : v=⟨1,by omega⟩ := Fin.ext h
      rw [heq]
      rw [neighbors_1 (6*k+4) (by omega)]
      simp [neighbors_1 (6*k+4) (by omega),thetaLiftLinear_apply,periodSix,Nat.add_mod,Nat.mul_mod,
        show 6*k+8≠0 by omega,show 6*k+8≠1 by omega,show 6*k+8≠2 by omega,show 6*k+8≠3 by omega,show 6*k+8≠4 by omega,show 6*k+8≠5 by omega]
      <;> ring
    · have heq : v=⟨2,by omega⟩ := Fin.ext h
      rw [heq]
      rw [neighbors_2 (6*k+4) (by omega)]
      simp [neighbors_2 (6*k+4) (by omega),thetaLiftLinear_apply] <;> ring
    · have heq : v=⟨3,by omega⟩ := Fin.ext h
      rw [heq]
      rw [neighbors_3 (6*k+4) (by omega)]
      simp [neighbors_3 (6*k+4) (by omega),thetaLiftLinear_apply] <;> ring
    · have heq : v=⟨4,by omega⟩ := Fin.ext h
      rw [heq]
      rw [neighbors_4 (6*k+4) (by omega)]
      simp [neighbors_4 (6*k+4) (by omega),thetaLiftLinear_apply] <;> ring
    · have heq : v=⟨5,by omega⟩ := Fin.ext h
      rw [heq]
      rw [neighbors_5 (6*k+4) (by omega)]
      simp [neighbors_5 (6*k+4) (by omega),thetaLiftLinear_apply] <;> ring
  · let j := v.val-5
    have hj : 0<j := by dsimp [j];omega
    have hjr : j<6*k+4 := by dsimp [j];omega
    have heq : v=longVertex (6*k+4) (by omega) j := by
      apply Fin.ext
      simp [longVertex,show j≠0 by omega,hjr]
      dsimp [j];omega
    rw [heq]
    simp only [←SimpleGraph.card_neighborFinset_eq_degree,neighbors_long _ (by omega) j hj hjr]
    simp [long_neighbors_distinct _ (by omega) j hj hjr,
      thetaLift_long k hk A B _ (show j-1≤6*k+4 by omega),
      thetaLift_long k hk A B _ (show j+1≤6*k+4 by omega),
      thetaLift_long k hk A B _ (show j≤6*k+4 by omega)]
    linear_combination -A*periodSix_recurrence j hj

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

private theorem thetaLift_injective (k : ℕ) : Function.Injective (thetaLiftLinear k) := by
  intro z w h
  have h0 := congrFun h ⟨0,by omega⟩
  have h2 := congrFun h ⟨2,by omega⟩
  apply Prod.ext
  · simpa [thetaLiftLinear_apply] using h0
  · simpa [thetaLiftLinear_apply] using h2

private theorem theta_laplacian_multiplicity_lower (k : ℕ) (hk : 1≤k) :
    2 ≤ TwinFreeThetaStructure.multiplicity ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ) 1 := by
  let S := Module.End.eigenspace
    (Matrix.toLin' ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ)) 1
  let f : (ℝ × ℝ) →ₗ[ℝ] S := (thetaLiftLinear k).codRestrict S
    (fun z => thetaLift_eigen k hk z.1 z.2)
  have hi : Function.Injective f := by
    intro z w h
    exact thetaLift_injective k (congrArg Subtype.val h)
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  simpa [S,TwinFreeThetaStructure.multiplicity] using hd

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation

private theorem theta_laplacian_multiplicity_upper (k : ℕ) (hk : 1≤k) (l : ℝ) :
    TwinFreeThetaStructure.multiplicity ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ) l ≤ 2 := by
  let E := Module.End.eigenspace
    (Matrix.toLin' ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ)) l
  have hM : mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-(1:ℝ)) =
      (thetaGraph (6*k+4) (by omega)).lapMatrix ℝ := by
    rw [mixed_theta_eq]
    simp [SimpleGraph.lapMatrix]
  have hl : 2-(1:ℝ)*(2-l)=l := by ring
  let m : ThetaCoordinates E k (2-l) 1 := by
    have H := graph_coordinates_exist k hk 1 (2-l) (by norm_num)
    rw [hM,hl] at H
    exact Classical.choice H
  change Module.finrank ℝ E ≤ 2
  by_cases ht : 2-l=1
  · exact model_laplacian_singular_finrank k (2-l) (Or.inl ht) m
  by_cases ht' : 2-l= -1
  · exact model_laplacian_singular_finrank k (2-l) (Or.inr ht') m
  exact (model_nonsingular_finrank k 1 (Or.inl rfl) (2-l) ht ht' (by simpa using m)).trans (by omega)

private theorem source_signless_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    sourceMatrix G .signless = (by classical exact G.degMatrix ℝ + G.adjMatrix ℝ) := by
  classical
  ext i j
  by_cases h : i = j <;> simp [sourceMatrix, SimpleGraph.degMatrix, h]

private theorem theta_signless_multiplicity_upper (k : ℕ) (hk : 1≤k) (l : ℝ) :
    TwinFreeThetaStructure.multiplicity (sourceMatrix (thetaGraph (6*k+4) (by omega)) .signless) l ≤ 1 := by
  let E := Module.End.eigenspace
    (Matrix.toLin' (sourceMatrix (thetaGraph (6*k+4) (by omega)) .signless)) l
  have hM : mixedMatrix (thetaGraph (6*k+4) (by omega)) (thetaGraph (6*k+4) (by omega)) (1-((-1):ℝ)) =
      sourceMatrix (thetaGraph (6*k+4) (by omega)) .signless := by
    rw [mixed_theta_eq,source_signless_eq]
    ext i j
    by_cases hij : i = j <;> by_cases ha : (thetaGraph (6*k+4) (by omega)).Adj i j <;>
      simp [SimpleGraph.degMatrix,hij,ha]
  have hl : 2-(-1:ℝ)*(l-2)=l := by ring
  let m : ThetaCoordinates E k (l-2) (-1) := by
    have H := graph_coordinates_exist k hk (-1) (l-2) (by norm_num)
    rw [hM,hl] at H
    exact Classical.choice H
  change Module.finrank ℝ E ≤ 1
  by_cases ht : l-2=1
  · exact model_signless_singular_finrank k (l-2) (Or.inl ht) m
  by_cases ht' : l-2= -1
  · exact model_signless_singular_finrank k (l-2) (Or.inr ht') m
  exact model_nonsingular_finrank k (-1) (Or.inr rfl) (l-2) ht ht' (by simpa using m)

private theorem theta_maximum_multiplicities (k : ℕ) (hk : 1≤k) :
    mmL (thetaGraph (6*k+4) (by omega))=2 ∧ mmQ (thetaGraph (6*k+4) (by omega))≤1 := by
  have hmL : mmL (thetaGraph (6*k+4) (by omega)) =
      maximumMultiplicity ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ) := by
    exact Nat.add_zero _
  rw [hmL]
  have hL := theta_laplacian_multiplicity_upper k hk
  have hQ := theta_signless_multiplicity_upper k hk
  have hL2 := theta_laplacian_multiplicity_lower k hk
  have heig : Module.End.HasEigenvalue
      (Matrix.toLin' ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ)) 1 := by
    apply Module.End.hasEigenvalue_iff.mpr
    intro hz
    have hzero : TwinFreeThetaStructure.multiplicity ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ) 1=0 := by
      simp [TwinFreeThetaStructure.multiplicity,hz]
    omega
  constructor
  · apply Nat.le_antisymm
    · apply csSup_le'
      rintro n ⟨l,hl,rfl⟩
      exact hL l
    · have hb : BddAbove {m : ℕ | ∃ l : ℝ,
          Module.End.HasEigenvalue
            (Matrix.toLin' ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ)) l ∧
          m=TwinFreeThetaStructure.multiplicity ((thetaGraph (6*k+4) (by omega)).lapMatrix ℝ) l} := by
        refine ⟨2,?_⟩
        rintro n ⟨l,hl,rfl⟩
        exact hL l
      exact hL2.trans (le_csSup hb ⟨1,heig,rfl⟩)
  · apply csSup_le'
    rintro n ⟨l,hl,rfl⟩
    simpa only [source_signless_eq, signlessLaplacian] using hQ l

/-- Problem 30: an infinite family up to graph isomorphism, with exactly one equality per graph. -/
def claim : Prop :=
  ∃ orders : ℕ → ℕ,
    ∃ graphs : (i : ℕ) → SimpleGraph (Fin (orders i)),
      (∀ i : ℕ, (graphs i).Connected ∧ TwinFree (graphs i) ∧
        ((mmL (graphs i) = metricDimension (graphs i) ∧
            mmQ (graphs i) ≠ metricDimension (graphs i)) ∨
          (mmQ (graphs i) = metricDimension (graphs i) ∧
            mmL (graphs i) ≠ metricDimension (graphs i)))) ∧
      (∀ i j : ℕ, i ≠ j → ¬ Nonempty ((graphs i).Iso (graphs j)))

theorem result : claim := by
  refine ⟨fun i=>6*(i+1)+9,fun i=>thetaGraph (6*(i+1)+4) (by omega),?_,?_⟩
  · intro i
    have hc := theta_metric_certificates (i+1) (by omega)
    have hm := hc.2.2
    have he := theta_maximum_multiplicities (i+1) (by omega)
    refine ⟨hc.1,hc.2.1,Or.inl ⟨?_,?_⟩⟩
    · exact he.1.trans hm.symm
    · rw [hm]
      exact ne_of_lt (lt_of_le_of_lt he.2 (by decide))
  · intro i j hij he
    obtain ⟨e⟩ := he
    have hc := Fintype.card_congr e.toEquiv
    simp only [Fintype.card_fin] at hc
    exact hij (by omega)

end D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaSeparation
