/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition
   mirror-E: none(waiver:kernel-checked-cone-construction)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.finite_cone_transfer; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/BoundaryConeDecomposition.rays
   digest: Two boundary halfspaces admit a conical decomposition into thirty-three rays. -/

/-
proof_shape: finite_cone_transfer: content
escape_witness: HalfspaceConeTransfer.halfspace_transfer; both successive
  halfspace cuts use its constructive positive-negative cancellation decomposition.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option maxHeartbeats 12000000
open Matrix
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.BoundaryConeDecomposition
open HalfspaceConeTransfer

def firstRow : Fin 9 → ℝ := ![-1,-2,-3,-2,-1,0,1,2,3]
def secondRow : Fin 9 → ℝ := ![-1,-1,-1,-1,-1,-1,0,1,2]
def rays : Fin 33 → (Fin 9 → ℝ) := ![![0,0,0,0,0,0,1,0,0],
![0,0,0,0,0,0,0,1,0],
![0,0,0,0,0,0,0,0,1],
![1,0,0,0,0,0,0,1,0],
![2,0,0,0,0,0,0,0,1],
![0,2,0,0,0,0,0,2,0],
![0,1,0,0,0,0,0,1,0],
![0,3,0,0,0,0,0,0,2],
![0,0,2,0,0,0,0,3,0],
![0,0,3,0,0,0,0,0,3],
![0,0,0,2,0,0,0,2,0],
![0,0,0,1,0,0,0,1,0],
![0,0,0,3,0,0,0,0,2],
![0,0,0,0,1,0,0,1,0],
![0,0,0,0,2,0,0,0,1],
![0,0,0,0,0,1,0,1,0],
![0,0,0,0,0,2,0,0,1],
![1,1,0,0,0,0,0,0,1],
![1,0,1,0,0,0,0,2,0],
![3,0,1,0,0,0,0,0,2],
![1,0,0,1,0,0,0,0,1],
![0,1,0,0,1,0,0,0,1],
![0,3,0,0,0,1,0,0,2],
![0,2,0,0,0,0,1,0,1],
![0,0,1,0,1,0,0,2,0],
![0,0,1,0,3,0,0,0,2],
![0,0,2,0,0,1,0,3,0],
![0,0,3,0,0,3,0,0,3],
![0,0,1,0,0,0,1,1,0],
![0,0,2,0,0,0,3,0,1],
![0,0,0,1,1,0,0,0,1],
![0,0,0,3,0,1,0,0,2],
![0,0,0,2,0,0,1,0,1]]
private def stages : Fin 19 → (Fin 9 → ℝ) := ![![0,0,0,0,0,1,0,0,0],
![0,0,0,0,0,0,1,0,0],
![0,0,0,0,0,0,0,1,0],
![0,0,0,0,0,0,0,0,1],
![1,0,0,0,0,0,1,0,0],
![0,1,0,0,0,0,2,0,0],
![0,0,1,0,0,0,3,0,0],
![0,0,0,1,0,0,2,0,0],
![0,0,0,0,1,0,1,0,0],
![2,0,0,0,0,0,0,1,0],
![0,2,0,0,0,0,0,2,0],
![0,0,2,0,0,0,0,3,0],
![0,0,0,2,0,0,0,2,0],
![0,0,0,0,2,0,0,1,0],
![3,0,0,0,0,0,0,0,1],
![0,3,0,0,0,0,0,0,2],
![0,0,3,0,0,0,0,0,3],
![0,0,0,3,0,0,0,0,2],
![0,0,0,0,3,0,0,0,1]]
private def stageC : Fin 19 → ℝ := ![-1,0,1,2,-1,-1,-1,-1,-1,-1,0,1,0,-1,-1,1,3,1,-1]
theorem finite_cone_transfer
    (Good : (Fin 9 → ℝ) → Prop) (hzero : Good 0)
    (hadd : ∀ u v, Good u → Good v → Good (u+v))
    (hsmul : ∀ (t : ℝ) u, 0 ≤ t → Good u → Good (t • u))
    (hr : ∀ r, Good (rays r)) (y : Fin 9 → ℝ) (hy : ∀ j, 0 ≤ y j)
    (hL : 0 ≤ ∑ j, y j*firstRow j) (hC : 0 ≤ ∑ j, y j*secondRow j) : Good y := by
  have halfspace_hull_transfer
      (Good : (Fin 9 → ℝ) → Prop) (hzero : Good 0)
      (hadd : ∀ u v, Good u → Good v → Good (u+v))
      (hsmul : ∀ (t : ℝ) u, 0 ≤ t → Good u → Good (t • u))
      (S : Set (Fin 9 → ℝ)) (b : (Fin 9 → ℝ) →ₗ[ℝ] ℝ) (u : (Fin 9 → ℝ)) (hu : u ∈ PointedCone.hull ℝ S)
      (hb : 0 ≤ b u)
      (hpos : ∀ v ∈ S, 0 ≤ b v → Good v)
      (hpair : ∀ v ∈ S, ∀ w ∈ S, 0 < b v → b w < 0 → Good ((-b w) • v + b v • w)) : Good u := by
    classical
    obtain ⟨c,hc,hc0,he⟩ := (PointedCone.mem_hull_set).mp hu
    have hs : (∑ i : c.support, c i • (i : (Fin 9 → ℝ))) = u := by
      change (∑ i ∈ c.support, c i • i) = u at he
      rw [← Finset.sum_attach c.support (fun i : (Fin 9 → ℝ) => c i • i)] at he
      simpa only [Finset.univ_eq_attach] using he
    have hsum : 0 ≤ ∑ i : c.support, c i * b (i : (Fin 9 → ℝ)) := by
      have h := hb
      rw [← hs,map_sum] at h
      simpa only [map_smul,smul_eq_mul] using h
    rw [← hs]
    apply halfspace_transfer Good hzero hadd hsmul (fun i : c.support => (i : (Fin 9 → ℝ)))
      (fun i => b (i : (Fin 9 → ℝ))) (fun i => c i) (fun i => hc0 i) hsum
    · intro i hi
      exact hpos i (hc i.property) hi
    · intro i j hi hj
      exact hpair i (hc i.property) j (hc j.property) hi hj

  have stage_C (i : Fin 19) : ((dotProductBilin ℝ ℝ).flip secondRow) (stages i) = stageC i := by
    fin_cases i <;> simp [dotProductBilin, LinearMap.flip, dotProduct,stages,secondRow,stageC,Fin.sum_univ_succ] <;> norm_num

  let H := PointedCone.hull ℝ (Set.range stages)
  have hyH : y ∈ H := by
    have he : (∑ j, y j • ((Pi.single (M := fun _ : Fin 9 => ℝ) j (1 : ℝ)) : Fin 9 → ℝ)) = y := by
      ext j; simp [Pi.single_apply,Finset.sum_ite_eq,eq_comm]
    rw [← he]
    apply halfspace_transfer (fun x => x ∈ H) H.zero_mem
      (fun _ _ hu hv => H.add_mem hu hv)
      (fun t u ht hu => PointedCone.smul_mem H ht hu)
      (fun j => (Pi.single (M := fun _ : Fin 9 => ℝ) j (1 : ℝ))) firstRow y hy hL
    · intro i hi
      fin_cases i <;> norm_num [firstRow] at hi

      · have he : ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 5 : Fin 9 → ℝ)=stages 0 := by
          ext q; fin_cases q <;> rfl
        change ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 5 : Fin 9 → ℝ) ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 0)
      · have he : ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)=stages 1 := by
          ext q; fin_cases q <;> rfl
        change ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ) ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 1)
      · have he : ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)=stages 2 := by
          ext q; fin_cases q <;> rfl
        change ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ) ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 2)
      · have he : ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)=stages 3 := by
          ext q; fin_cases q <;> rfl
        change ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ) ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 3)
    · intro i j hi hj
      fin_cases i <;> norm_num [firstRow] at hi
      all_goals fin_cases j <;> norm_num [firstRow] at hj
      · have he : (-firstRow 0) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 0 = stages 4 := by
          ext q; fin_cases q
          all_goals first | change ((-(-1)) * 0+(1) * 1 : ℝ) = (1 : ℝ) | change ((-(-1)) * 0+(1) * 0 : ℝ) = (0 : ℝ) | change ((-(-1)) * 1+(1) * 0 : ℝ) = (1 : ℝ)
          all_goals norm_num
        change (-firstRow 0) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 0 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 4)
      · have he : (-firstRow 1) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 1 = stages 5 := by
          ext q; fin_cases q
          all_goals first | change ((-(-2)) * 0+(1) * 0 : ℝ) = (0 : ℝ) | change ((-(-2)) * 0+(1) * 1 : ℝ) = (1 : ℝ) | change ((-(-2)) * 1+(1) * 0 : ℝ) = (2 : ℝ)
          all_goals norm_num
        change (-firstRow 1) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 1 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 5)
      · have he : (-firstRow 2) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 2 = stages 6 := by
          ext q; fin_cases q
          all_goals first | change ((-(-3)) * 0+(1) * 0 : ℝ) = (0 : ℝ) | change ((-(-3)) * 0+(1) * 1 : ℝ) = (1 : ℝ) | change ((-(-3)) * 1+(1) * 0 : ℝ) = (3 : ℝ)
          all_goals norm_num
        change (-firstRow 2) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 2 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 6)
      · have he : (-firstRow 3) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 3 = stages 7 := by
          ext q; fin_cases q
          all_goals first | change ((-(-2)) * 0+(1) * 0 : ℝ) = (0 : ℝ) | change ((-(-2)) * 0+(1) * 1 : ℝ) = (1 : ℝ) | change ((-(-2)) * 1+(1) * 0 : ℝ) = (2 : ℝ)
          all_goals norm_num
        change (-firstRow 3) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 3 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 7)
      · have he : (-firstRow 4) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 4 = stages 8 := by
          ext q; fin_cases q
          all_goals first | change ((-(-1)) * 0+(1) * 0 : ℝ) = (0 : ℝ) | change ((-(-1)) * 0+(1) * 1 : ℝ) = (1 : ℝ) | change ((-(-1)) * 1+(1) * 0 : ℝ) = (1 : ℝ)
          all_goals norm_num
        change (-firstRow 4) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 6 : Fin 9 → ℝ)+firstRow 6 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 4 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 8)
      · have he : (-firstRow 0) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 0 = stages 9 := by
          ext q; fin_cases q
          all_goals first | change ((-(-1)) * 0+(2) * 1 : ℝ) = (2 : ℝ) | change ((-(-1)) * 0+(2) * 0 : ℝ) = (0 : ℝ) | change ((-(-1)) * 1+(2) * 0 : ℝ) = (1 : ℝ)
          all_goals norm_num
        change (-firstRow 0) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 0 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 9)
      · have he : (-firstRow 1) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 1 = stages 10 := by
          ext q; fin_cases q
          all_goals first | change ((-(-2)) * 0+(2) * 0 : ℝ) = (0 : ℝ) | change ((-(-2)) * 0+(2) * 1 : ℝ) = (2 : ℝ) | change ((-(-2)) * 1+(2) * 0 : ℝ) = (2 : ℝ)
          all_goals norm_num
        change (-firstRow 1) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 1 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 10)
      · have he : (-firstRow 2) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 2 = stages 11 := by
          ext q; fin_cases q
          all_goals first | change ((-(-3)) * 0+(2) * 0 : ℝ) = (0 : ℝ) | change ((-(-3)) * 0+(2) * 1 : ℝ) = (2 : ℝ) | change ((-(-3)) * 1+(2) * 0 : ℝ) = (3 : ℝ)
          all_goals norm_num
        change (-firstRow 2) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 2 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 11)
      · have he : (-firstRow 3) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 3 = stages 12 := by
          ext q; fin_cases q
          all_goals first | change ((-(-2)) * 0+(2) * 0 : ℝ) = (0 : ℝ) | change ((-(-2)) * 0+(2) * 1 : ℝ) = (2 : ℝ) | change ((-(-2)) * 1+(2) * 0 : ℝ) = (2 : ℝ)
          all_goals norm_num
        change (-firstRow 3) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 3 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 12)
      · have he : (-firstRow 4) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 4 = stages 13 := by
          ext q; fin_cases q
          all_goals first | change ((-(-1)) * 0+(2) * 0 : ℝ) = (0 : ℝ) | change ((-(-1)) * 0+(2) * 1 : ℝ) = (2 : ℝ) | change ((-(-1)) * 1+(2) * 0 : ℝ) = (1 : ℝ)
          all_goals norm_num
        change (-firstRow 4) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 7 : Fin 9 → ℝ)+firstRow 7 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 4 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 13)
      · have he : (-firstRow 0) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 0 = stages 14 := by
          ext q; fin_cases q
          all_goals first | change ((-(-1)) * 0+(3) * 1 : ℝ) = (3 : ℝ) | change ((-(-1)) * 0+(3) * 0 : ℝ) = (0 : ℝ) | change ((-(-1)) * 1+(3) * 0 : ℝ) = (1 : ℝ)
          all_goals norm_num
        change (-firstRow 0) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 0 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 14)
      · have he : (-firstRow 1) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 1 = stages 15 := by
          ext q; fin_cases q
          all_goals first | change ((-(-2)) * 0+(3) * 0 : ℝ) = (0 : ℝ) | change ((-(-2)) * 0+(3) * 1 : ℝ) = (3 : ℝ) | change ((-(-2)) * 1+(3) * 0 : ℝ) = (2 : ℝ)
          all_goals norm_num
        change (-firstRow 1) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 1 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 15)
      · have he : (-firstRow 2) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 2 = stages 16 := by
          ext q; fin_cases q
          all_goals first | change ((-(-3)) * 0+(3) * 0 : ℝ) = (0 : ℝ) | change ((-(-3)) * 0+(3) * 1 : ℝ) = (3 : ℝ) | change ((-(-3)) * 1+(3) * 0 : ℝ) = (3 : ℝ)
          all_goals norm_num
        change (-firstRow 2) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 2 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 16)
      · have he : (-firstRow 3) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 3 = stages 17 := by
          ext q; fin_cases q
          all_goals first | change ((-(-2)) * 0+(3) * 0 : ℝ) = (0 : ℝ) | change ((-(-2)) * 0+(3) * 1 : ℝ) = (3 : ℝ) | change ((-(-2)) * 1+(3) * 0 : ℝ) = (2 : ℝ)
          all_goals norm_num
        change (-firstRow 3) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 3 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 17)
      · have he : (-firstRow 4) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 4 = stages 18 := by
          ext q; fin_cases q
          all_goals first | change ((-(-1)) * 0+(3) * 0 : ℝ) = (0 : ℝ) | change ((-(-1)) * 0+(3) * 1 : ℝ) = (3 : ℝ) | change ((-(-1)) * 1+(3) * 0 : ℝ) = (1 : ℝ)
          all_goals norm_num
        change (-firstRow 4) • ((fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 8 : Fin 9 → ℝ)+firstRow 8 • (fun i : Fin 9 => Pi.single (M := fun _ : Fin 9 => ℝ) i (1 : ℝ)) 4 ∈ H
        rw [he]
        exact PointedCone.subset_hull (Set.mem_range_self 18)
  apply halfspace_hull_transfer Good hzero hadd hsmul (Set.range stages) (((dotProductBilin ℝ ℝ).flip secondRow)) y hyH hC
  · rintro v ⟨i,rfl⟩ hi
    rw [stage_C] at hi
    fin_cases i <;> norm_num [stageC] at hi
    · have he : stages 1 = (1 : ℝ) • rays 0 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (1 : ℝ) = (1 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 1)
      have hg : Good (stages 1) := by
        rw [he]
        exact hsmul 1 (rays 0) (by norm_num) (hr 0)
      simpa only [one_smul] using hg
    · have he : stages 2 = (1 : ℝ) • rays 1 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (1 : ℝ) = (1 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 2)
      have hg : Good (stages 2) := by
        rw [he]
        exact hsmul 1 (rays 1) (by norm_num) (hr 1)
      simpa only [one_smul] using hg
    · have he : stages 3 = (1 : ℝ) • rays 2 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (1 : ℝ) = (1 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 3)
      have hg : Good (stages 3) := by
        rw [he]
        exact hsmul 1 (rays 2) (by norm_num) (hr 2)
      simpa only [one_smul] using hg
    · have he : stages 10 = (1 : ℝ) • rays 5 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (2 : ℝ) = (1 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 10)
      have hg : Good (stages 10) := by
        rw [he]
        exact hsmul 1 (rays 5) (by norm_num) (hr 5)
      simpa only [one_smul] using hg
    · have he : stages 11 = (1 : ℝ) • rays 8 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (2 : ℝ) = (1 * 2 : ℝ) | change (3 : ℝ) = (1 * 3 : ℝ)
        all_goals norm_num
      change Good (stages 11)
      have hg : Good (stages 11) := by
        rw [he]
        exact hsmul 1 (rays 8) (by norm_num) (hr 8)
      simpa only [one_smul] using hg
    · have he : stages 12 = (1 : ℝ) • rays 10 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (2 : ℝ) = (1 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 12)
      have hg : Good (stages 12) := by
        rw [he]
        exact hsmul 1 (rays 10) (by norm_num) (hr 10)
      simpa only [one_smul] using hg
    · have he : stages 15 = (1 : ℝ) • rays 7 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (3 : ℝ) = (1 * 3 : ℝ) | change (2 : ℝ) = (1 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 15)
      have hg : Good (stages 15) := by
        rw [he]
        exact hsmul 1 (rays 7) (by norm_num) (hr 7)
      simpa only [one_smul] using hg
    · have he : stages 16 = (1 : ℝ) • rays 9 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (3 : ℝ) = (1 * 3 : ℝ)
        all_goals norm_num
      change Good (stages 16)
      have hg : Good (stages 16) := by
        rw [he]
        exact hsmul 1 (rays 9) (by norm_num) (hr 9)
      simpa only [one_smul] using hg
    · have he : stages 17 = (1 : ℝ) • rays 12 := by
        ext q; fin_cases q
        all_goals first | change (0 : ℝ) = (1 * 0 : ℝ) | change (3 : ℝ) = (1 * 3 : ℝ) | change (2 : ℝ) = (1 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 17)
      have hg : Good (stages 17) := by
        rw [he]
        exact hsmul 1 (rays 12) (by norm_num) (hr 12)
      simpa only [one_smul] using hg
  · rintro v ⟨i,rfl⟩ w ⟨j,rfl⟩ hi hj
    rw [stage_C] at hi hj
    fin_cases i <;> norm_num [stageC] at hi
    all_goals fin_cases j <;> norm_num [stageC] at hj
    all_goals rw [stage_C,stage_C]
    all_goals norm_num [stageC]
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 0 = (1 : ℝ) • rays 15 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (1 * 0 : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (1 * 1 : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = (1 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 0)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 0) := by
        rw [he]
        exact hsmul 1 (rays 15) (by norm_num) (hr 15)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 4 = ((1 : ℝ) • rays 0)+((1 : ℝ) • rays 3) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 4)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 4) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 3) (by norm_num) (hr 3))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 5 = ((2 : ℝ) • rays 0)+((1/2 : ℝ) • rays 5) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((2 * 0)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((2 * 0)+((1/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = ((2 * 1)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((2 * 0)+((1/2 : ℝ) * 2) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 5)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 5) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 0) (by norm_num) (hr 0)) (hsmul (1/2 : ℝ) (rays 5) (by norm_num) (hr 5))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 6 = ((2 : ℝ) • rays 0)+((1 : ℝ) • rays 28) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((2 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((2 * 0)+(1 * 1) : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = ((2 * 1)+(1 * 1) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((2 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 6)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 6) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 28) (by norm_num) (hr 28))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 7 = ((2 : ℝ) • rays 0)+((1/2 : ℝ) • rays 10) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((2 * 0)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((2 * 0)+((1/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = ((2 * 1)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((2 * 0)+((1/2 : ℝ) * 2) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 7)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 7) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 0) (by norm_num) (hr 0)) (hsmul (1/2 : ℝ) (rays 10) (by norm_num) (hr 10))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 8 = ((1 : ℝ) • rays 0)+((1 : ℝ) • rays 13) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 8)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 8) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 13) (by norm_num) (hr 13))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 9 = (2 : ℝ) • rays 3 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 2 : ℝ) = (2 * 1 : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (2 * 0 : ℝ) | change (1 * 1 + 1 * 1 : ℝ) = (2 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 9)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 9) := by
        rw [he]
        exact hsmul 2 (rays 3) (by norm_num) (hr 3)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 13 = (2 : ℝ) • rays 13 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (2 * 0 : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (2 * 1 : ℝ) | change (1 * 1 + 1 * 1 : ℝ) = (2 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 13)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 13) := by
        rw [he]
        exact hsmul 2 (rays 13) (by norm_num) (hr 13)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 14 = ((1 : ℝ) • rays 3)+((1 : ℝ) • rays 4) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 3 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 14)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 14) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 3) (by norm_num) (hr 3)) (hsmul 1 (rays 4) (by norm_num) (hr 4))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 2 + (1 : ℝ) • stages 18 = ((1 : ℝ) • rays 13)+((1 : ℝ) • rays 14) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 1 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 2 + stages 18)
      have hg : Good ((1 : ℝ) • stages 2 + (1 : ℝ) • stages 18) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 13) (by norm_num) (hr 13)) (hsmul 1 (rays 14) (by norm_num) (hr 14))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 0 = (1 : ℝ) • rays 16 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = (1 * 0 : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = (1 * 2 : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = (1 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 0)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 0) := by
        rw [he]
        exact hsmul 1 (rays 16) (by norm_num) (hr 16)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 4 = ((2 : ℝ) • rays 0)+((1 : ℝ) • rays 4) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 1 : ℝ) = ((2 * 0)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((2 * 1)+(1 * 0) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 4)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 4) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 4) (by norm_num) (hr 4))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 5 = ((3 : ℝ) • rays 0)+((1 : ℝ) • rays 23) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = ((3 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((3 * 0)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 2 : ℝ) = ((3 * 1)+(1 * 1) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((3 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 5)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 5) := by
        rw [he]
        exact hadd _ _ (hsmul 3 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 23) (by norm_num) (hr 23))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 6 = ((3 : ℝ) • rays 0)+((1 : ℝ) • rays 29) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = ((3 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((3 * 0)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 3 : ℝ) = ((3 * 1)+(1 * 3) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((3 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 6)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 6) := by
        rw [he]
        exact hadd _ _ (hsmul 3 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 29) (by norm_num) (hr 29))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 7 = ((3 : ℝ) • rays 0)+((1 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = ((3 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((3 * 0)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 2 : ℝ) = ((3 * 1)+(1 * 1) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((3 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 7)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 7) := by
        rw [he]
        exact hadd _ _ (hsmul 3 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 8 = ((2 : ℝ) • rays 0)+((1 : ℝ) • rays 14) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((2 * 0)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((2 * 1)+(1 * 0) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 8)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 8) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 0) (by norm_num) (hr 0)) (hsmul 1 (rays 14) (by norm_num) (hr 14))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 9 = ((2 : ℝ) • rays 3)+((1 : ℝ) • rays 4) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 2 : ℝ) = ((2 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((2 * 1)+(1 * 0) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 9)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 9) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 3) (by norm_num) (hr 3)) (hsmul 1 (rays 4) (by norm_num) (hr 4))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 13 = ((2 : ℝ) • rays 13)+((1 : ℝ) • rays 14) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 2 * 2 : ℝ) = ((2 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 2 * 1 : ℝ) = ((2 * 1)+(1 * 0) : ℝ) | change (1 * 1 + 2 * 0 : ℝ) = ((2 * 0)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 13)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 13) := by
        rw [he]
        exact hadd _ _ (hsmul 2 (rays 13) (by norm_num) (hr 13)) (hsmul 1 (rays 14) (by norm_num) (hr 14))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 14 = (3 : ℝ) • rays 4 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 3 : ℝ) = (3 * 2 : ℝ) | change (1 * 0 + 2 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 1 + 2 * 1 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 14)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 14) := by
        rw [he]
        exact hsmul 3 (rays 4) (by norm_num) (hr 4)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 3 + (2 : ℝ) • stages 18 = (3 : ℝ) • rays 14 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 2 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 0 + 2 * 3 : ℝ) = (3 * 2 : ℝ) | change (1 * 1 + 2 * 1 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 3 + (2 : ℝ) • stages 18)
      have hg : Good ((1 : ℝ) • stages 3 + (2 : ℝ) • stages 18) := by
        rw [he]
        exact hsmul 3 (rays 14) (by norm_num) (hr 14)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 0 = (1 : ℝ) • rays 26 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (1 * 0 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (1 * 2 : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (1 * 1 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (1 * 3 : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 0)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 0) := by
        rw [he]
        exact hsmul 1 (rays 26) (by norm_num) (hr 26)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 4 = ((1 : ℝ) • rays 18)+((1 : ℝ) • rays 28) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = ((1 * 2)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 4)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 4) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 18) (by norm_num) (hr 18)) (hsmul 1 (rays 28) (by norm_num) (hr 28))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 5 = ((1/2 : ℝ) • rays 5)+((2 : ℝ) • rays 28) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 5)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 5) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 5) (by norm_num) (hr 5)) (hsmul 2 (rays 28) (by norm_num) (hr 28))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 6 = (3 : ℝ) • rays 28 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 2 + 1 * 1 : ℝ) = (3 * 1 : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = (3 * 1 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 6)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 6) := by
        rw [he]
        exact hsmul 3 (rays 28) (by norm_num) (hr 28)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 7 = ((1/2 : ℝ) • rays 10)+((2 : ℝ) • rays 28) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 0) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 7)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 7) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 10) (by norm_num) (hr 10)) (hsmul 2 (rays 28) (by norm_num) (hr 28))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 8 = ((1 : ℝ) • rays 24)+((1 : ℝ) • rays 28) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = ((1 * 2)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 8)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 8) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 24) (by norm_num) (hr 24)) (hsmul 1 (rays 28) (by norm_num) (hr 28))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 9 = (2 : ℝ) • rays 18 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 2 : ℝ) = (2 * 1 : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (2 * 0 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (2 * 1 : ℝ) | change (1 * 3 + 1 * 1 : ℝ) = (2 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 9)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 9) := by
        rw [he]
        exact hsmul 2 (rays 18) (by norm_num) (hr 18)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 13 = (2 : ℝ) • rays 24 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (2 * 0 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (2 * 1 : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (2 * 1 : ℝ) | change (1 * 3 + 1 * 1 : ℝ) = (2 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 13)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 13) := by
        rw [he]
        exact hsmul 2 (rays 24) (by norm_num) (hr 24)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 14 = ((3/2 : ℝ) • rays 18)+((1/2 : ℝ) • rays 19) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 3 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 3) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 1) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 2)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 2) : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 14)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 14) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 18) (by norm_num) (hr 18)) (hsmul (1/2 : ℝ) (rays 19) (by norm_num) (hr 19))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 11 + (1 : ℝ) • stages 18 = ((3/2 : ℝ) • rays 24)+((1/2 : ℝ) • rays 25) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 1) : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 3) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 2)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 2) : ℝ)
        all_goals norm_num
      change Good (stages 11 + stages 18)
      have hg : Good ((1 : ℝ) • stages 11 + (1 : ℝ) • stages 18) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 24) (by norm_num) (hr 24)) (hsmul (1/2 : ℝ) (rays 25) (by norm_num) (hr 25))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 0 = (1 : ℝ) • rays 22 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (1 * 0 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (1 * 3 : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (1 * 1 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (1 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 0)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 0) := by
        rw [he]
        exact hsmul 1 (rays 22) (by norm_num) (hr 22)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 4 = ((1 : ℝ) • rays 17)+((1 : ℝ) • rays 23) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 4)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 4) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 17) (by norm_num) (hr 17)) (hsmul 1 (rays 23) (by norm_num) (hr 23))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 5 = (2 : ℝ) • rays 23 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (2 * 0 : ℝ) | change (1 * 3 + 1 * 1 : ℝ) = (2 * 2 : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (2 * 1 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (2 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 5)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 5) := by
        rw [he]
        exact hsmul 2 (rays 23) (by norm_num) (hr 23)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 6 = ((3/2 : ℝ) • rays 23)+((1/2 : ℝ) • rays 29) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 2)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 3) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 1) : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 6)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 6) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 23) (by norm_num) (hr 23)) (hsmul (1/2 : ℝ) (rays 29) (by norm_num) (hr 29))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 7 = ((3/2 : ℝ) • rays 23)+((1/2 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 2)+((1/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((3/2 : ℝ) * 0)+((1/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((1/2 : ℝ) * 1) : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 7)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 7) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 23) (by norm_num) (hr 23)) (hsmul (1/2 : ℝ) (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 8 = ((1 : ℝ) • rays 21)+((1 : ℝ) • rays 23) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 8)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 8) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 21) (by norm_num) (hr 21)) (hsmul 1 (rays 23) (by norm_num) (hr 23))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 9 = ((1/2 : ℝ) • rays 5)+((2 : ℝ) • rays 17) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 9)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 9) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 5) (by norm_num) (hr 5)) (hsmul 2 (rays 17) (by norm_num) (hr 17))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 13 = ((1/2 : ℝ) • rays 5)+((2 : ℝ) • rays 21) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 13)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 13) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 5) (by norm_num) (hr 5)) (hsmul 2 (rays 21) (by norm_num) (hr 21))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 14 = (3 : ℝ) • rays 17 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 3 : ℝ) = (3 * 1 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (3 * 1 : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 2 + 1 * 1 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 14)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 14) := by
        rw [he]
        exact hsmul 3 (rays 17) (by norm_num) (hr 17)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 15 + (1 : ℝ) • stages 18 = (3 : ℝ) • rays 21 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (3 * 1 : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = (3 * 1 : ℝ) | change (1 * 2 + 1 * 1 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 15 + stages 18)
      have hg : Good ((1 : ℝ) • stages 15 + (1 : ℝ) • stages 18) := by
        rw [he]
        exact hsmul 3 (rays 21) (by norm_num) (hr 21)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 0 = (1 : ℝ) • rays 27 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = (1 * 0 : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (1 * 3 : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = (1 * 3 : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 0)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 0) := by
        rw [he]
        exact hsmul 1 (rays 27) (by norm_num) (hr 27)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 4 = ((1 : ℝ) • rays 19)+((1 : ℝ) • rays 29) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 1 : ℝ) = ((1 * 3)+(1 * 0) : ℝ) | change (1 * 0 + 3 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = ((1 * 0)+(1 * 3) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = ((1 * 2)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 4)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 4) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 19) (by norm_num) (hr 19)) (hsmul 1 (rays 29) (by norm_num) (hr 29))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 5 = ((3/2 : ℝ) • rays 23)+((3/2 : ℝ) • rays 29) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = (((3/2 : ℝ) * 2)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 3 * 2 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 3) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 5)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 5) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 23) (by norm_num) (hr 23)) (hsmul (3/2 : ℝ) (rays 29) (by norm_num) (hr 29))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 6 = (3 : ℝ) • rays 29 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 3 + 3 * 1 : ℝ) = (3 * 2 : ℝ) | change (1 * 0 + 3 * 3 : ℝ) = (3 * 3 : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 6)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 6) := by
        rw [he]
        exact hsmul 3 (rays 29) (by norm_num) (hr 29)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 7 = ((3/2 : ℝ) • rays 29)+((3/2 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 2)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 3 * 2 : ℝ) = (((3/2 : ℝ) * 3)+((3/2 : ℝ) * 1) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 7)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 7) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 29) (by norm_num) (hr 29)) (hsmul (3/2 : ℝ) (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 8 = ((1 : ℝ) • rays 25)+((1 : ℝ) • rays 29) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = ((1 * 3)+(1 * 0) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = ((1 * 0)+(1 * 3) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = ((1 * 2)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 8)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 8) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 25) (by norm_num) (hr 25)) (hsmul 1 (rays 29) (by norm_num) (hr 29))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 9 = ((3/2 : ℝ) • rays 18)+((3/2 : ℝ) • rays 19) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 2 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 3) : ℝ) | change (1 * 0 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = (((3/2 : ℝ) * 2)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 2) : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 9)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 9) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 18) (by norm_num) (hr 18)) (hsmul (3/2 : ℝ) (rays 19) (by norm_num) (hr 19))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 13 = ((3/2 : ℝ) • rays 24)+((3/2 : ℝ) • rays 25) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ) | change (1 * 0 + 3 * 2 : ℝ) = (((3/2 : ℝ) * 1)+((3/2 : ℝ) * 3) : ℝ) | change (1 * 0 + 3 * 1 : ℝ) = (((3/2 : ℝ) * 2)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (((3/2 : ℝ) * 0)+((3/2 : ℝ) * 2) : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 13)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 13) := by
        rw [he]
        exact hadd _ _ (hsmul (3/2 : ℝ) (rays 24) (by norm_num) (hr 24)) (hsmul (3/2 : ℝ) (rays 25) (by norm_num) (hr 25))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 14 = (3 : ℝ) • rays 19 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 3 : ℝ) = (3 * 3 : ℝ) | change (1 * 0 + 3 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (3 * 1 : ℝ) | change (1 * 3 + 3 * 1 : ℝ) = (3 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 14)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 14) := by
        rw [he]
        exact hsmul 3 (rays 19) (by norm_num) (hr 19)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 16 + (3 : ℝ) • stages 18 = (3 : ℝ) • rays 25 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 3 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 3 + 3 * 0 : ℝ) = (3 * 1 : ℝ) | change (1 * 0 + 3 * 3 : ℝ) = (3 * 3 : ℝ) | change (1 * 3 + 3 * 1 : ℝ) = (3 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 16 + (3 : ℝ) • stages 18)
      have hg : Good ((1 : ℝ) • stages 16 + (3 : ℝ) • stages 18) := by
        rw [he]
        exact hsmul 3 (rays 25) (by norm_num) (hr 25)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 0 = (1 : ℝ) • rays 31 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (1 * 0 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (1 * 3 : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (1 * 1 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (1 * 2 : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 0)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 0) := by
        rw [he]
        exact hsmul 1 (rays 31) (by norm_num) (hr 31)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 4 = ((1 : ℝ) • rays 20)+((1 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 4)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 4) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 20) (by norm_num) (hr 20)) (hsmul 1 (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 5 = ((1/2 : ℝ) • rays 23)+((3/2 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+((3/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 5)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 5) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 23) (by norm_num) (hr 23)) (hsmul (3/2 : ℝ) (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 6 = ((1/2 : ℝ) • rays 29)+((3/2 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+((3/2 : ℝ) * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+((3/2 : ℝ) * 2) : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = (((1/2 : ℝ) * 3)+((3/2 : ℝ) * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 1)+((3/2 : ℝ) * 1) : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 6)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 6) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 29) (by norm_num) (hr 29)) (hsmul (3/2 : ℝ) (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 7 = (2 : ℝ) • rays 32 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (2 * 0 : ℝ) | change (1 * 3 + 1 * 1 : ℝ) = (2 * 2 : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (2 * 1 : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (2 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 7)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 7) := by
        rw [he]
        exact hsmul 2 (rays 32) (by norm_num) (hr 32)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 8 = ((1 : ℝ) • rays 30)+((1 : ℝ) • rays 32) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = ((1 * 0)+(1 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 2) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 1)+(1 * 0) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = ((1 * 0)+(1 * 1) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = ((1 * 1)+(1 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 8)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 8) := by
        rw [he]
        exact hadd _ _ (hsmul 1 (rays 30) (by norm_num) (hr 30)) (hsmul 1 (rays 32) (by norm_num) (hr 32))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 9 = ((1/2 : ℝ) • rays 10)+((2 : ℝ) • rays 20) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 9)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 9) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 10) (by norm_num) (hr 10)) (hsmul 2 (rays 20) (by norm_num) (hr 20))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 13 = ((1/2 : ℝ) • rays 10)+((2 : ℝ) • rays 30) := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 0) : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 2 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ) | change (1 * 0 + 1 * 1 : ℝ) = (((1/2 : ℝ) * 2)+(2 * 0) : ℝ) | change (1 * 2 + 1 * 0 : ℝ) = (((1/2 : ℝ) * 0)+(2 * 1) : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 13)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 13) := by
        rw [he]
        exact hadd _ _ (hsmul (1/2 : ℝ) (rays 10) (by norm_num) (hr 10)) (hsmul 2 (rays 30) (by norm_num) (hr 30))
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 14 = (3 : ℝ) • rays 20 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 3 : ℝ) = (3 * 1 : ℝ) | change (1 * 0 + 1 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (3 * 1 : ℝ) | change (1 * 2 + 1 * 1 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 14)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 14) := by
        rw [he]
        exact hsmul 3 (rays 20) (by norm_num) (hr 20)
      simpa only [one_smul] using hg
    · have he : (1 : ℝ) • stages 17 + (1 : ℝ) • stages 18 = (3 : ℝ) • rays 30 := by
        ext q; fin_cases q
        all_goals first | change (1 * 0 + 1 * 0 : ℝ) = (3 * 0 : ℝ) | change (1 * 3 + 1 * 0 : ℝ) = (3 * 1 : ℝ) | change (1 * 0 + 1 * 3 : ℝ) = (3 * 1 : ℝ) | change (1 * 2 + 1 * 1 : ℝ) = (3 * 1 : ℝ)
        all_goals norm_num
      change Good (stages 17 + stages 18)
      have hg : Good ((1 : ℝ) • stages 17 + (1 : ℝ) • stages 18) := by
        rw [he]
        exact hsmul 3 (rays 30) (by norm_num) (hr 30)
      simpa only [one_smul] using hg

#print axioms finite_cone_transfer
#check stages
#check stageC
end D5.S3.Quantum.Entanglement.AbsolutePPT.BoundaryConeDecomposition
