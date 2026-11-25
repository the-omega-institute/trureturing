/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/EightCubeBits
   generality: G
   mirror-B: none(waiver:covered-by-q9-paired-weight-sixteen-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: An eight-cube bit chart for relabeling, shells and binary adjacency. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
import Mathlib.Data.Finset.SymmDiff

/-! The little-endian bit chart identifies finite words with binary functions on the cube.
Translations and coordinate permutations preserve the Hamming metric and transport neighbor shells. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.EightCubeBits

open Finset
open scoped BigOperators symmDiff
open BalancedCriticalSpectrum (Q flip)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open private adjacency_add from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel

abbrev Vertex := Fin (2 ^ 8)

abbrev Word := Finset Vertex

def cube : Vertex ≃ Q 8 :=
  (show Vertex ≃ BitVec 8 from
    { toFun := BitVec.ofFin
      invFun := BitVec.toFin
      left_inv := fun _ => rfl
      right_inv := fun x => by cases x; rfl }).trans (cubeBitVec 8)

def toggle (x : Vertex) (i : Fin 8) : Vertex :=
  (BitVec.ofFin x ^^^ BitVec.ofNat 8 (2 ^ i.val)).toFin

@[simp] theorem cube_toggle (x : Vertex) (i : Fin 8) :
    cube (toggle x i) = flip (cube x) i := by
  change cubeBitVec 8 (BitVec.ofFin x ^^^ BitVec.ofNat 8 (2 ^ i.val)) = _
  rw [cubeBitVec_xor_single]
  rfl

theorem toggle_injective (x : Vertex) : Function.Injective (toggle x) := by
  intro i j h
  apply BalancedCubeComponentBoundary.flip_injective (cube x)
  simpa only [cube_toggle] using congrArg cube h

@[simp] private theorem toggle_twice (x : Vertex) (i : Fin 8) :
    toggle (toggle x i) i = x := by
  apply cube.injective
  simp

def shell (x : Vertex) : Word := univ.image (toggle x)

@[simp] private theorem toggle_mem_shell (x : Vertex) (i : Fin 8) :
    toggle x i ∈ shell x := mem_image.mpr ⟨i, mem_univ _, rfl⟩

/-- Adjacency between two vertices is symmetric. -/
theorem shell_symm {x y : Vertex} : x ∈ shell y ↔ y ∈ shell x := by
  have forward {u v : Vertex} (h : u ∈ shell v) : v ∈ shell u := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp h
    simpa only [toggle_twice] using toggle_mem_shell (toggle v i) i
  exact ⟨forward, forward⟩

def coeff (w : Word) (x : Vertex) : ZMod 2 := if x ∈ w then 1 else 0

def row (w : Word) (r : Vertex) : ZMod 2 := ∑ i, coeff w (toggle r i)

def IsKernel (w : Word) : Prop := ∀ r, row w r = 0

def oddRows (w : Word) : Word := univ.filter (fun r => row w r ≠ 0)

/-- A binary adjacency row is the parity of its support intersection. -/
theorem row_eq_card (w : Word) (r : Vertex) :
    row w r = ((shell r ∩ w).card : ZMod 2) := by
  have hfilter : (shell r).filter (fun x => x ∈ w) = shell r ∩ w := by
    ext x
    simp
  calc
    row w r = ∑ x ∈ shell r, coeff w x := by
      unfold shell row
      rw [sum_image]
      intro i _ j _ hij
      exact toggle_injective r hij
    _ = ∑ _x ∈ (shell r).filter (fun x => x ∈ w), (1 : ZMod 2) := by
      simpa only [coeff] using
        (Finset.sum_filter (s := shell r) (fun x => x ∈ w) (fun _ => (1 : ZMod 2))).symm
    _ = _ := by rw [hfilter, sum_const, nsmul_eq_mul, mul_one]

def distance (x y : Vertex) : ℕ := hammingDist (cube x) (cube y)

def parity (x : Vertex) : ZMod 2 := distance x 0

private theorem distance_add_mod_two (x y z : Vertex) :
    (distance x y : ZMod 2) + (distance y z : ZMod 2) = (distance x z : ZMod 2) := by
  have hsum (u v : Vertex) : (distance u v : ZMod 2) =
      ∑ a : Fin 8, if cube u a ≠ cube v a then 1 else 0 := by
    unfold distance hammingDist
    rw [← sum_filter]
    simp [sum_const, nsmul_eq_mul]
  simp only [hsum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  cases cube x i <;> cases cube y i <;> cases cube z i <;> decide

private theorem toggle_distance (x : Vertex) (i : Fin 8) : distance x (toggle x i) = 1 := by
  have hd : (univ.filter (fun a => cube x a ≠ cube (toggle x i) a)) = {i} := by
    ext a
    by_cases h : a = i
    · subst a
      cases hx : cube x i <;> simp [BalancedCriticalSpectrum.flip, hx]
    · simp [BalancedCriticalSpectrum.flip, h]
  unfold distance hammingDist
  rw [hd, card_singleton]

private theorem toggle_parity (x : Vertex) (i : Fin 8) :
    parity (toggle x i) = 1 + parity x := by
  have h := distance_add_mod_two x (toggle x i) 0
  rw [toggle_distance, Nat.cast_one] at h
  change 1 + parity (toggle x i) = parity x at h
  rw [← h, ← add_assoc]
  have h₂ : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h₂, zero_add]

private def relabelCube (σ : Equiv.Perm (Fin 8)) (r : Q 8) : Q 8 ≃ Q 8 where
  toFun x i := x (σ.symm i) != r (σ.symm i)
  invFun x i := x (σ i) != r i
  left_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply]
    cases x i <;> cases r i <;> rfl
  right_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    cases x i <;> cases r (σ.symm i) <;> rfl

def relabel (σ : Equiv.Perm (Fin 8)) (r : Vertex) : Vertex ≃ Vertex :=
  cube.trans ((relabelCube σ (cube r)).trans cube.symm)

@[simp] private theorem cube_relabel (σ : Equiv.Perm (Fin 8)) (r x : Vertex) (i : Fin 8) :
    cube (relabel σ r x) i = (cube x (σ.symm i) != cube r (σ.symm i)) := by
  change cube (cube.symm _) i = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] private theorem cube_zero_apply (i : Fin 8) : cube (0 : Vertex) i = false := by
  change (BitVec.ofFin (w := 8) (0 : Vertex)).getLsbD i.val = false
  simp

private theorem relabel_center (σ : Equiv.Perm (Fin 8)) (r : Vertex) :
    relabel σ r r = 0 := by
  apply cube.injective
  funext i
  rw [cube_relabel, cube_zero_apply]
  cases cube r (σ.symm i) <;> rfl

private theorem relabel_toggle (σ : Equiv.Perm (Fin 8)) (r x : Vertex) (i : Fin 8) :
    relabel σ r (toggle x i) = toggle (relabel σ r x) (σ i) := by
  apply cube.injective
  funext j
  by_cases hj : j = σ i
  · subst j
    simp only [cube_toggle, BalancedCriticalSpectrum.flip_apply_same, cube_relabel,
      Equiv.symm_apply_apply]
    cases cube x i <;> cases cube r i <;> rfl
  · have hi : σ.symm j ≠ i := fun h => hj ((σ.symm_apply_eq).mp h)
    simp [cube_toggle, cube_relabel, BalancedCriticalSpectrum.flip, hi, hj]

/-- The affine action preserves Hamming distance. -/
theorem relabel_distance (σ : Equiv.Perm (Fin 8)) (r x y : Vertex) :
    distance (relabel σ r x) (relabel σ r y) = distance x y := by
  have h (i : Fin 8) : cube (relabel σ r x) i ≠ cube (relabel σ r y) i ↔
      cube x (σ.symm i) ≠ cube y (σ.symm i) := by
    simp only [cube_relabel]
    cases cube x (σ.symm i) <;> cases cube y (σ.symm i) <;>
      cases cube r (σ.symm i) <;> decide
  unfold distance hammingDist
  simp_rw [h]
  apply card_bij (fun i _ => σ.symm i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact σ.symm.injective hij
  · intro i hi
    refine ⟨σ i, mem_filter.mpr ⟨mem_univ _, ?_⟩, σ.symm_apply_apply i⟩
    simpa only [Equiv.symm_apply_apply] using (mem_filter.mp hi).2

private theorem relabel_shell (σ : Equiv.Perm (Fin 8)) (r x : Vertex) :
    (shell x).map (relabel σ r).toEmbedding = shell (relabel σ r x) := by
  ext z
  simp only [mem_map, shell, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨σ i, (relabel_toggle σ r x i).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨toggle x (σ.symm j), ⟨σ.symm j, rfl⟩,
      by change relabel σ r (toggle x (σ.symm j)) = _
         rw [relabel_toggle, Equiv.apply_symm_apply]⟩

/-- Interpret a finite support as a binary word on the repository cube. -/
def asFunction (w : Word) (x : Q 8) : ZMod 2 := coeff w (cube.symm x)

theorem adjacency_asFunction (w : Word) (r : Vertex) :
    adjacency (asFunction w) (cube r) = row w r := by
  unfold adjacency row
  apply sum_congr rfl
  intro i _
  have ht := congrArg cube.symm (cube_toggle r i)
  simp only [Equiv.symm_apply_apply] at ht
  rw [asFunction, ← ht]

theorem isKernel_iff_adjacency (w : Word) : IsKernel w ↔ adjacency (asFunction w) = 0 := by
  constructor
  · intro h
    funext x
    obtain ⟨r, rfl⟩ := cube.surjective x
    exact (adjacency_asFunction w r).trans (h r)
  · intro h r
    exact (adjacency_asFunction w r).symm.trans (congrFun h (cube r))

theorem row_singleton (x y : Vertex) : row {x} y = coeff (shell x) y := by
  rw [row_eq_card]
  by_cases h : y ∈ shell x
  · have he : shell y ∩ {x} = {x} := inter_eq_right.mpr
      (singleton_subset_iff.mpr (shell_symm.mp h))
    simp [he, coeff, h]
  · have he : shell y ∩ {x} = ∅ := by
      ext z
      simp only [mem_inter, mem_singleton, notMem_empty, iff_false]
      rintro ⟨hz, rfl⟩
      exact h (shell_symm.mp hz)
    simp [he, coeff, h]

private theorem shell_asFunction (x : Vertex) :
    asFunction (shell x) = adjacency (asFunction {x}) := by
  funext y
  obtain ⟨r, rfl⟩ := cube.surjective y
  rw [adjacency_asFunction, row_singleton]
  simp [asFunction]

theorem asFunction_symmDiff (u v : Word) :
    asFunction (u ∆ v) = asFunction u + asFunction v := by
  funext x
  simp only [asFunction, Pi.add_apply, coeff, mem_symmDiff]
  by_cases hu : cube.symm x ∈ u <;> by_cases hv : cube.symm x ∈ v <;>
    simp [hu, hv, (show (1 : ZMod 2) + 1 = 0 by decide)]

/-- A binary adjacency row is additive under symmetric difference. -/
theorem row_symmDiff (A B : Word) (r : Vertex) :
    row (A ∆ B) r = row A r + row B r := by
  rw [← adjacency_asFunction (A ∆ B), asFunction_symmDiff, adjacency_add]
  simp only [Pi.add_apply, adjacency_asFunction]

private theorem shell_xor_card_at_origin :
    ∀ x : Vertex, distance 0 x = 2 → (shell 0 ∆ shell x).card = 12 := by
  decide +kernel

theorem shell_xor_card {x y : Vertex} (h : distance x y = 2) :
    (shell x ∆ shell y).card = 12 := by
  let σ := Equiv.refl (Fin 8)
  let e := relabel σ x
  have hx : e x = 0 := relabel_center σ x
  have hy : distance 0 (e y) = 2 := by
    rw [← hx, relabel_distance]
    exact h
  have hm : (shell x ∆ shell y).map e.toEmbedding = shell 0 ∆ shell (e y) := by
    ext z
    obtain ⟨a, rfl⟩ := e.surjective z
    have hs (v : Vertex) : e a ∈ shell (e v) ↔ a ∈ shell v := by
      rw [← relabel_shell σ x v]
      exact mem_map' _
    rw [← hx]
    simp only [mem_map_equiv, Equiv.symm_apply_apply, mem_symmDiff, hs]
  simpa only [← hm, card_map] using shell_xor_card_at_origin (e y) hy

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.EightCubeBits
