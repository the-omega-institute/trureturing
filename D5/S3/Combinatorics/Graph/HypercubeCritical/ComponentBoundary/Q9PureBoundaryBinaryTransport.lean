/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureBoundaryBinaryTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureBoundaryBinaryTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A closed odd-degree region filters a binary kernel support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-! A closed exterior region of odd internal degree transfers a binary kernel
word into a prescribed support in the nine-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9PureBoundaryBinaryTransport

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9IsotropicHuang (flipSign weightedAction weightedLinear)
open private weightedLinear_apply weightedLinear_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-- The binary characteristic function of a finite support. -/
def indicator (S : Finset (Q 9)) (x : Q 9) : ZMod 2 :=
  if x ∈ S then 1 else 0

/-- Unsigned cube adjacency over the binary field. -/
def adjacency (f : Q 9 → ZMod 2) (x : Q 9) : ZMod 2 :=
  ∑ i : Fin 9, f (flip x i)

/-- The sum of the identity and binary adjacency. -/
def boundary (f : Q 9 → ZMod 2) : Q 9 → ZMod 2 :=
  f + adjacency f

private theorem flipSign_zmod_two {n : ℕ} (i : Fin n) (x : Q n) :
    (flipSign i x : ZMod 2) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero => simp [flipSign]
    | succ i =>
      rw [flipSign, Fin.cases_succ, Int.cast_mul, ih]
      cases x 0 <;> simp [ZModModule.neg_eq_self]

private theorem adjacency_eq_weightedAction (f : Q 9 → ZMod 2) :
    adjacency f = weightedAction (fun _ => 1) f := by
  funext x
  simp [adjacency, weightedAction, flipSign_zmod_two]

private theorem adjacency_square (f : Q 9 → ZMod 2) : adjacency (adjacency f) = f := by
  have hsum : (∑ _i : Fin 9, (1 : ZMod 2) ^ 2) = 1 := by
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin] <;> decide
  have hA : weightedLinear (fun _ => (1 : ZMod 2)) * weightedLinear (fun _ => 1) = 1 := by
    rw [weightedLinear_square, hsum, one_smul]
  simpa only [Module.End.mul_apply, Module.End.one_apply, weightedLinear_apply,
    ← adjacency_eq_weightedAction] using LinearMap.congr_fun hA f

private theorem adjacency_add (f g : Q 9 → ZMod 2) :
    adjacency (f + g) = adjacency f + adjacency g := by
  funext x
  exact Finset.sum_add_distrib

private theorem boundary_add (f g : Q 9 → ZMod 2) :
    boundary (f + g) = boundary f + boundary g := by
  unfold boundary
  rw [adjacency_add]
  abel

private theorem boundary_square (f : Q 9 → ZMod 2) : boundary (boundary f) = 0 := by
  unfold boundary
  rw [adjacency_add, adjacency_square]
  calc
    _ = (f + f) + (adjacency f + adjacency f) := by abel
    _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, zero_add]

private theorem boundary_indicator (S : Finset (Q 9)) (x : Q 9) :
    boundary (indicator S) x = indicator S x + ((directions S x).card : ZMod 2) := by
  change indicator S x + (∑ i : Fin 9, indicator S (flip x i)) = _
  congr 1
  classical
  simp [indicator, directions]

/-- A disjoint odd-degree region whose exterior neighbors all lie in `D` toggles
exactly the vertices with odd degree into the region. The remaining subset of a
binary kernel support is again a binary kernel support. -/
theorem filter_even_boundary_kernel (D P : Finset (Q 9))
    (hD : boundary (indicator D) = 0) (hdisjoint : Disjoint D P)
    (hodd : ∀ p ∈ P, Odd (directions P p).card)
    (hclosed : ∀ p ∈ P, ∀ x, (hypercube 9).Adj p x → x ∉ P → x ∈ D) :
    let R := D.filter fun x => Even (directions P x).card
    indicator R = indicator D + boundary (indicator P) ∧ boundary (indicator R) = 0 := by
  dsimp only
  have hword : indicator (D.filter fun x => Even (directions P x).card) =
      indicator D + boundary (indicator P) := by
    funext x
    rw [Pi.add_apply, boundary_indicator]
    by_cases hxD : x ∈ D
    · have hxP : x ∉ P := fun h => (Finset.disjoint_left.mp hdisjoint) hxD h
      by_cases heven : Even (directions P x).card
      · simp [indicator, hxD, hxP, heven, heven.natCast_zmod_two]
      · have hone := (Nat.not_even_iff_odd.mp heven).natCast_zmod_two
        simp [indicator, hxD, hxP, heven, hone, ZModModule.add_self]
    · by_cases hxP : x ∈ P
      · simp [indicator, hxD, hxP, (hodd x hxP).natCast_zmod_two, ZModModule.add_self]
      · have hnone : directions P x = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact hxD (hclosed _ ((mem_directions P x i).mp hi) x (flip_adj x i).symm hxP)
        simp [indicator, hxD, hxP, hnone]
  exact ⟨hword, by rw [hword, boundary_add, hD, boundary_square, zero_add]⟩

end Q9PureBoundaryBinaryTransport
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
