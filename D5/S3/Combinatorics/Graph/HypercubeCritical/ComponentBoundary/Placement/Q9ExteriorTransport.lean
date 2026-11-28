import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization

/-!
# Coordinate transport through two-neighbor exterior rows

An exterior row with two selected neighbors transports the absolute value of a
parity kernel by the ratio of their coordinate weights. The gains of successive
rows add in the free abelian group on the coordinates. Testing one doubled
weight at a time shows that the total gain depends only on the endpoints.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9ExteriorTransport

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open private normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open Q9IsotropicHuang (flipSign parity weightedAction weightedLinear weightedLinear_apply)
open Q9WeightedSaturation (defect signedBiadjacency)
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

abbrev Exponent := Fin 9 → ℤ

/-- The coordinate basis vector in the free abelian group on the nine axes. -/
def axis (i : Fin 9) : Exponent := Pi.single i 1

/-- A two-step exterior path through `z` has gain `axis i - axis j` when
the path enters `z` on axis `i` and leaves on axis `j`. -/
inductive Walk (C : Finset (Q 9)) : Q 9 → Q 9 → Exponent → Prop
  | nil (x : Q 9) : Walk C x x 0
  | step {x z : Q 9} {gain : Exponent} {i j : Fin 9}
      (path : Walk C x (flip z i) gain) (hne : i ≠ j)
      (hout : z ∉ C) (hrow : directions C z = {i, j}) :
      Walk C x (flip z j) (gain + (axis i - axis j))

private theorem absolute_row {C : Finset (Q 9)} {w : Fin 9 → ℝ} {f : Q 9 → ℝ}
    (hw : ∀ i, 0 < w i) (hs : ∀ x ∉ C, f x = 0)
    {z : Q 9} {i j : Fin 9} (hij : i ≠ j) (hrow : directions C z = {i, j})
    (hzero : weightedLinear w f z = 0) :
    w j * |f (flip z j)| = w i * |f (flip z i)| := by
  let t (k : Fin 9) := w k * (flipSign k z : ℝ) * f (flip z k)
  rw [weightedLinear_apply] at hzero
  change (∑ k, t k) = 0 at hzero
  have hfilt : (∑ k ∈ directions C z, t k) = ∑ k, t k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    exact mul_eq_zero_of_right _ (hs _ (fun h => hk ((mem_directions C z k).mpr h)))
  rw [← hfilt, hrow, Finset.sum_pair hij] at hzero
  have habs : |t j| = |t i| := by
    rw [show t j = -t i by linarith, abs_neg]
  have hunit (k : Fin 9) : |(flipSign k z : ℝ)| = 1 := by
    rw [flipSign_cast]
    exact SupportedEigenSaturation.matrix_abs_of_adj (flip_adj z k)
  simpa only [t, abs_mul, hunit, abs_of_pos (hw _), mul_one] using habs

private theorem axis_value (i k : Fin 9) :
    (2 : ℝ) ^ axis i k = if i = k then 2 else 1 := by
  by_cases hik : i = k
  · simp [axis, Pi.single_apply, hik]
  · simp [axis, Pi.single_apply, hik, Ne.symm hik]

private theorem walk_value {C : Finset (Q 9)} {f : Q 9 → ℝ} (k : Fin 9)
    (hs : ∀ x ∉ C, f x = 0)
    (hout : ∀ z ∉ C, weightedLinear (fun i => if i = k then 2 else 1) f z = 0)
    {x y : Q 9} {gain : Exponent} (walk : Walk C x y gain) :
    |f y| = (2 : ℝ) ^ gain k * |f x| := by
  induction walk with
  | nil => simp
  | @step z gain i j path hij hz hrow ih =>
    let w (i : Fin 9) : ℝ := if i = k then 2 else 1
    have hw (i : Fin 9) : 0 < w i := by
      dsimp only [w]
      split <;> norm_num
    have hval := absolute_row hw hs hij hrow (hout z hz)
    apply mul_left_cancel₀ (ne_of_gt (hw j))
    rw [hval, ih]
    change w i * ((2 : ℝ) ^ gain k * |f x|) =
      w j * ((2 : ℝ) ^ (gain k + (axis i k - axis j k)) * |f x|)
    have hwi : w i = (2 : ℝ) ^ axis i k := (axis_value i k).symm
    have hwj : w j = (2 : ℝ) ^ axis j k := (axis_value j k).symm
    rw [hwi, hwj, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hn : (2 : ℝ) ^ axis j k ≠ 0 := zpow_ne_zero _ (by norm_num)
    field_simp [hn]
    <;> ring

open Classical in
/-- Two exterior walks in a universally saturated component with the same
endpoints have identical coordinate gains. In particular a closed exterior
walk has zero gain. -/
theorem gain_eq_of_endpoints {C : Finset (Q 9)} {x y : Q 9} {g h : Exponent}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hb : IsBalanced C)
    (hdet : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hx : x ∈ C) (p : Walk C x y g) (q : Walk C x y h) : g = h := by
  funext k
  let w (i : Fin 9) : ℝ := if i = k then 2 else 1
  have hw (i : Fin 9) : 0 < w i := by
    dsimp only [w]
    split <;> norm_num
  obtain ⟨f, hf, hext⟩ :=
    exists_both_parity_supported_of_signed_defect_singular C hr hc hb w hw (hdet w) (parity x)
  have hs (v : Q 9) (hv : v ∉ C) : f v = 0 := by
    by_contra hn
    exact hv ((hf v).mp hn).1
  have hnonzero : |f x| ≠ 0 := abs_ne_zero.mpr ((hf x).mpr ⟨hx, rfl⟩)
  apply zpow_right_injective₀ (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1)
  exact mul_right_cancel₀ hnonzero ((walk_value k hs hext p).symm.trans (walk_value k hs hext q))

/-- The coordinate gains of exterior walks depend only on their endpoints. -/
def GainConsistent (C : Finset (Q 9)) : Prop :=
  ∀ ⦃x y : Q 9⦄ ⦃g h : Exponent⦄, x ∈ C → Walk C x y g → Walk C x y h → g = h

private theorem map_walk {C : Finset (Q 9)} (e : Q 9 ≃ Q 9) (σ : Equiv.Perm (Fin 9))
    (hflip : ∀ z i, e (flip z i) = flip (e z) (σ i))
    {x y : Q 9} {g : Exponent} (p : Walk C x y g) :
    Walk (C.map e.toEmbedding) (e x) (e y) (g ∘ σ.symm) := by
  induction p with
  | nil => exact Walk.nil _
  | @step z gain i j path hij hout hrow ih =>
    have hz : e z ∉ C.map e.toEmbedding := by
      simpa using hout
    have hdirs : directions (C.map e.toEmbedding) (e z) = {σ i, σ j} := by
      ext a
      obtain ⟨k, rfl⟩ := σ.surjective a
      rw [mem_directions, ← hflip]
      have hk : flip z k ∈ C ↔ k ∈ ({i, j} : Finset (Fin 9)) := by
        rw [← mem_directions, hrow]
      simpa only [Equiv.coe_toEmbedding, mem_map_equiv, Equiv.symm_apply_apply,
        mem_insert, mem_singleton, Equiv.apply_eq_iff_eq] using hk
    have hgain : (gain + (axis i - axis j)) ∘ σ.symm =
        gain ∘ σ.symm + (axis (σ i) - axis (σ j)) := by
      funext k
      simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, axis,
        Pi.single_apply, σ.symm_apply_eq]
    rw [hflip, hgain]
    rw [hflip] at ih
    exact Walk.step ih (σ.injective.ne hij) hz hdirs

/-- Coordinate permutations and translations preserve consistency of exterior gains. -/
theorem normalize_gain_consistent {C : Finset (Q 9)} (hC : GainConsistent C)
    (σ : Equiv.Perm (Fin 9)) (z : Q 9) :
    GainConsistent (C.map (normalize σ z).toEmbedding) := by
  let e := normalize σ z
  intro x y g h hx p q
  have hflip (v : Q 9) (i : Fin 9) : e.symm (flip v i) = flip (e.symm v) (σ i) := by
    apply e.injective
    have hf := normalize_flip σ.symm z (e.symm v) (σ i)
    simpa [e] using hf.symm
  have hmap : (C.map e.toEmbedding).map e.symm.toEmbedding = C := by
    rw [map_map]
    simp
  have hp := map_walk e.symm σ hflip p
  have hq := map_walk e.symm σ hflip q
  rw [hmap] at hp hq
  have hx' : e.symm x ∈ C := by simpa [e] using hx
  have hsame := hC hx' hp hq
  funext i
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun hsame (σ i)

#print axioms gain_eq_of_endpoints
#print axioms normalize_gain_consistent

end Q9ExteriorTransport
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
