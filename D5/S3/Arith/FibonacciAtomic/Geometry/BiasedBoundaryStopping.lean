/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Weak mass stopping in the original biased boundary and its actual residual. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! The actual first weak crossing, without changing the boundary law or coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H)
open FiniteSourceMass (a)
open BiasedBoundaryTrace (b Omega M G cylinder mass a_pos a_lt_one sum_weights cylinder_mass)
open BiasedBoundaryPathSplit (constG S)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open BiasedBoundaryConditionalLaw (pullback)
open BiasedBoundaryCylinderProjection (atomMean Q V V0 cylinder_ray
  cylinder_average_projection partition_centered_residual bounded_partition_residual)
open D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open D5.S0.Computability.Coding.BiasedMassFrontier
open D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality (wordMass)
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

/-- Every threshold is strictly between zero and one. -/
abbrev Threshold := Set.Ioo (0 : ℝ) 1

private noncomputable def frontier_exists (t : Threshold) :=
  biased_first_mass_frontier a b t.val (sq_pos_of_pos a_pos)
    (by change a ^ 2 ≤ a; nlinarith [a_pos, a_lt_one]) a_lt_one sum_weights
    t.property.1 t.property.2

private def words (t : Threshold) : Finset Address :=
  (frontier_exists t).choose_spec.choose

private theorem words_spec (t : Threshold) :
    (words t : Set Address) = Crossing a b t.val ∧
    (∀ w ∈ words t, w.length ≤ (frontier_exists t).choose) ∧
    IsPrefixFree (words t : Set Address) ∧
    (∀ ω : Omega, ∃! w, w ∈ words t ∧ w = rayPrefix ω w.length) ∧
    (∑ w ∈ words t, wordMass (letterMass a b) w) = 1 ∧
    (∀ w ∈ words t, b * t.val < wordMass (letterMass a b) w ∧
      wordMass (letterMass a b) w ≤ t.val) ∧
    1 / t.val ≤ ((words t).card : ℝ) ∧
      ((words t).card : ℝ) < 1 / (b * t.val) :=
  (frontier_exists t).choose_spec.choose_spec

private theorem words_nonempty (t : Threshold) (w : Address) (hw : w ∈ words t) :
    w ≠ [] := by
  have hc : w ∈ Crossing a b t.val := by
    rw [← (words_spec t).1]
    exact hw
  exact hc.1

/-- The first weak mass crossing, in the original nonempty edge coordinates. -/
def A (t : Threshold) : Finset Edge := (words t).subtype (· ≠ [])

/-- The actual average on the weak stopping cylinders. -/
def Qt (t : Threshold) : G →L[ℝ] G := Q (A t)

/-- The span of the actual stopping-cylinder indicators. -/
def Vt (t : Threshold) : Submodule ℝ G := V (A t)

/-- The mean-zero part of the actual stopping-cylinder span. -/
def Vt0 (t : Threshold) : Submodule ℝ (Vt t) := V0 (A t)

/-- The original actual mean-zero boundary space, as a subspace of G. -/
def G0 : Submodule ℝ G := LinearMap.ker mean.toLinearMap

private theorem addresses (t : Threshold) :
    Subtype.val '' (A t : Set Edge) = (words t : Set Address) := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact Finset.mem_subtype.mp hp
  · intro hw
    exact ⟨⟨w, words_nonempty t w hw⟩, Finset.mem_subtype.mpr hw, rfl⟩

private theorem card_A (t : Threshold) : (A t).card = (words t).card := by
  have he := Finset.subtype_map_of_mem (words_nonempty t)
  have hc := congrArg Finset.card he
  change ((words t).subtype (· ≠ [])).card = (words t).card
  simpa only [Finset.card_map] using hc

instance instFiniteDimensionalVt (t : Threshold) : FiniteDimensional ℝ (Vt t) := by
  unfold Vt
  infer_instance

/-- The weak crossing has exactly the original Bernoulli cylinder masses and
covers every original ray by one nonempty address. Equality is a stopping event. -/
theorem actual_stopping_partition (t : Threshold) :
    (∀ p : Address, M.real (cylinder p) = wordMass (letterMass a b) p) ∧
    (∀ p : Edge, p ∈ A t ↔ mass p.val ≤ t.val ∧ t.val < mass p.val.dropLast) ∧
    (∃ N : ℕ, ∀ p ∈ A t, p.val.length ≤ N) ∧
    IsPrefixFree (Subtype.val '' (A t : Set Edge)) ∧
    (∀ ω : Omega, ∃! p : Edge, p ∈ A t ∧ ω ∈ cylinder p.val) ∧
    (∑ p ∈ A t, M.real (cylinder p.val)) = 1 ∧
    (∀ p ∈ A t, b * t.val < M.real (cylinder p.val) ∧
      M.real (cylinder p.val) ≤ t.val) ∧
    1 / t.val ≤ ((A t).card : ℝ) ∧
      ((A t).card : ℝ) < 1 / (b * t.val) := by
  classical
  have hm (p : Address) : M.real (cylinder p) = wordMass (letterMass a b) p := by
    rw [measureReal_def, cylinder_mass]
    rfl
  have hmem (p : Edge) : p ∈ A t ↔
      mass p.val ≤ t.val ∧ t.val < mass p.val.dropLast := by
    rw [A, Finset.mem_subtype, ← Finset.mem_coe, (words_spec t).1]
    change p.val ≠ [] ∧ wordMass (letterMass a b) p.val ≤ t.val ∧
      t.val < wordMass (letterMass a b) p.val.dropLast ↔ _
    rw [show mass p.val = wordMass (letterMass a b) p.val by rfl,
      show mass p.val.dropLast = wordMass (letterMass a b) p.val.dropLast by rfl]
    simp [p.property]
  have hcover (ω : Omega) : ∃! p : Edge, p ∈ A t ∧ ω ∈ cylinder p.val := by
    obtain ⟨w, ⟨hw, hω⟩, huniq⟩ := (words_spec t).2.2.2.1 ω
    let p : Edge := ⟨w, words_nonempty t w hw⟩
    refine ⟨p, ⟨Finset.mem_subtype.mpr hw, (cylinder_ray w ω).mpr hω⟩, ?_⟩
    rintro q ⟨hq, hqω⟩
    apply Subtype.ext
    exact huniq q.val ⟨Finset.mem_subtype.mp hq, (cylinder_ray q.val ω).mp hqω⟩
  have hsum : (∑ p ∈ A t, M.real (cylinder p.val)) = 1 := by
    simp_rw [hm]
    have he := Finset.subtype_map_of_mem (words_nonempty t)
    have hs := (words_spec t).2.2.2.2.1
    rw [← he, Finset.sum_map] at hs
    exact hs
  refine ⟨hm, hmem, ⟨(frontier_exists t).choose, ?_⟩, ?_, hcover, hsum, ?_, ?_, ?_⟩
  · intro p hp
    exact (words_spec t).2.1 p.val (Finset.mem_subtype.mp hp)
  · rw [addresses]
    exact (words_spec t).2.2.1
  · intro p hp
    rw [hm]
    exact (words_spec t).2.2.2.2.2.1 p.val (Finset.mem_subtype.mp hp)
  · rw [card_A]
    exact (words_spec t).2.2.2.2.2.2.1
  · rw [card_A]
    exact (words_spec t).2.2.2.2.2.2.2

private theorem centered_range (t : Threshold)
    (hp : IsPrefixFree (Subtype.val '' (A t : Set Edge)))
    (hc : ∀ ω : Omega, ∃ p ∈ A t, ω ∈ cylinder p.val) :
    LinearMap.range ((Qt t).toLinearMap.comp G0.subtype) = Vt t ⊓ G0 := by
  have hpart := partition_centered_residual (A t) hp hc
  have hproj := (cylinder_average_projection (A t) hp).2.2.1
  have hPi (F : G) : mean (Pi F) = 0 := by
    rw [centered_suffix_residual.2.2.1, map_sub, centered_suffix_residual.2.1, sub_self]
  have hfix (F : G) (hF : F ∈ G0) : Pi F = F := by
    rw [centered_suffix_residual.2.2.1]
    have hz : mean F = 0 := hF
    rw [hz, map_zero, sub_zero]
  apply Submodule.ext
  intro F
  constructor
  · rintro ⟨f, rfl⟩
    change Qt t f.val ∈ Vt t ∧ mean (Qt t f.val) = 0
    constructor
    · change Q (A t) f.val ∈ V (A t)
      rw [hproj]
      exact Submodule.starProjection_apply_mem _ _
    · have he : Pi (Qt t f.val) = Qt t f.val := by
        change Pi (Q (A t) f.val) = Q (A t) f.val
        rw [← hpart.2.2.2.2.2.1, hfix f.val f.property]
      rw [← he]
      exact hPi _
  · rintro ⟨hV, h0⟩
    refine ⟨⟨F, h0⟩, ?_⟩
    change Q (A t) F = F
    rw [hproj]
    exact Submodule.starProjection_eq_self_iff.mpr hV

/-- All-threshold identities for the constructed actual average, including the
exact all-vector residual and its coefficient-one golden-ratio estimate. -/
theorem actual_stopping_residual (t : Threshold) :
    (∀ (p : Edge) (F : G), atomMean p F =
      (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, F ω ∂M) ∧
    (∀ F : G, Qt t F = (Vt t).starProjection F) ∧
    (∀ p ∈ A t, ∀ F : G, pullback p.val (Qt t F) = constG (atomMean p F)) ∧
    (∀ p ∈ A t, ∀ z : H, pullback p.val (C z-Qt t (C z)) = C (S p.val z)) ∧
    (∀ F : G, ‖F‖ ^ 2 =
      ∑ p ∈ A t, M.real (cylinder p.val) * ‖pullback p.val F‖ ^ 2) ∧
    (∀ z : H, ‖C z-Qt t (C z)‖ ^ 2 =
      ∑ p ∈ A t, M.real (cylinder p.val) * ‖C (S p.val z)‖ ^ 2) ∧
    (∀ z : H, ‖C z-Qt t (C z)‖ ^ 2 ≤ Real.goldenRatio * t.val * ‖z‖ ^ 2) ∧
    (∀ c : ℝ, Qt t (constG c) = constG c) ∧
    (∀ F : G, Qt t (Pi F) = Pi (Qt t F)) ∧
    Module.finrank ℝ (Vt t) = (A t).card ∧
    Module.finrank ℝ (Vt0 t) = (A t).card - 1 ∧
    LinearMap.range ((Qt t).toLinearMap.comp G0.subtype) = Vt t ⊓ G0 := by
  have hstop := actual_stopping_partition t
  have hp := hstop.2.2.2.1
  have hc : ∀ ω : Omega, ∃ p ∈ A t, ω ∈ cylinder p.val := by
    intro ω
    obtain ⟨p, hp, _⟩ := hstop.2.2.2.2.1 ω
    exact ⟨p, hp⟩
  have hpart := partition_centered_residual (A t) hp hc
  refine ⟨(cylinder_average_projection (A t) hp).1,
    (cylinder_average_projection (A t) hp).2.2.1,
    hpart.1, hpart.2.1, hpart.2.2.1, hpart.2.2.2.1, ?_,
    hpart.2.2.2.2.1, hpart.2.2.2.2.2.1,
    hpart.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2, centered_range t hp hc⟩
  intro z
  exact bounded_partition_residual (A t) hp hc t.val t.property.1.le
    (fun p hp => (hstop.2.2.2.2.2.2.1 p hp).2) z

#print axioms actual_stopping_partition
#print axioms actual_stopping_residual

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping
