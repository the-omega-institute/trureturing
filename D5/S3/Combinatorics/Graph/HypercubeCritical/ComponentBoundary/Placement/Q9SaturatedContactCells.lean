/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCells
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: One-coordinate weighted saturation forces signed cancellation in every two-bit contact cell. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Signed contact cells from one-coordinate saturation

For each parity, signed defect singularity supplies a supported crossing-kernel
vector as one weight varies. Normalize these vectors and use the closed projection
from the compact unit sphere to carry annihilation to the unit weights. At that
parameter the crossing kernel is the parity-switch line. Its cancellation and the
three nonconstant Walsh coefficients give cancellation on each two-bit cell.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SaturatedContactCells

noncomputable section

open scoped BigOperators Matrix
open Metric
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching gamma switchingVector)
open Q9IsotropicHuang (parity weightedLinear)
open Q9SignedContactCells (parityPart unit_weight)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open private Vec Cubic Connected Separated Supported OnParity H axisWeight axis_weight
  axis_annihilates unit_line bitSign mask mask_overlap_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
open private regular_parity_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
open private paritySide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

open Classical in
private theorem signed_overlap_parity_zero (C D : Finset (Q 9)) (s r : Vec)
    (hdisj : Disjoint C D) (hsep : Separated C D) (hrC : Cubic C) (hrD : Cubic D)
    (hcD : Connected D) (hs : IsSwitching C s) (hr : IsSwitching D r)
    (b : Bool) (i j : Fin 9)
    (hdet : ∀ t : ℝ, 0 < t →
      (defect (axisWeight j t) (signedBiadjacency (axisWeight j t) D false)).det = 0) :
    parityPart b (switchingVector C s) ⬝ᵥ
      gamma i (gamma j (parityPart b (switchingVector D r))) = 0 := by
  classical
  have hcard : 0 < D.card := by
    obtain ⟨x⟩ := hcD.nonempty
    exact Finset.card_pos.mpr ⟨x.val, x.property⟩
  have hparCard := regular_parity_card D b (d := 3) (by decide) hrD
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (paritySide D b).card by omega)
  let root : Q 9 := x.val
  have hroot : root ∈ D := x.property
  have hrootParity : parity root = b := (Finset.mem_filter.mp hx).2
  have hbD : IsBalanced D := ⟨r, hr⟩

  let L : Vec →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ (parityPart b (switchingVector C s))).comp
    ((gamma i).comp (gamma j))
  let Sphere := ↥(Metric.sphere (0 : Vec) 1)
  letI : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Vec) 1)
  let v (z : ℝ × Sphere) : Vec := z.2.val
  let W (z : ℝ × Sphere) : Vec := weightedLinear (axisWeight j z.1) (v z)
  have hv : Continuous v := continuous_subtype_val.comp continuous_snd
  have hW : Continuous W := by
    have hformula : W = fun z => H (v z) + (z.1 - 1) • gamma j (v z) := by
      funext z
      exact axis_weight j z.1 (v z)
    rw [hformula]
    exact (H.continuous_of_finiteDimensional.comp hv).add
      ((continuous_fst.sub continuous_const).smul
        ((gamma j).continuous_of_finiteDimensional.comp hv))
  have hclosedCoordinates (F : ℝ × Sphere → Vec) (hF : Continuous F) (P : Q 9 → Prop) :
      IsClosed {z : ℝ × Sphere | ∀ x, P x → F z x = 0} := by
    have heq : {z : ℝ × Sphere | ∀ x, P x → F z x = 0} =
        ⋂ x : {x : Q 9 // P x}, {z : ℝ × Sphere | F z x.val = 0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
    rw [heq]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply x.val).comp hF) continuous_const

  let K : Set (ℝ × Sphere) := {z | Supported D (v z) ∧ OnParity b (v z) ∧
    Supported D (W z) ∧ L (v z) = 0}
  have hK : IsClosed K :=
    (hclosedCoordinates v hv (fun x => x ∉ D)).inter
      ((hclosedCoordinates v hv (fun x => parity x ≠ b)).inter
        ((hclosedCoordinates W hW (fun x => x ∉ D)).inter
          (isClosed_eq (L.continuous_of_finiteDimensional.comp hv) continuous_const)))
  have hprojection : IsClosed (Prod.fst '' K) := isClosedMap_fst_of_compactSpace K hK
  have hinterval : Set.Ioo (1 : ℝ) 2 ⊆ Prod.fst '' K := by
    intro t ht
    have htpos : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht.1
    have hw (k : Fin 9) : 0 < axisWeight j t k := by
      by_cases hk : k = j <;> simp [axisWeight, hk, htpos]
    obtain ⟨u, hu, huW⟩ := exists_both_parity_supported_of_signed_defect_singular
      D hrD hcD hbD (axisWeight j t) hw (hdet t htpos) b
    have hu0 : u ≠ 0 := by
      intro h
      exact (hu root).2 ⟨hroot, hrootParity⟩ (by simp [h])
    let g : Sphere := ⟨NormedSpace.normalize u,
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hu0)⟩
    have hgZero (y : Q 9) (hy : ¬ (y ∈ D ∧ parity y = b)) : (g : Vec) y = 0 := by
      have huy : u y = 0 := not_not.mp (fun h => hy ((hu y).mp h))
      simp only [g, NormedSpace.normalize, Pi.smul_apply, huy, smul_zero]
    have hgD : Supported D (g : Vec) := fun y hy => hgZero y (fun h => hy h.1)
    have hgb : OnParity b (g : Vec) := fun y hy => hgZero y (fun h => hy h.2)
    have hgW : Supported D (weightedLinear (axisWeight j t) (g : Vec)) := by
      intro y hy
      change weightedLinear (axisWeight j t) (‖u‖⁻¹ • u) y = 0
      rw [map_smul, Pi.smul_apply, huW y hy, smul_zero]
    have hgL : L (g : Vec) = 0 :=
      axis_annihilates hdisj hsep hrC hs b i j (ne_of_gt ht.1) hgD hgW
    exact ⟨(t, g), ⟨hgD, hgb, hgW, hgL⟩, rfl⟩

  have hunit : (1 : ℝ) ∈ closure (Set.Ioo 1 2) := by
    rw [closure_Ioo (show (1 : ℝ) ≠ 2 by norm_num)]
    exact Set.left_mem_Icc.mpr (by norm_num)
  obtain ⟨⟨t, g⟩, hg, ht⟩ := closure_minimal hinterval hprojection hunit
  change t = 1 at ht
  subst t
  obtain ⟨hgD, hgb, hgW, hgL⟩ : Supported D (g : Vec) ∧ OnParity b (g : Vec) ∧
      Supported D (weightedLinear (axisWeight j 1) (g : Vec)) ∧ L (g : Vec) = 0 := hg
  have hg0 : (g : Vec) ≠ 0 := by
    intro h
    have hn : ‖(g : Vec)‖ = 1 := mem_sphere_zero_iff_norm.mp g.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hweightOne : axisWeight j (1 : ℝ) = fun _ => 1 := by
    funext k
    simp [axisWeight]
  rw [hweightOne, unit_weight] at hgW
  have hline := unit_line hrD hcD hr hgD hgb hgW root hroot hrootParity
  have hscalar : (g : Vec) root * r root ≠ 0 := by
    intro hzero
    apply hg0
    rw [hline, hzero, zero_smul]
  have hmul := (congrArg L hline).symm.trans hgL
  rw [map_smul, smul_eq_mul] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hscalar

open Classical in
/-- Each unit-weight signed two-bit cell cancels on either parity when the
`false`-parity signed defect of `D` is singular for every positive weight on `j`. -/
theorem signed_overlap_cell_zero (C D : Finset (Q 9)) (s r : Vec)
    (hdisj : Disjoint C D) (hsep : Separated C D) (hrC : Cubic C) (hrD : Cubic D)
    (hcD : Connected D) (hs : IsSwitching C s) (hr : IsSwitching D r)
    (b : Bool) (i j : Fin 9) (hij : i ≠ j)
    (hdet : ∀ t : ℝ, 0 < t →
      let w : Fin 9 → ℝ := fun k => if k = j then t else 1
      (defect w (signedBiadjacency w D false)).det = 0)
    (p q : Bool) :
    (∑ x : Q 9, if x i = p ∧ x j = q then
      parityPart b (switchingVector C s) x *
        gamma i (gamma j (parityPart b (switchingVector D r))) x else 0) = 0 := by
  let f := parityPart b (switchingVector C s)
  let g := gamma i (gamma j (parityPart b (switchingVector D r)))
  have h00 : ∑ x, f x * g x = 0 :=
    signed_overlap_parity_zero C D s r hdisj hsep hrC hrD hcD hs hr b i j hdet
  have h10 : ∑ x, (bitSign (x i) * f x) * g x = 0 := by
    simpa [dotProduct, mask, bitSign] using
      mask_overlap_zero hdisj hsep hrC hrD hs hr b hij true false (Or.inl rfl)
  have h01 : ∑ x, (bitSign (x j) * f x) * g x = 0 := by
    simpa [dotProduct, mask, bitSign] using
      mask_overlap_zero hdisj hsep hrC hrD hs hr b hij false true (Or.inr rfl)
  have h11 : ∑ x, (bitSign (x i) * bitSign (x j) * f x) * g x = 0 := by
    simpa [dotProduct, mask] using
      mask_overlap_zero hdisj hsep hrC hrD hs hr b hij true true (Or.inl rfl)
  change (∑ x, if x i = p ∧ x j = q then f x * g x else 0) = 0
  have hindicator (x : Q 9) :
      4 * (if x i = p ∧ x j = q then f x * g x else 0) =
        f x * g x + bitSign p * ((bitSign (x i) * f x) * g x) +
          bitSign q * ((bitSign (x j) * f x) * g x) +
            (bitSign p * bitSign q) * ((bitSign (x i) * bitSign (x j) * f x) * g x) := by
    cases p <;> cases q <;> cases hxi : x i <;> cases hxj : x j <;>
      norm_num [hxi, hxj, bitSign] <;> ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hindicator x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h00, h10, h01, h11,
    mul_zero, add_zero] at hsum
  linarith

#print axioms signed_overlap_cell_zero

end

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SaturatedContactCells
