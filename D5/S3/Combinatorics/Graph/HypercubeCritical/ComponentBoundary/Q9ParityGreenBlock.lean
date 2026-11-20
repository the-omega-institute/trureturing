/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParityGreenBlock
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Parity Green equations for the switched crossing matrices of a balanced cubic support. -/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Matrix.ColumnRowPartitioned
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityGreenDefect
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence

/-! The parity Green equations for the actual Huang operator on a balanced cubic support.
For separated connected cubic supports, the joint Green rank gives an obstruction
in Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityGreenBlock

open Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj gamma gamma_apply IsSwitching
  switchingVector ambient_eigenvector anticommutator directionEdges directionEndpoints
  direction_edge_count)
open BalancedCubeGirth (gamma_anticommute)
local notation "flip" => BalancedCriticalSpectrum.flip
open Q9ParityFoldedBoundary (parity parityPart cubic_parityPart_card)
open Q9ParityGreenDefect (GreenBlock)
open Q9MixedBoundaryCollisions (Separated)
open SupportedEigenSaturation (matrix_eq_zero_of_not_adj)

open private cubeParity_ne_of_adj huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private switching_sq endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private gamma_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
open private gamma_dotProduct from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence

open private huang_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap

attribute [local instance] Classical.propDecidable

/-- The vertices of one global parity in a finite set. -/
abbrev Side (C : Finset (Q 9)) (p : Bool) := ↥(parityPart C p)

/-- The exterior vertices of parity opposite to the row parity. -/
abbrev Outside (U : Finset (Q 9)) (p : Bool) := Side (Finset.univ \ U) (!p)

private theorem side_mem {C : Finset (Q 9)} {p : Bool} (x : Side C p) : x.val ∈ C :=
  (Finset.mem_filter.mp x.property).1

private theorem side_parity {C : Finset (Q 9)} {p : Bool} (x : Side C p) : parity x.val = p :=
  (Finset.mem_filter.mp x.property).2

private theorem parity_flip (x : Q 9) (i : Fin 9) : parity (flip x i) = !parity x :=
  Bool.eq_not_of_ne (Ne.symm (cubeParity_ne_of_adj (flip_adj x i)))

private theorem sum_side (C : Finset (Q 9)) (p : Bool) (g : Q 9 → ℝ) :
    (∑ x : Side C p, g x) = ∑ x ∈ parityPart C p, g x :=
  (Finset.sum_subtype _ (fun _ => Iff.rfl) g).symm

/-- The unsigned bipartite adjacency after switching the selected edges to positive. -/
def adjacency (C : Finset (Q 9)) (p : Bool) : Matrix (Side C p) (Side C (!p)) ℝ :=
  Matrix.of fun x y => if (hypercube 9).Adj x.val y.val then 1 else 0

/-- The Huang crossing matrix with the gauge on selected rows and unit exterior gauge. -/
def crossing (C U : Finset (Q 9)) (σ : Q 9 → ℝ) (p : Bool) :
    Matrix (Side C p) (Outside U p) ℝ :=
  Matrix.of fun x y => σ x * huangMatrix 9 x y

/-- Direction incidence on a selected vertex. -/
def incidence (C : Finset (Q 9)) (p : Bool) (i : Fin 9) (x : Side C p) : ℝ :=
  if flip x i ∈ C then 1 else 0

/-- The corresponding parity row of the Laplace source. -/
def source (C : Finset (Q 9)) (p : Bool) (i : Fin 9) (x : Side C p) : ℝ :=
  3 * incidence C p i x - 1

/-- The switching vector truncated to one parity. -/
def parityVector (C : Finset (Q 9)) (σ : Q 9 → ℝ) (p : Bool) (x : Q 9) : ℝ :=
  if parity x = p then switchingVector C σ x else 0

/-- Exterior part of the signed flip applied to the switching vector on parity p. -/
def exterior (C U : Finset (Q 9)) (σ : Q 9 → ℝ) (p : Bool) (i : Fin 9)
    (y : Outside U p) : ℝ :=
  gamma i (parityVector C σ p) y

private theorem huang_zero_of_parity {x y : Q 9} (h : parity x = parity y) :
    huangMatrix 9 x y = 0 :=
  matrix_eq_zero_of_not_adj (fun ha => cubeParity_ne_of_adj ha h)

private theorem huang_parityVector (C : Finset (Q 9)) (σ : Q 9 → ℝ)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (p : Bool) :
    huangMatrix 9 *ᵥ parityVector C σ p = (3 : ℝ) • parityVector C σ (!p) := by
  funext x
  by_cases hx : parity x = !p
  · have he := congrFun (ambient_eigenvector (d := 3) C σ hr hs) x
    change (huangMatrix 9 *ᵥ switchingVector C σ) x = 3 * switchingVector C σ x at he
    rw [show ((3 : ℝ) • parityVector C σ (!p)) x = 3 * switchingVector C σ x by
      simp [parityVector, hx], ← he]
    simp only [mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : parity y = p
    · simp [parityVector, hy]
    · have hxy : parity x = parity y := hx.trans (Bool.eq_not_of_ne hy).symm
      rw [huang_zero_of_parity hxy]
      simp
  · have hp : parity x = p := by simpa only [Bool.not_not] using Bool.eq_not_of_ne hx
    change ∑ y, huangMatrix 9 x y * parityVector C σ p y = _
    simp only [Pi.smul_apply, parityVector, ite_eq_right hx, smul_zero]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : parity y = p
    · rw [huang_zero_of_parity (hp.trans hy.symm), zero_mul]
    · simp [hy]

private theorem gamma_parityVector_eq_zero (C : Finset (Q 9)) (σ : Q 9 → ℝ)
    {p : Bool} {x : Q 9} (h : parity x ≠ !p) (i : Fin 9) :
    gamma i (parityVector C σ p) x = 0 := by
  have hp : parity x = p := by simpa only [Bool.not_not] using Bool.eq_not_of_ne h
  rw [gamma_apply]
  simp [parityVector, parity_flip, hp]

private theorem switched_entry {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hs : IsSwitching C σ) {x y : Q 9} (hx : x ∈ C) (hy : y ∈ C) :
    σ x * huangMatrix 9 x y * σ y = if (hypercube 9).Adj x y then 1 else 0 := by
  split_ifs with ha
  · rw [hs.2 x hx y hy ha]
    calc
      σ x * (σ x * σ y) * σ y = σ x ^ 2 * σ y ^ 2 := by ring
      _ = 1 := by rw [switching_sq hs hx, switching_sq hs hy, one_mul]
  · rw [matrix_eq_zero_of_not_adj ha, mul_zero, zero_mul]

private theorem internal_gamma {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hs : IsSwitching C σ) (p : Bool) (i : Fin 9) (y : Side C p) :
    gamma i (parityVector C σ (!p)) y = σ y * incidence C p i y := by
  have hflip : parity (flip y.val i) = !p := by rw [parity_flip, side_parity y]
  rw [gamma_apply]
  by_cases hy : flip y.val i ∈ C
  · simp only [parityVector, hflip, ite_eq_left, switchingVector, hy, incidence, mul_one]
    rw [hs.2 _ (side_mem y) _ hy (flip_adj y.val i), mul_assoc, ← pow_two, switching_sq hs hy,
      mul_one]
  · simp [parityVector, switchingVector, incidence, hy]

private theorem sum_side_add_outside {C U : Finset (Q 9)} (hCU : C ⊆ U) (p : Bool)
    (g : Q 9 → ℝ) (hParity : ∀ y, parity y ≠ !p → g y = 0)
    (hGap : ∀ y ∈ U, y ∉ C → g y = 0) :
    (∑ y : Side C (!p), g y) + (∑ y : Outside U p, g y) = ∑ y, g y := by
  rw [sum_side, sum_side, ← Finset.sum_union]
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_cases hp : parity y = !p
    · have hmiss : y ∉ C ∧ y ∈ U := by
        simpa [parityPart, hp] using hy
      exact hGap y hmiss.2 hmiss.1
    · exact hParity y hp
  · apply Finset.disjoint_left.mpr
    intro y hyC hyU
    have hc := (Finset.mem_filter.mp hyC).1
    have hu := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyU).1).2
    exact hu (hCU hc)

private theorem cross_anticommutator {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (p : Bool) (i : Fin 9) (x : Q 9) :
    (huangMatrix 9 *ᵥ gamma i (parityVector C σ p)) x =
      2 * parityVector C σ p x - 3 * gamma i (parityVector C σ (!p)) x := by
  have h := congrFun (anticommutator i (parityVector C σ p)) x
  rw [huang_parityVector C σ hr hs, map_smul] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  linarith

/-- The crossing image of a parity-restricted direction satisfies the two source rows of the
Green equation. The omitted vertices of U can be any vertices separated from C. -/
theorem crossing_exterior {C U : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (hCU : C ⊆ U)
    (hsep : ∀ x ∈ C, ∀ y ∈ U, y ∉ C → ¬ (hypercube 9).Adj x y)
    (p : Bool) (i : Fin 9) :
    crossing C U σ p *ᵥ exterior C U σ p i =
      (-1 / 3 : ℝ) • ((3 : ℝ) • source C p i + adjacency C p *ᵥ source C (!p) i) := by
  classical
  have hrow (x : Side C p) : ∑ y : Side C (!p), adjacency C p x y = 3 := by
    have h := congrArg (σ x.val * ·) (congrFun (huang_parityVector C σ hr hs (!p)) x.val)
    simp only [Bool.not_not, Pi.smul_apply, smul_eq_mul] at h
    rw [show parityVector C σ p x.val = σ x.val by
      simp [parityVector, side_parity x, switchingVector, side_mem x],
      show σ x.val * (3 * σ x.val) = 3 by
        rw [mul_comm (3 : ℝ), ← mul_assoc, ← pow_two, switching_sq hs (side_mem x), one_mul]]
      at h
    rw [mulVec, dotProduct, Finset.mul_sum] at h
    calc
      _ = ∑ y : Side C (!p), σ x.val *
          (huangMatrix 9 x.val y.val * parityVector C σ (!p) y.val) := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [parityVector, side_parity y, ite_eq_left, switchingVector, side_mem y, adjacency,
          Matrix.of_apply]
        rw [← mul_assoc, switched_entry hs (side_mem x) (side_mem y)]
      _ = 3 := by
        rw [sum_side C (!p) (fun y => σ x.val *
          (huangMatrix 9 x.val y * parityVector C σ (!p) y)), ← h]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro y _ hy
        by_cases hyC : y ∈ C <;> by_cases hyP : parity y = !p
        · exact (hy (Finset.mem_filter.mpr ⟨hyC, hyP⟩)).elim
        all_goals simp [parityVector, switchingVector, hyC, hyP]
  funext x
  let g (y : Q 9) := σ x.val *
    (huangMatrix 9 x.val y * gamma i (parityVector C σ p) y)
  have hsplit := sum_side_add_outside hCU p g
    (fun y hy => by simp [g, gamma_parityVector_eq_zero C σ hy i])
    (fun y hy hyn => by simp [g, matrix_eq_zero_of_not_adj (hsep x (side_mem x) y hy hyn)])
  have hin : (∑ y : Side C (!p), g y) = (adjacency C p *ᵥ incidence C (!p) i) x := by
    apply Finset.sum_congr rfl
    intro y _
    have hg : gamma i (parityVector C σ p) y.val = σ y.val * incidence C (!p) i y := by
      simpa using internal_gamma hs (!p) i y
    simp only [g, hg, adjacency, Matrix.of_apply]
    rw [← switched_entry hs (side_mem x) (side_mem y)]
    ring
  have hout : (∑ y : Outside U p, g y) = (crossing C U σ p *ᵥ exterior C U σ p i) x := by
    simp only [g, crossing, exterior, mulVec, dotProduct, Matrix.of_apply, mul_assoc]
  rw [hin, hout, show (∑ y, g y) =
      σ x.val * (huangMatrix 9 *ᵥ gamma i (parityVector C σ p)) x.val by
      simp only [g, mulVec, dotProduct, Finset.mul_sum], cross_anticommutator hr hs] at hsplit
  have hxg : gamma i (parityVector C σ (!p)) x.val = σ x.val * incidence C p i x :=
    internal_gamma hs p i x
  rw [hxg, show parityVector C σ p x.val = σ x.val by
    simp [parityVector, side_parity x, switchingVector, side_mem x]] at hsplit
  have hsquare := switching_sq hs (side_mem x)
  have hscaled : σ x.val * (2 * σ x.val - 3 * (σ x.val * incidence C p i x)) =
      2 - 3 * incidence C p i x := by
    calc
      _ = σ x.val ^ 2 * (2 - 3 * incidence C p i x) := by ring
      _ = _ := by rw [hsquare, one_mul]
  rw [hscaled] at hsplit
  have hsource : source C (!p) i = (3 : ℝ) • incidence C (!p) i - fun _ => 1 := rfl
  rw [hsource, mulVec_sub, mulVec_smul]
  have hone : (adjacency C p *ᵥ (fun _ => 1)) x = 3 := by
    simpa only [mulVec, dotProduct, mul_one] using hrow x
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hone]
  unfold source
  linarith

private theorem huang_row_gram (x z : Q 9) :
    (∑ y, huangMatrix 9 x y * huangMatrix 9 z y) = if x = z then 9 else 0 := by
  classical
  have h := congrFun (huang_square (Pi.single z 1)) x
  rw [mulVec_mulVec, mulVec_single_one] at h
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
  rw [mul_ite, mul_one, mul_zero] at h
  change (huangMatrix 9 * huangMatrix 9) x z = _ at h
  rw [← h, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun y _ => by rw [huangMatrix_symmetric z y]

/-- The crossing row Gram is the complementary square of the switched adjacency. -/
theorem crossing_mul_transpose {C U : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hs : IsSwitching C σ) (hCU : C ⊆ U)
    (hsep : ∀ x ∈ C, ∀ y ∈ U, y ∉ C → ¬ (hypercube 9).Adj x y) (p : Bool) :
    crossing C U σ p * (crossing C U σ p)ᵀ =
      (9 : ℝ) • 1 - adjacency C p * (adjacency C p)ᵀ := by
  classical
  ext x z
  let g (y : Q 9) := (σ x.val * huangMatrix 9 x.val y) * (σ z.val * huangMatrix 9 z.val y)
  have hsplit := sum_side_add_outside hCU p g
    (fun y hy => by
      have hy' : parity y = p := by simpa only [Bool.not_not] using Bool.eq_not_of_ne hy
      simp [g, huang_zero_of_parity ((side_parity x).trans hy'.symm)])
    (fun y hy hyn => by
      simp [g, matrix_eq_zero_of_not_adj (hsep x (side_mem x) y hy hyn)])
  have hin : (∑ y : Side C (!p), g y) = (adjacency C p * (adjacency C p)ᵀ) x z := by
    apply Finset.sum_congr rfl
    intro y _
    change g y.val = (adjacency C p x y) * (adjacency C p z y)
    change g y.val = (if (hypercube 9).Adj x.val y.val then 1 else 0) *
      (if (hypercube 9).Adj z.val y.val then 1 else 0)
    rw [← switched_entry hs (side_mem x) (side_mem y),
      ← switched_entry hs (side_mem z) (side_mem y)]
    calc
      _ = σ y.val ^ 2 * g y.val := by rw [switching_sq hs (side_mem y), one_mul]
      _ = _ := by unfold g; ring
  have hAmbient : (∑ y, g y) = ((9 : ℝ) • (1 : Matrix (Side C p) (Side C p) ℝ)) x z := by
    simp only [g, show ∀ y : Q 9,
      σ x.val * huangMatrix 9 x.val y * (σ z.val * huangMatrix 9 z.val y) =
        (σ x.val * σ z.val) * (huangMatrix 9 x.val y * huangMatrix 9 z.val y)
      from fun _ => by ring, ← Finset.mul_sum, huang_row_gram, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    by_cases h : x = z
    · subst z
      rw [ite_eq_left rfl, ite_eq_left rfl, ← pow_two, switching_sq hs (side_mem x),
        one_mul, mul_one]
    · rw [ite_eq_right (fun he => h (Subtype.ext he)), ite_eq_right h, mul_zero, mul_zero]
  change (∑ y : Outside U p, g y) = _
  rw [Matrix.sub_apply]
  rw [hin, hAmbient] at hsplit
  linarith

private theorem endpoints_on_parity (C : Finset (Q 9)) (i : Fin 9) (p : Bool) :
    (parityPart (directionEndpoints C i) p).card = directionEdges C i := by
  classical
  have he : (parityPart (directionEndpoints C i) p).card =
      (parityPart (directionEndpoints C i) (!p)).card := by
    apply Finset.card_bij (fun x _ => flip x i)
    · intro x hx
      have hx' : (x ∈ C ∧ flip x i ∈ C) ∧ parity x = p := by
        simpa only [parityPart, directionEndpoints, Finset.mem_filter] using hx
      simp [parityPart, directionEndpoints, hx'.1.1, hx'.1.2, parity_flip, hx'.2]
    · intro x _ y _ hxy
      simpa only [BalancedCriticalSpectrum.flip_flip] using
        congrArg (fun z : Q 9 => flip z i) hxy
    · intro y hy
      have hy' : (y ∈ C ∧ flip y i ∈ C) ∧ parity y = !p := by
        simpa only [parityPart, directionEndpoints, Finset.mem_filter] using hy
      refine ⟨flip y i, ?_, BalancedCriticalSpectrum.flip_flip y i⟩
      simp [parityPart, directionEndpoints, hy'.1.1, hy'.1.2, parity_flip, hy'.2]
  have ht := Finset.card_filter_add_card_filter_not (s := directionEndpoints C i)
    (fun x => parity x = p)
  have hnot (x : Q 9) : (¬ parity x = p) ↔ parity x = !p := by
    cases p <;> cases parity x <;> simp
  simp only [hnot] at ht
  change (parityPart (directionEndpoints C i) p).card +
    (parityPart (directionEndpoints C i) (!p)).card = (directionEndpoints C i).card at ht
  rw [← he, endpoint_card_twice] at ht
  omega

private theorem incidence_sum (C : Finset (Q 9)) (i : Fin 9) (p : Bool) :
    ∑ x : Side C p, incidence C p i x = (directionEdges C i : ℝ) := by
  classical
  change (∑ x : Side C p, (if flip x.val i ∈ C then (1 : ℝ) else 0)) = _
  rw [sum_side C p (fun x => if flip x i ∈ C then (1 : ℝ) else 0), ← Finset.sum_filter]
  have he : (parityPart C p).filter (fun x => flip x i ∈ C) =
      parityPart (directionEndpoints C i) p := by
    ext x
    simp only [parityPart, directionEndpoints, Finset.mem_filter]
    tauto
  simp [he, endpoints_on_parity]

private theorem parityVector_norm {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hs : IsSwitching C σ) (p : Bool) :
    parityVector C σ p ⬝ᵥ parityVector C σ p = ((parityPart C p).card : ℝ) := by
  have hterm (x : Q 9) :
      parityVector C σ p x * parityVector C σ p x =
        if x ∈ parityPart C p then 1 else 0 := by
    by_cases hx : x ∈ C <;> by_cases hp : parity x = p
    · simpa [parityVector, switchingVector, parityPart, hx, hp, pow_two] using switching_sq hs hx
    all_goals simp [parityVector, switchingVector, parityPart, hx, hp]
  simp only [dotProduct, hterm]
  simp

private theorem gamma_gram {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hs : IsSwitching C σ) (p : Bool) (i j : Fin 9) :
    gamma i (parityVector C σ p) ⬝ᵥ gamma j (parityVector C σ p) =
      if i = j then ((parityPart C p).card : ℝ) else 0 := by
  by_cases he : i = j
  · subst j
    rw [ite_eq_left rfl, gamma_dotProduct, gamma_square, parityVector_norm hs]
  · rw [ite_eq_right he]
    let f := parityVector C σ p
    have h : gamma i f ⬝ᵥ gamma j f = -(gamma i f ⬝ᵥ gamma j f) := by
      calc
        _ = f ⬝ᵥ gamma i (gamma j f) := (gamma_dotProduct i f _).symm
        _ = -(f ⬝ᵥ gamma j (gamma i f)) := by rw [gamma_anticommute he, dotProduct_neg]
        _ = _ := by rw [gamma_dotProduct j, dotProduct_comm (gamma j f)]
    linarith

/-- The exterior Gram on either parity, corrected by the internal Laplace source. -/
theorem exterior_gram {C U : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (hCU : C ⊆ U)
    (hsep : ∀ x ∈ C, ∀ y ∈ U, y ∉ C → ¬ (hypercube 9).Adj x y)
    (p : Bool) (i j : Fin 9) :
    exterior C U σ p i ⬝ᵥ exterior C U σ p j +
      (source C (!p) i ⬝ᵥ source C (!p) j) / 9 =
        (C.card : ℝ) * ((if i = j then (1 : ℝ) else 0) - 1 / 9) / 2 := by
  classical
  let g (y : Q 9) := gamma i (parityVector C σ p) y * gamma j (parityVector C σ p) y
  have hsplit := sum_side_add_outside hCU p g
    (fun y hy => by simp [g, gamma_parityVector_eq_zero C σ hy i])
    (fun y hy hyn => by
      have hf : flip y i ∉ C := fun hf => hsep _ hf y hy hyn (flip_adj y i).symm
      simp [g, gamma_apply, parityVector, switchingVector, hf])
  have hin : (∑ y : Side C (!p), g y) = incidence C (!p) i ⬝ᵥ incidence C (!p) j := by
    apply Finset.sum_congr rfl
    intro y _
    have h (k : Fin 9) :
        gamma k (parityVector C σ p) y.val = σ y.val * incidence C (!p) k y := by
      simpa using internal_gamma hs (!p) k y
    dsimp only [g]
    rw [h i, h j]
    calc
      _ = σ y.val ^ 2 * (incidence C (!p) i y * incidence C (!p) j y) := by ring
      _ = _ := by rw [switching_sq hs (side_mem y), one_mul]
  change (∑ y : Side C (!p), g y) + (exterior C U σ p i ⬝ᵥ exterior C U σ p j) =
    (gamma i (parityVector C σ p) ⬝ᵥ gamma j (parityVector C σ p)) at hsplit
  rw [hin, gamma_gram hs] at hsplit
  have hdir (k : Fin 9) : 6 * directionEdges C k = C.card :=
    direction_edge_count (d := 3) C hr ⟨σ, hs⟩ k
  have hcard (q : Bool) : (parityPart C q).card = 3 * directionEdges C i :=
    cubic_parityPart_card (hdir i).symm hr q
  have hsize (q : Bool) : ((parityPart C q).card : ℝ) = (C.card : ℝ) / 2 := by
    rw [hcard]
    push_cast
    have h := congrArg (Nat.cast : ℕ → ℝ) (hdir i)
    push_cast at h
    linarith
  have hsum (k : Fin 9) : (∑ x : Side C (!p), incidence C (!p) k x) = (C.card : ℝ) / 6 := by
    rw [incidence_sum]
    have h := congrArg (Nat.cast : ℕ → ℝ) (hdir k)
    push_cast at h
    linarith
  have hinner : source C (!p) i ⬝ᵥ source C (!p) j =
      9 * (incidence C (!p) i ⬝ᵥ incidence C (!p) j) - (C.card : ℝ) / 2 := by
    calc
      _ = ∑ x : Side C (!p),
          (9 * (incidence C (!p) i x * incidence C (!p) j x) -
            3 * incidence C (!p) i x - 3 * incidence C (!p) j x + 1) := by
        apply Finset.sum_congr rfl
        intro x _
        unfold source
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe, mul_one,
          hsum, hsize, dotProduct]
        ring
  rw [hinner, hsize] at *
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] at hsplit ⊢ <;> linarith

/-- A Laplace solution on the support supplies a Green block on either exterior parity.
The ambient set U may also contain components separated from C. -/
def greenBlock {C U : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (hCU : C ⊆ U)
    (hsep : ∀ x ∈ C, ∀ y ∈ U, y ∉ C → ¬ (hypercube 9).Adj x y) (p : Bool)
    (hₑ : Fin 9 → Side C p → ℝ) (hₒ : Fin 9 → Side C (!p) → ℝ)
    (he : ∀ i, (3 : ℝ) • hₑ i - adjacency C p *ᵥ hₒ i = source C p i)
    (ho : ∀ i, (3 : ℝ) • hₒ i - (adjacency C p)ᵀ *ᵥ hₑ i = source C (!p) i) :
    GreenBlock (Side C p) (Side C (!p)) (Outside U p) (Fin 9) where
  adjacency := adjacency C p
  crossing := crossing C U σ p
  size := C.card
  evenPotential := hₑ
  oddPotential := hₒ
  evenSource := source C p
  oddSource := source C (!p)
  exterior := exterior C U σ p
  even_laplace := he
  odd_laplace := ho
  crossing_mul_transpose := crossing_mul_transpose hs hCU hsep p
  crossing_exterior := crossing_exterior hr hs hCU hsep p
  exterior_gram := exterior_gram hr hs hCU hsep p

private theorem sum_outside (U : Finset (Q 9)) (p : Bool) (g : Q 9 → ℝ)
    (hParity : ∀ y, parity y ≠ !p → g y = 0) (hU : ∀ y ∈ U, g y = 0) :
    (∑ y : Outside U p, g y) = ∑ y, g y := by
  have h := sum_side_add_outside (Finset.empty_subset U) p g hParity (fun y hy _ => hU y hy)
  simpa only [sum_side ∅ (!p) g, parityPart, Finset.filter_empty, Finset.sum_empty,
    zero_add] using h

/-- A separated support's exterior direction has zero image across the other support. -/
theorem crossing_exterior_of_separated {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hsep : Separated C D)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hτ : IsSwitching D τ) (p : Bool) (i : Fin 9) :
    crossing C (C ∪ D) σ p *ᵥ exterior D (C ∪ D) τ p i = 0 := by
  funext x
  let g (y : Q 9) := huangMatrix 9 x.val y * gamma i (parityVector D τ p) y
  have hsum := sum_outside (C ∪ D) p g
    (fun y hy => by simp [g, gamma_parityVector_eq_zero D τ hy i])
    (fun y hy => by
      rcases Finset.mem_union.mp hy with hyC | hyD
      · have hf : flip y i ∉ D := fun hf => hsep.2 y hyC _ hf (flip_adj y i)
        simp [g, gamma_apply, parityVector, switchingVector, hf]
      · simp [g, matrix_eq_zero_of_not_adj (hsep.2 x (side_mem x) y hyD)])
  have hxD : x.val ∉ D := fun hxD => Finset.disjoint_left.mp hsep.1 (side_mem x) hxD
  have hf : flip x.val i ∉ D := fun hf => hsep.2 x (side_mem x) _ hf (flip_adj x.val i)
  have hzero : (huangMatrix 9 *ᵥ gamma i (parityVector D τ p)) x.val = 0 := by
    rw [cross_anticommutator hr hτ]
    simp [parityVector, switchingVector, gamma_apply, hxD, hf]
  change (∑ y : Outside (C ∪ D) p, g y) =
    (huangMatrix 9 *ᵥ gamma i (parityVector D τ p)) x.val at hsum
  change (∑ y : Outside (C ∪ D) p, σ x.val * (huangMatrix 9 x.val y.val) *
    gamma i (parityVector D τ p) y.val) = 0
  simp only [mul_assoc, ← Finset.mul_sum]
  change σ x.val * (∑ y : Outside (C ∪ D) p, g y) = 0
  rw [hsum, hzero, mul_zero]

/-- On the common exterior, the crossing row spaces of separated supports are orthogonal. -/
theorem crossing_mul_transpose_of_separated {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hsep : Separated C D) (p : Bool) :
    crossing C (C ∪ D) σ p * (crossing D (C ∪ D) τ p)ᵀ = 0 := by
  ext x z
  let g (y : Q 9) := huangMatrix 9 x.val y * huangMatrix 9 z.val y
  have hsum := sum_outside (C ∪ D) p g
    (fun y hy => by
      have hp : parity y = p := by simpa only [Bool.not_not] using Bool.eq_not_of_ne hy
      simp [g, huang_zero_of_parity ((side_parity x).trans hp.symm)])
    (fun y hy => by
      rcases Finset.mem_union.mp hy with hyC | hyD
      · have hzy := matrix_eq_zero_of_not_adj
          (fun h => hsep.2 y hyC z (side_mem z) h.symm)
        simp [g, hzy]
      · simp [g, matrix_eq_zero_of_not_adj (hsep.2 x (side_mem x) y hyD)])
  have hne : x.val ≠ z.val := fun h =>
    Finset.disjoint_left.mp hsep.1 (side_mem x) (h ▸ side_mem z)
  have hzero : (∑ y, g y) = 0 := by
    simp only [g, huang_row_gram, ite_eq_right hne]
  rw [hzero] at hsum
  change (∑ y : Outside (C ∪ D) p,
    (σ x.val * huangMatrix 9 x.val y) * (τ z.val * huangMatrix 9 z.val y)) = 0
  have hterm (y : Outside (C ∪ D) p) :
      (σ x.val * huangMatrix 9 x.val y.val) * (τ z.val * huangMatrix 9 z.val y.val) =
        (σ x.val * τ z.val) * g y.val := by
    dsimp only [g]
    ring
  simp only [hterm, ← Finset.mul_sum, hsum, mul_zero]

private def sideEquiv (C : Finset (Q 9)) (p : Bool) :
    Side C p ⊕ Side C (!p) ≃ (C : Set (Q 9)) where
  toFun := Sum.elim (fun x => ⟨x.val, side_mem x⟩) (fun x => ⟨x.val, side_mem x⟩)
  invFun x := if hx : parity x.val = p then
    Sum.inl ⟨x.val, Finset.mem_filter.mpr ⟨x.property, hx⟩⟩
  else
    Sum.inr ⟨x.val, Finset.mem_filter.mpr ⟨x.property, Bool.eq_not_of_ne hx⟩⟩
  left_inv x := by
    cases x with
    | inl x => simp [side_parity x]
    | inr x =>
      have h : parity x.val ≠ p := by rw [side_parity x]; cases p <;> decide
      simp [h]
  right_inv x := by
    dsimp
    split <;> rfl

private theorem laplace_block {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (p : Bool) :
    let L := ((hypercube 9).induce (C : Set (Q 9))).lapMatrix ℝ
    let A := adjacency C p
    let e := sideEquiv C p
    L.submatrix e e = fromBlocks ((3 : ℝ) • 1) (-A) (-Aᵀ) ((3 : ℝ) • 1) := by
  intro L A e
  have hsame (q : Bool) (x y : Side C q) : ¬ (hypercube 9).Adj x.val y.val :=
    fun h => cubeParity_ne_of_adj h ((side_parity x).trans (side_parity y).symm)
  have heL (x : Side C p) : (e (Sum.inl x)).val = x.val := rfl
  have heR (x : Side C (!p)) : (e (Sum.inr x)).val = x.val := rfl
  have hentry (x y : ↥(C : Set (Q 9))) :
      L x y = (if x = y then (3 : ℝ) else 0) -
        (if (hypercube 9).Adj x.val y.val then 1 else 0) := by
    simp only [L, SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
      Matrix.diagonal_apply, hr.degree_eq, Nat.cast_ofNat, SimpleGraph.adjMatrix,
      Matrix.of_apply, SimpleGraph.induce_adj]
  ext (x | x) (y | y)
  · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, hentry, heL, hsame, ite_false, sub_zero,
      e.injective.eq_iff, Sum.inl.injEq, mul_ite, mul_one, mul_zero]
  · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
      hentry, heL, heR, e.injective.eq_iff, Sum.inl_ne_inr, ite_false, zero_sub,
      A, adjacency, Matrix.of_apply]
  · have hadj : (hypercube 9).Adj x.val y.val ↔ (hypercube 9).Adj y.val x.val :=
      ⟨fun h => h.symm, fun h => h.symm⟩
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply,
      Matrix.transpose_apply, hentry, heL, heR, e.injective.eq_iff, Sum.inr_ne_inl,
      ite_false, zero_sub, A, adjacency, Matrix.of_apply, hadj]
  · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, hentry, heR, hsame, ite_false, sub_zero,
      e.injective.eq_iff, Sum.inr.injEq, mul_ite, mul_one, mul_zero]

private theorem laplace_rows {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (p : Bool)
    (v : ↥(C : Set (Q 9)) → ℝ) :
    ((hypercube 9).induce (C : Set (Q 9))).lapMatrix ℝ *ᵥ v = 0 ↔
      adjacency C p *ᵥ (v ∘ sideEquiv C p ∘ Sum.inr) =
        (3 : ℝ) • (v ∘ sideEquiv C p ∘ Sum.inl) ∧
      (adjacency C p)ᵀ *ᵥ (v ∘ sideEquiv C p ∘ Sum.inl) =
        (3 : ℝ) • (v ∘ sideEquiv C p ∘ Sum.inr) := by
  let A := adjacency C p
  let e := sideEquiv C p
  let a := v ∘ e ∘ Sum.inl
  let b := v ∘ e ∘ Sum.inr
  let L := ((hypercube 9).induce (C : Set (Q 9))).lapMatrix ℝ
  have h := submatrix_mulVec_equiv L (v ∘ e) e e
  rw [show (v ∘ e) ∘ e.symm = v by funext x; simp, laplace_block hr p,
    fromBlocks_mulVec, smul_mulVec, smul_mulVec, one_mulVec, one_mulVec,
    neg_mulVec, neg_mulVec] at h
  change (Sum.elim ((3 : ℝ) • a + -(A *ᵥ b)) (-(Aᵀ *ᵥ a) + (3 : ℝ) • b)) =
    (L *ᵥ v) ∘ e at h
  change L *ᵥ v = 0 ↔ A *ᵥ b = (3 : ℝ) • a ∧ Aᵀ *ᵥ a = (3 : ℝ) • b
  constructor
  · intro hz
    rw [hz] at h
    refine ⟨?_, ?_⟩
    · have he : (3 : ℝ) • a + -(A *ᵥ b) = 0 := by
        funext x
        exact congrFun h (Sum.inl x)
      exact (sub_eq_zero.mp he).symm
    · have ho : -(Aᵀ *ᵥ a) + (3 : ℝ) • b = 0 := by
        funext x
        exact congrFun h (Sum.inr x)
      rw [add_comm] at ho
      exact (sub_eq_zero.mp ho).symm
  · rintro ⟨he, ho⟩
    rw [he, ho, add_neg_cancel, neg_add_cancel] at h
    funext x
    have hx := congrFun h (e.symm x)
    change Sum.elim (0 : Side C p → ℝ) (0 : Side C (!p) → ℝ) (e.symm x) =
      (L *ᵥ v) (e (e.symm x)) at hx
    rw [Equiv.apply_symm_apply] at hx
    cases hs : e.symm x <;>
      simpa only [hs, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] using hx.symm

private theorem finrank_ker_parity_square {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected) (p : Bool) :
    let A := adjacency C p
    let S := (9 : ℝ) • 1 - A * Aᵀ
    Module.finrank ℝ (LinearMap.ker S.mulVecLin) = 1 := by
  intro A S
  let G := (hypercube 9).induce (C : Set (Q 9))
  let e := sideEquiv C p
  let extend (a : Side C p → ℝ) : ↥(C : Set (Q 9)) → ℝ :=
    Sum.elim a ((1 / 3 : ℝ) • (Aᵀ *ᵥ a)) ∘ e.symm
  have he (a : Side C p → ℝ) : extend a ∘ e ∘ Sum.inl = a := by
    funext x
    simp [extend]
  have ho (a : Side C p → ℝ) :
      extend a ∘ e ∘ Sum.inr = (1 / 3 : ℝ) • (Aᵀ *ᵥ a) := by
    funext x
    simp [extend]
  have hmem (a : Side C p → ℝ) :
      a ∈ LinearMap.ker S.mulVecLin ↔ G.lapMatrix ℝ *ᵥ extend a = 0 := by
    rw [laplace_rows hr p]
    change a ∈ LinearMap.ker S.mulVecLin ↔
      A *ᵥ (extend a ∘ e ∘ Sum.inr) = (3 : ℝ) • (extend a ∘ e ∘ Sum.inl) ∧
      Aᵀ *ᵥ (extend a ∘ e ∘ Sum.inl) = (3 : ℝ) • (extend a ∘ e ∘ Sum.inr)
    rw [he, ho, mulVec_smul, mulVec_mulVec, smul_smul]
    norm_num
    rw [show S = (9 : ℝ) • 1 - A * Aᵀ from rfl, sub_mulVec, smul_mulVec, one_mulVec,
      sub_eq_zero]
    constructor <;> intro h <;> funext x <;> have hx := congrFun h x <;>
      simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢ <;> linarith
  let f : LinearMap.ker S.mulVecLin →ₗ[ℝ] LinearMap.ker (G.lapMatrix ℝ).toLin' := by
    refine { toFun := fun a => ⟨extend a.val, (hmem a.val).mp a.property⟩
             map_add' := ?_, map_smul' := ?_ }
    · intro a b
      apply Subtype.ext
      funext x
      change extend (a.val + b.val) x = (extend a.val + extend b.val) x
      cases hx : e.symm x <;> simp [extend, hx, mulVec_add, smul_add]
    · intro c a
      apply Subtype.ext
      funext x
      change extend (c • a.val) x = (c • extend a.val) x
      cases hx : e.symm x <;> simp [extend, hx, mulVec_smul, mul_left_comm]
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have hval : extend a.val = extend b.val := congrArg Subtype.val hab
      simpa only [he] using congrArg (fun v => v ∘ e ∘ Sum.inl) hval
    · intro v
      let a := v.val ∘ e ∘ Sum.inl
      let b := v.val ∘ e ∘ Sum.inr
      have hv := (laplace_rows hr p v.val).mp v.property
      have hb : (1 / 3 : ℝ) • (Aᵀ *ᵥ a) = b := by
        have hv' : Aᵀ *ᵥ a = (3 : ℝ) • b := hv.2
        rw [hv', smul_smul]
        norm_num
      have hext : extend a = v.val := by
        funext x
        have hx := congrFun (show Sum.elim a b = v.val ∘ e by
          funext y; cases y <;> rfl) (e.symm x)
        change Sum.elim a ((1 / 3 : ℝ) • (Aᵀ *ᵥ a)) (e.symm x) = v.val x
        rw [hb]
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx
      have ha : a ∈ LinearMap.ker S.mulVecLin := (hmem a).mpr (hext.symm ▸ v.property)
      exact ⟨⟨a, ha⟩, Subtype.ext hext⟩
  have : Nonempty (C : Set (Q 9)) := hc.nonempty
  have : Subsingleton G.ConnectedComponent := hc.preconnected.subsingleton_connectedComponent
  have : Unique G.ConnectedComponent := uniqueOfSubsingleton (Classical.choice inferInstance)
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hf),
    ← G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix, Fintype.card_unique]

/-- Each connected balanced cubic support loses exactly one crossing row on either parity. -/
theorem crossing_rank_add_one {C U : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hs : IsSwitching C σ) (hCU : C ⊆ U)
    (hsep : ∀ x ∈ C, ∀ y ∈ U, y ∉ C → ¬ (hypercube 9).Adj x y) (p : Bool) :
    (crossing C U σ p).rank + 1 = (parityPart C p).card := by
  let A := adjacency C p
  let S := (9 : ℝ) • 1 - A * Aᵀ
  have hnull : Module.finrank ℝ (LinearMap.ker S.mulVecLin) = 1 :=
    finrank_ker_parity_square hr hc p
  have hrank := S.mulVecLin.finrank_range_add_finrank_ker
  change ((9 : ℝ) • 1 - A * Aᵀ).rank + _ = _ at hrank
  rw [hnull] at hrank
  change ((9 : ℝ) • 1 - adjacency C p * (adjacency C p)ᵀ).rank + 1 = _ at hrank
  rw [← crossing_mul_transpose hs hCU hsep p, rank_self_mul_transpose] at hrank
  simpa using hrank

private theorem common_crossing_nullity_aux {e f n : Type*} [Finite e] [Finite f] [Fintype n]
    (X : Matrix e n ℝ) (Y : Matrix f n ℝ) (h : X * Yᵀ = 0) :
    Module.finrank ℝ (X.mulVecLin.ker ⊓ Y.mulVecLin.ker : Submodule ℝ (n → ℝ)) +
      X.rank + Y.rank = Fintype.card n := by
  let _ := Fintype.ofFinite e
  let _ := Fintype.ofFinite f
  let Z := fromRows X Y
  have hYX : Y * Xᵀ = 0 := by simpa using congrArg Matrix.transpose h
  have hGram : Z * Zᵀ = fromBlocks (X * Xᵀ) 0 0 (Y * Yᵀ) := by
    rw [show Z = fromRows X Y from rfl, transpose_fromRows, fromRows_mul_fromCols, h, hYX]
  let E := LinearEquiv.sumArrowLequivProdArrow e f ℝ ℝ
  let KX := (X * Xᵀ).mulVecLin.ker
  let KY := (Y * Yᵀ).mulVecLin.ker
  let K := (Z * Zᵀ).mulVecLin.ker
  have hmap : K.map E.toLinearMap = KX.prod KY := by
    ext w
    rw [Submodule.mem_map_equiv, Submodule.mem_prod]
    change ((Z * Zᵀ) *ᵥ E.symm w = 0) ↔
      (X * Xᵀ) *ᵥ w.1 = 0 ∧ (Y * Yᵀ) *ᵥ w.2 = 0
    rw [hGram, fromBlocks_mulVec, zero_mulVec, zero_mulVec, add_zero, zero_add]
    have h₁ : (E.symm w : e ⊕ f → ℝ) ∘ Sum.inl = w.1 := rfl
    have h₂ : (E.symm w : e ⊕ f → ℝ) ∘ Sum.inr = w.2 := rfl
    rw [h₁, h₂]
    constructor
    · intro hz
      exact ⟨funext fun x => congrFun hz (Sum.inl x), funext fun y => congrFun hz (Sum.inr y)⟩
    · rintro ⟨hx, hy⟩
      rw [hx, hy]
      funext i
      cases i <;> rfl
  have hK : Module.finrank ℝ K = Module.finrank ℝ KX + Module.finrank ℝ KY := by
    rw [(E.ofSubmodules K (KX.prod KY) hmap).finrank_eq,
      (Submodule.prodEquiv KX KY).finrank_eq, Module.finrank_prod]
  have hXRank : X.rank + Module.finrank ℝ KX = Fintype.card e := by
    rw [← rank_self_mul_transpose X, Matrix.rank]
    simpa [KX] using (X * Xᵀ).mulVecLin.finrank_range_add_finrank_ker
  have hYRank : Y.rank + Module.finrank ℝ KY = Fintype.card f := by
    rw [← rank_self_mul_transpose Y, Matrix.rank]
    simpa [KY] using (Y * Yᵀ).mulVecLin.finrank_range_add_finrank_ker
  have hZRank : Z.rank + Module.finrank ℝ K = Fintype.card e + Fintype.card f := by
    rw [← rank_self_mul_transpose Z, Matrix.rank]
    simpa [K] using (Z * Zᵀ).mulVecLin.finrank_range_add_finrank_ker
  have hker : Z.mulVecLin.ker = X.mulVecLin.ker ⊓ Y.mulVecLin.ker := by
    ext w
    change Z *ᵥ w = 0 ↔ X *ᵥ w = 0 ∧ Y *ᵥ w = 0
    rw [show Z = fromRows X Y from rfl, fromRows_mulVec]
    constructor
    · intro hz
      exact ⟨funext fun x => congrFun hz (Sum.inl x), funext fun y => congrFun hz (Sum.inr y)⟩
    · rintro ⟨hx, hy⟩
      rw [hx, hy]
      funext i
      cases i <;> rfl
  have hZ := Z.mulVecLin.finrank_range_add_finrank_ker
  change Z.rank + _ = _ at hZ
  rw [hker, Module.finrank_fintype_fun_eq_card] at hZ
  omega

/-- Two separated connected cubic supports of orders c and d leave dimension
258 - c - d in their common crossing kernel on each exterior parity. -/
theorem common_crossing_nullity {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hsC : IsSwitching C σ) (hsD : IsSwitching D τ) (p : Bool) :
    let X := crossing C (C ∪ D) σ p
    let Y := crossing D (C ∪ D) τ p
    Module.finrank ℝ (X.mulVecLin.ker ⊓ Y.mulVecLin.ker :
      Submodule ℝ (Outside (C ∪ D) p → ℝ)) = 258 - C.card - D.card := by
  intro X Y
  have hC := direction_edge_count (d := 3) C hrC ⟨σ, hsC⟩ (0 : Fin 9)
  have hD := direction_edge_count (d := 3) D hrD ⟨τ, hsD⟩ (0 : Fin 9)
  have hsCcard (q : Bool) := cubic_parityPart_card hC.symm hrC q
  have hsDcard (q : Bool) := cubic_parityPart_card hD.symm hrD q
  have hrX : X.rank + 1 = (parityPart C p).card :=
    crossing_rank_add_one hrC hcC hsC Finset.subset_union_left
      (fun x hx y hy hyC => hsep.2 x hx y ((Finset.mem_union.mp hy).resolve_left hyC)) p
  have hrY : Y.rank + 1 = (parityPart D p).card :=
    crossing_rank_add_one hrD hcD hsD Finset.subset_union_right
      (fun x hx y hy hyD hxy =>
        hsep.2 y ((Finset.mem_union.mp hy).resolve_right hyD) x hx hxy.symm) p
  have ht := common_crossing_nullity_aux X Y (crossing_mul_transpose_of_separated hsep p)
  have hu : (parityPart (Finset.univ : Finset (Q 9)) (!p)).card = 256 := by
    let eqv : Side Finset.univ (!p) ≃ Q 8 :=
      (Equiv.subtypeEquivRight fun _ => by simp [parityPart]).trans
        (Q9ParityFoldedBoundary.parityFold (n := 8) 0 (!p))
    have := Fintype.card_congr eqv
    simpa [Fintype.card_fun] using this
  have hd : Disjoint (parityPart C (!p)) (parityPart D (!p)) :=
    hsep.1.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hout : (parityPart (Finset.univ \ (C ∪ D)) (!p)).card =
      256 - ((parityPart C (!p)).card + (parityPart D (!p)).card) := by
    have hdiff : parityPart (Finset.univ \ (C ∪ D)) (!p) =
        parityPart Finset.univ (!p) \ (parityPart C (!p) ∪ parityPart D (!p)) := by
      ext x
      by_cases hp : parity x = !p <;> simp [parityPart, hp]
    rw [hdiff, Finset.card_sdiff_of_subset, hu, Finset.card_union_of_disjoint hd]
    exact Finset.union_subset (Finset.filter_subset_filter _ (Finset.subset_univ _))
      (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hsum : (parityPart C (!p)).card + (parityPart D (!p)).card ≤ 256 := by
    rw [← hu, ← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset_filter _ (Finset.subset_univ _))
      (Finset.filter_subset_filter _ (Finset.subset_univ _)))
  change _ + X.rank + Y.rank = Fintype.card ↥(parityPart (Finset.univ \ (C ∪ D)) (!p)) at ht
  rw [Fintype.card_coe, hout] at ht
  rw [hsCcard p] at hrX
  rw [hsDcard p] at hrY
  rw [hsCcard (!p), hsDcard (!p)] at hsum ht
  omega

/-- The joint parity Green matrix of two separated connected balanced cubic supports is
positive semidefinite, with rank at most `258 - C.card - D.card`. -/
theorem joint_defect_rank_le {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hsC : IsSwitching C σ) (hsD : IsSwitching D τ) (p : Bool)
    (cₑ : Fin 9 → Side C p → ℝ) (cₒ : Fin 9 → Side C (!p) → ℝ)
    (dₑ : Fin 9 → Side D p → ℝ) (dₒ : Fin 9 → Side D (!p) → ℝ)
    (hce : ∀ i, (3 : ℝ) • cₑ i - adjacency C p *ᵥ cₒ i = source C p i)
    (hco : ∀ i, (3 : ℝ) • cₒ i - (adjacency C p)ᵀ *ᵥ cₑ i = source C (!p) i)
    (hde : ∀ i, (3 : ℝ) • dₑ i - adjacency D p *ᵥ dₒ i = source D p i)
    (hdo : ∀ i, (3 : ℝ) • dₒ i - (adjacency D p)ᵀ *ᵥ dₑ i = source D (!p) i) :
    let U := C ∪ D
    let B := Matrix.of fun i j =>
      3 * (exterior C U σ p i ⬝ᵥ exterior D U τ p j)
    let G := fromBlocks
      (Matrix.of fun i j => ((C.card : ℝ) / 6) * (9 * (if i = j then 1 else 0) - 1) -
        (cₑ i ⬝ᵥ source C p j + cₒ i ⬝ᵥ source C (!p) j))
      B Bᵀ
      (Matrix.of fun i j => ((D.card : ℝ) / 6) * (9 * (if i = j then 1 else 0) - 1) -
        (dₑ i ⬝ᵥ source D p j + dₒ i ⬝ᵥ source D (!p) j))
    G.PosSemidef ∧ G.rank ≤ 258 - C.card - D.card := by
  intro U B G
  let BC := greenBlock hrC hsC Finset.subset_union_left
    (fun x hx y hy hyC => hsep.2 x hx y ((Finset.mem_union.mp hy).resolve_left hyC))
    p cₑ cₒ hce hco
  let BD := greenBlock hrD hsD Finset.subset_union_right
    (fun x hx y hy hyD hxy => hsep.2 y ((Finset.mem_union.mp hy).resolve_right hyD) x hx hxy.symm)
    p dₑ dₒ hde hdo
  have hsep' : Separated D C := ⟨hsep.1.symm, fun y hy x hx h => hsep.2 x hx y hy h.symm⟩
  have hDC (i : Fin 9) : BD.crossing *ᵥ BC.exterior i = 0 := by
    change crossing D (C ∪ D) τ p *ᵥ exterior C (C ∪ D) σ p i = 0
    rw [Finset.union_comm C D]
    exact crossing_exterior_of_separated hsep' hrC hsC p i
  obtain ⟨_, _, _, hpsd, hrank⟩ := BC.joint_green_defect BD
    (crossing_mul_transpose_of_separated hsep p)
    (crossing_exterior_of_separated hsep hrD hsD p) hDC
  change G.PosSemidef at hpsd
  change G.rank ≤ Module.finrank ℝ (BC.crossing.mulVecLin.ker ⊓ BD.crossing.mulVecLin.ker :
    Submodule ℝ (Outside U p → ℝ)) at hrank
  exact ⟨hpsd, hrank.trans_eq (common_crossing_nullity hsep hrC hrD hcC hcD hsC hsD p)⟩

#print axioms joint_defect_rank_le
#print axioms common_crossing_nullity
#print axioms crossing_rank_add_one
#print axioms crossing_exterior
#print axioms crossing_mul_transpose
#print axioms exterior_gram
#print axioms greenBlock
#print axioms crossing_exterior_of_separated
#print axioms crossing_mul_transpose_of_separated

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityGreenBlock
