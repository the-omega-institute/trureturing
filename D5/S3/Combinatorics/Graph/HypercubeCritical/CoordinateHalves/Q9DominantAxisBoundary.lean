/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Dominant coordinate weights force rank loss from paired to empty cube fibres. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-! Dominant-axis elimination for the signed boundary in Hong–Wu–Xia Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary

open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q flip flip_adj flip_flip)
open Q9BoundaryGram (Exterior)
open Q9IsotropicHuang (flipSign parity flip_off_parity)
open Q9WeightedBoundaryGram (signed)
open Q9WeightedSaturation (Rows)

noncomputable section

private def boundaryOver {R : Type*} [CommRing R] (C : Finset (Q 9)) (b : Bool)
    (w : Fin 9 → R) : Matrix (Exterior C b) (Rows C b) R :=
  fun y x => signed w y.1.1 x.1.1

/-- The signed weighted boundary from the retained side of `C` to its actual exterior. -/
def boundary (C : Finset (Q 9)) (b : Bool) (w : Fin 9 → ℝ) :
    Matrix (Exterior C b) (Rows C b) ℝ :=
  boundaryOver C b w

/-- Retained vertices whose other endpoint on the chosen axis also lies in `C`. -/
abbrev PairedRows (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :=
  {x : Rows C b // flip x.1.1 i ∈ C}

/-- Exterior vertices whose entire fibre on the chosen axis lies outside `C`. -/
abbrev EmptyExterior (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :=
  {y : Exterior C b // flip y.1.1 i ∉ C}

private def axisBoundary (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :
    Matrix (Exterior C b) (Rows C b) ℝ :=
  boundary C b (fun a => if a = i then 1 else 0)

private def transverseBoundary {R : Type*} [CommRing R] (C : Finset (Q 9)) (b : Bool)
    (i : Fin 9) (w : Fin 9 → R) : Matrix (Exterior C b) (Rows C b) R :=
  boundaryOver C b (fun a => if a = i then 0 else w a)

/-- The signed transverse boundary from paired retained vertices to empty fibres. -/
def emptyFibreBoundary (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (w : Fin 9 → ℝ) :
    Matrix (EmptyExterior C b i) (PairedRows C b i) ℝ :=
  (transverseBoundary C b i w).submatrix Subtype.val Subtype.val

private def axisWeights (i : Fin 9) (w : Fin 9 → ℝ) (t : ℝ) (a : Fin 9) : ℝ :=
  if a = i then 1 else t * w a

private theorem axisBoundary_apply (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (y : Exterior C b) (x : Rows C b) :
    axisBoundary C b i y x =
      if flip y.1.1 i = x.1.1 then (flipSign i y.1.1 : ℝ) else 0 := by
  classical
  unfold axisBoundary boundary boundaryOver signed
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

private theorem boundary_axisWeights_apply (C : Finset (Q 9)) (b : Bool)
    (i : Fin 9) (w : Fin 9 → ℝ) (t : ℝ) (y : Exterior C b) (x : Rows C b) :
    boundary C b (axisWeights i w t) y x =
      axisBoundary C b i y x + t * transverseBoundary C b i w y x := by
  classical
  simp only [axisBoundary, boundary, transverseBoundary, boundaryOver, signed, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = i <;> by_cases he : flip y.1.1 a = x.1.1 <;>
    simp [axisWeights, ha, he, mul_assoc]

open Classical in
private def rescaledBoundary (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (w : Fin 9 → ℝ)
    (t : ℝ) : Matrix (Exterior C b) (Rows C b) ℝ :=
  fun y x => if flip y.1.1 i ∈ C then
    axisBoundary C b i y x + t * transverseBoundary C b i w y x
  else transverseBoundary C b i w y x

open Classical in
private def polynomialBoundary (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (w : Fin 9 → ℝ) :
    Matrix (Exterior C b) (Rows C b) (Polynomial ℝ) :=
  fun y x => if flip y.1.1 i ∈ C then
    Polynomial.C (axisBoundary C b i y x) +
      Polynomial.X * Polynomial.C (transverseBoundary C b i w y x)
  else Polynomial.C (transverseBoundary C b i w y x)

private theorem boundary_axisWeights_mulVec (C : Finset (Q 9)) (b : Bool)
    (i : Fin 9) (w : Fin 9 → ℝ) (t : ℝ) (v : Rows C b → ℝ) (y : Exterior C b) :
    (boundary C b (axisWeights i w t) *ᵥ v) y =
      (if flip y.1.1 i ∈ C then 1 else t) * (rescaledBoundary C b i w t *ᵥ v) y := by
  classical
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [boundary_axisWeights_apply]
  by_cases hy : flip y.1.1 i ∈ C
  · simp [rescaledBoundary, hy]
  · have hne : flip y.1.1 i ≠ x.1.1 := fun h => hy (h.symm ▸ x.1.property)
    simp [rescaledBoundary, hy, axisBoundary_apply, hne, mul_assoc]

private theorem gram_det_eq_zero_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix κ ι ℝ) :
    (Mᵀ * M).det = 0 ↔ ∃ v ≠ 0, M *ᵥ v = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  simp only [← Matrix.mulVecLin_apply, ← LinearMap.mem_ker,
    Matrix.ker_mulVecLin_transpose_mul_self]

/-- Specializing to zero preserves singularity of the Gram of the rescaled boundary. -/
private theorem rescaled_gram_det_zero (C : Finset (Q 9)) (b : Bool)
    (hker : ∀ v : Fin 9 → ℝ,
      ∃ f ≠ 0, boundary C b v *ᵥ f = 0)
    (i : Fin 9) (w : Fin 9 → ℝ) :
    let A := rescaledBoundary C b i w 0
    (Aᵀ * A).det = 0 := by
  classical
  let P := polynomialBoundary C b i w
  let p := (Pᵀ * P).det
  have hmap (t : ℝ) : P.map (Polynomial.evalRingHom t) = rescaledBoundary C b i w t := by
    ext y x
    by_cases hy : flip y.1.1 i ∈ C
    · simpa [P, polynomialBoundary, rescaledBoundary, hy] using
        mul_comm (transverseBoundary C b i w y x) t
    · simp [P, polynomialBoundary, rescaledBoundary, hy]
  have heval (t : ℝ) :
      Polynomial.eval t p = ((rescaledBoundary C b i w t)ᵀ * rescaledBoundary C b i w t).det := by
    change Polynomial.evalRingHom t (Pᵀ * P).det = _
    rw [RingHom.map_det]
    change ((Pᵀ * P).map (Polynomial.evalRingHom t)).det = _
    rw [Matrix.map_mul, Matrix.transpose_map, hmap]
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioi_infinite (0 : ℝ)).mono
    intro t ht
    have ht' : 0 < t := ht
    obtain ⟨f, hf, hzero⟩ := hker (axisWeights i w t)
    have hscaled : rescaledBoundary C b i w t *ᵥ f = 0 := by
      funext y
      have h := congrFun hzero y
      rw [boundary_axisWeights_mulVec] at h
      have hs : (if flip y.1.1 i ∈ C then (1 : ℝ) else t) ≠ 0 := by
        by_cases hy : flip y.1.1 i ∈ C <;> simp [hy, ne_of_gt ht']
      exact (mul_eq_zero.mp h).resolve_left hs
    change Polynomial.eval t p = 0
    rw [heval]
    exact (gram_det_eq_zero_iff _).2 ⟨f, hf, hscaled⟩
  dsimp only
  rw [← heval, hp, Polynomial.eval_zero]

private theorem flipSign_eq_one_or_neg_one {n : ℕ} (i : Fin n) (x : Q n) :
    flipSign i x = 1 ∨ flipSign i x = -1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · rcases ih j (Sensitivity.π x) with h | h <;>
        cases hx : x 0 <;> simp [flipSign, hx, h]

private theorem vanishes_on_singletons (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (w : Fin 9 → ℝ) {f : Rows C b → ℝ} (hf : rescaledBoundary C b i w 0 *ᵥ f = 0)
    (x : Rows C b) (hx : flip x.1.1 i ∉ C) : f x = 0 := by
  classical
  have hxpar : parity x.1.1 = b := (Finset.mem_filter.mp x.property).2
  let y : Exterior C b := ⟨⟨flip x.1.1 i,
    flip_off_parity i (by rw [hxpar]; cases b <;> decide)⟩, hx⟩
  have hflip : flip y.1.1 i = x.1.1 := flip_flip _ _
  have hy : flip y.1.1 i ∈ C := hflip.symm ▸ x.1.property
  have hentry (z : Rows C b) : rescaledBoundary C b i w 0 y z =
      if x.1.1 = z.1.1 then (flipSign i y.1.1 : ℝ) else 0 := by
    unfold rescaledBoundary
    rw [ite_eq_left hy, zero_mul, add_zero, axisBoundary_apply, hflip]
  have hrow : (∑ z, (if x.1.1 = z.1.1 then (flipSign i y.1.1 : ℝ) else 0) * f z) = 0 := by
    simpa only [Matrix.mulVec, dotProduct, hentry, Pi.zero_apply] using congrFun hf y
  rw [Finset.sum_eq_single x] at hrow
  · rw [ite_eq_left rfl] at hrow
    have hsign : (flipSign i y.1.1 : ℝ) ≠ 0 := by
      rcases flipSign_eq_one_or_neg_one i y.1.1 with h | h <;> simp [h]
    exact (mul_eq_zero.mp hrow).resolve_left hsign
  · intro z _ hz
    have hne : x.1.1 ≠ z.1.1 := fun h => hz (Subtype.ext (Subtype.ext h.symm))
    simp [hne]
  · simp

/-- Saturation of the actual signed boundary for all real weights forces a
nonzero kernel on the paired columns and empty exterior rows for each axis and
each real transverse weighting. -/
theorem exists_emptyFibreBoundary_kernel (C : Finset (Q 9)) (b : Bool)
    (hker : ∀ v : Fin 9 → ℝ,
      ∃ f ≠ 0, boundary C b v *ᵥ f = 0)
    (i : Fin 9) (w : Fin 9 → ℝ) :
    ∃ f ≠ 0, emptyFibreBoundary C b i w *ᵥ f = 0 := by
  classical
  obtain ⟨f, hf, hzero⟩ := (gram_det_eq_zero_iff (rescaledBoundary C b i w 0)).1
    (rescaled_gram_det_zero C b hker i w)
  have hsingle := vanishes_on_singletons C b i w hzero
  refine ⟨fun x => f x.1, ?_, ?_⟩
  · intro hz
    apply hf
    funext x
    by_cases hx : flip x.1.1 i ∈ C
    · exact congrFun hz (⟨x, hx⟩ : PairedRows C b i)
    · exact hsingle x hx
  · funext y
    have heq : (emptyFibreBoundary C b i w *ᵥ fun x => f x.1) y =
        (rescaledBoundary C b i w 0 *ᵥ f) y.1 := by
      simp only [Matrix.mulVec, dotProduct, emptyFibreBoundary, Matrix.submatrix_apply,
        rescaledBoundary, ite_eq_right y.property]
      refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ (fun _ => rfl)
      intro x hx
      have hn : flip x.1.1 i ∉ C := fun h => hx ⟨⟨x, h⟩, rfl⟩
      rw [hsingle x hn, mul_zero]
    exact heq.trans (congrFun hzero y)

private theorem transverseBoundary_eq_zero_of_ne_bit {R : Type*} [CommRing R]
    {C : Finset (Q 9)} {b : Bool} {i : Fin 9} (w : Fin 9 → R)
    {y : Exterior C b} {x : Rows C b} (h : y.1.1 i ≠ x.1.1 i) :
    transverseBoundary C b i w y x = 0 := by
  simp only [transverseBoundary, boundaryOver, signed]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a = i
  · simp [ha]
  · have hflip : flip y.1.1 a ≠ x.1.1 := by
      intro he
      apply h
      simpa only [BalancedCriticalSpectrum.flip, Function.update_of_ne (Ne.symm ha)] using
        congrFun he i
    simp [hflip]

private theorem eval_gram_det {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : Fin 9 → ℝ) (P : Matrix κ ι (MvPolynomial (Fin 9) ℝ)) :
    MvPolynomial.eval w (Pᵀ * P).det = ((P.map (MvPolynomial.eval w))ᵀ *
      P.map (MvPolynomial.eval w)).det := by
  rw [RingHom.map_det]
  change ((Pᵀ * P).map (MvPolynomial.eval w)).det = _
  rw [Matrix.map_mul, Matrix.transpose_map]

/-- A single bit on the dropped axis supports a nonzero empty-fibre kernel
for every real weighting. -/
theorem exists_fixed_bit_emptyFibreBoundary_kernel (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (hker : ∀ w : Fin 9 → ℝ, ∃ f ≠ 0, emptyFibreBoundary C b i w *ᵥ f = 0) :
    ∃ t : Bool, ∀ w : Fin 9 → ℝ, ∃ f : PairedRows C b i → ℝ,
      f ≠ 0 ∧ emptyFibreBoundary C b i w *ᵥ f = 0 ∧
      ∀ x, x.1.1.1 i ≠ t → f x = 0 := by
  classical
  let bit (x : PairedRows C b i) := x.1.1.1 i
  let P : Matrix (EmptyExterior C b i) (PairedRows C b i) (MvPolynomial (Fin 9) ℝ) :=
    (transverseBoundary C b i MvPolynomial.X).submatrix Subtype.val Subtype.val
  let G := Pᵀ * P
  have hmap (w : Fin 9 → ℝ) : P.map (MvPolynomial.eval w) = emptyFibreBoundary C b i w := by
    ext y x
    change MvPolynomial.eval w (transverseBoundary C b i MvPolynomial.X y.1 x.1) =
      transverseBoundary C b i w y.1 x.1
    simp only [transverseBoundary, boundaryOver, signed, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hdet : G.det = 0 := by
    apply MvPolynomial.funext
    intro w
    rw [map_zero, eval_gram_det, hmap]
    exact (gram_det_eq_zero_iff _).2 (hker w)
  have htri : G.BlockTriangular bit := by
    intro x z hxz
    have hne : bit x ≠ bit z := ne_of_gt hxz
    simp only [G, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y.1.1.1 i = bit x
    · have hz : P y z = 0 := transverseBoundary_eq_zero_of_ne_bit MvPolynomial.X
        (y := y.1) (x := z.1) (hy.trans_ne hne)
      rw [hz, mul_zero]
    · have hx : P y x = 0 := transverseBoundary_eq_zero_of_ne_bit MvPolynomial.X
        (y := y.1) (x := x.1) hy
      rw [hx, zero_mul]
  have hprod := htri.det_fintype.symm.trans hdet
  obtain ⟨t, _, ht⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨t, fun w => ?_⟩
  let E := emptyFibreBoundary C b i w
  -- The Gram block is the Gram of the restriction to the selected columns.
  let Pt := P.submatrix id (Subtype.val : {x // bit x = t} → PairedRows C b i)
  let Et := E.submatrix id (Subtype.val : {x // bit x = t} → PairedRows C b i)
  have hmapt : Pt.map (MvPolynomial.eval w) = Et := by
    ext y x
    exact congrFun (congrFun (hmap w) y) x.1
  have ht' : (Ptᵀ * Pt).det = 0 := ht
  have hdet' := congrArg (MvPolynomial.eval w) ht'
  rw [eval_gram_det, hmapt, map_zero] at hdet'
  obtain ⟨g, hg, hzero⟩ := (gram_det_eq_zero_iff Et).1 hdet'
  let f (x : PairedRows C b i) : ℝ := if hx : bit x = t then g ⟨x, hx⟩ else 0
  have hf (x : {x // bit x = t}) : f x.1 = g x := dite_eq_left x.2
  refine ⟨f, ?_, ?_, fun x hx => dite_eq_right hx⟩
  · intro he
    apply hg
    funext x
    exact (hf x).symm.trans (congrFun he x.1)
  · funext y
    calc
      (E *ᵥ f) y = (Et *ᵥ g) y := by
        simp only [Matrix.mulVec, dotProduct, Et, Matrix.submatrix_apply, id_eq]
        symm
        refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ ?_
        · intro x hx
          have hne : bit x ≠ t := fun h => hx ⟨⟨x, h⟩, rfl⟩
          simp [f, hne]
        · intro x
          rw [hf]
      _ = 0 := congrFun hzero y

end

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary

open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open Q9BoundaryGram (Exterior)
open Q9IsotropicHuang (parity)
open Q9WeightedSaturation (Rows signedBiadjacency defect)
open Q9WeightedBoundaryGram (signed signed_transpose switched gram_split)
open Q9ComponentSaturation (exists_two_weighted_singular_components)
open TwoBalancedComponents (componentFinset)
open Translation.Q9ActualAperiodicity (signed_defect_det_eq_component)

open Classical in
private theorem boundary_gram_eq_signed_defect (C : Finset (Q 9)) (b : Bool)
    (w : Fin 9 → ℝ) :
    (boundary C b w)ᵀ * boundary C b w = defect w (signedBiadjacency w C b) := by
  let r : Rows C b ↪ Q 9 :=
    ⟨fun x => x.1.1, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  have hr (x : Rows C b) : parity (r x) = b := (Finset.mem_filter.mp x.property).2
  have hs : switched w (fun _ => 1) = signed w := by
    ext x y
    simp [switched]
  have h := gram_split w (fun _ => 1) (by simp) C b r hr
  dsimp only at h
  rw [hs] at h
  let K := (signed w).submatrix r (fun y : Exterior C b => y.1.1)
  have hB : boundary C b w = Kᵀ := by
    ext y x
    exact congrFun (congrFun (signed_transpose w) y.1.1) (r x) |>.symm
  rw [hB, Matrix.transpose_transpose]
  exact h

open Classical in
/-- The same two actual components of a 258-vertex subcubic support pass every
dominant-axis empty-fibre boundary test. -/
theorem exists_two_components_with_emptyFibre_kernels (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (b : Bool) :
    ∃ C D : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      C ≠ D ∧ ∀ (i : Fin 9) (w : Fin 9 → ℝ),
        (∃ f ≠ 0, emptyFibreBoundary (componentFinset U C) b i w *ᵥ f = 0) ∧
        (∃ f ≠ 0, emptyFibreBoundary (componentFinset U D) b i w *ᵥ f = 0) := by
  obtain ⟨C, D, hCD, hdet⟩ := exists_two_weighted_singular_components U hU hdeg b
  refine ⟨C, D, hCD, fun i w => ?_⟩
  have go (A : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
      (hA : ∀ v : Fin 9 → ℝ, (Q9ComponentSaturation.componentDefect v U b A).det = 0) :
      ∃ f ≠ 0, emptyFibreBoundary (componentFinset U A) b i w *ᵥ f = 0 := by
    apply exists_emptyFibreBoundary_kernel _ _ _ i w
    intro v
    apply (gram_det_eq_zero_iff _).1
    rw [boundary_gram_eq_signed_defect, signed_defect_det_eq_component]
    exact hA v
  exact ⟨go C (fun v => (hdet v).1), go D (fun v => (hdet v).2)⟩

private theorem projected_parity_eq (i : Fin 9) {x : Q 9} {b t : Bool}
    (hb : parity x = b) (ht : x i = t) :
    (∑ j : Fin 8, x (i.succAbove j)) = t + b := by
  change (∑ j : Fin 9, x j) = b at hb
  rw [Fin.sum_univ_succAbove x i, ht] at hb
  rw [← hb]
  cases t <;> cases (∑ j : Fin 8, x (i.succAbove j)) <;> rfl

open Classical in
/-- For each retained parity of a 258-point subcubic support, two distinct actual
components have a nonzero kernel on paired fibres for every transverse weighting
and mask. For each dominant axis, each component has a single projected parity
supporting these kernels. -/
theorem exists_two_components_with_fixed_projectedParity_emptyFibre_kernels
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (b : Bool) :
    ∃ C D : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      C ≠ D ∧ ∀ i : Fin 9, ∃ pC pD : Bool,
        ∀ (I : Finset (Fin 9)) (w : Fin 9 → ℝ),
          (∃ f : PairedRows (componentFinset U C) b i → ℝ,
            f ≠ 0 ∧
            emptyFibreBoundary (componentFinset U C) b i (fun a => if a ∈ I then w a else 0)
              *ᵥ f = 0 ∧
            ∀ x, (∑ j : Fin 8, x.1.1.1 (i.succAbove j)) ≠ pC → f x = 0) ∧
          (∃ f : PairedRows (componentFinset U D) b i → ℝ,
            f ≠ 0 ∧
            emptyFibreBoundary (componentFinset U D) b i (fun a => if a ∈ I then w a else 0)
              *ᵥ f = 0 ∧
            ∀ x, (∑ j : Fin 8, x.1.1.1 (i.succAbove j)) ≠ pD → f x = 0) := by
  obtain ⟨C, D, hCD, hker⟩ := exists_two_components_with_emptyFibre_kernels U hU hdeg b
  refine ⟨C, D, hCD, fun i => ?_⟩
  obtain ⟨tC, hC⟩ := exists_fixed_bit_emptyFibreBoundary_kernel (componentFinset U C) b i
    (fun w => (hker i w).1)
  obtain ⟨tD, hD⟩ := exists_fixed_bit_emptyFibreBoundary_kernel (componentFinset U D) b i
    (fun w => (hker i w).2)
  refine ⟨tC + b, tD + b, fun I w => ?_⟩
  let v (a : Fin 9) : ℝ := if a ∈ I then w a else 0
  obtain ⟨f, hf, hfzero, hfsupp⟩ := hC v
  obtain ⟨g, hg, hgzero, hgsupp⟩ := hD v
  refine ⟨⟨f, hf, hfzero, ?_⟩, ⟨g, hg, hgzero, ?_⟩⟩
  · intro x hx
    apply hfsupp x
    intro ht
    exact hx (projected_parity_eq i (Finset.mem_filter.mp x.1.property).2 ht)
  · intro x hx
    apply hgsupp x
    intro ht
    exact hx (projected_parity_eq i (Finset.mem_filter.mp x.1.property).2 ht)

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary
