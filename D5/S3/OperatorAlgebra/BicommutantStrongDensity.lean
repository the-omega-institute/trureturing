/- GID: D5/S3/OperatorAlgebra/BicommutantStrongDensity
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-vector strong approximation of an operator in the bicommutant of a unital star subalgebra. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Omega original.

Finite-vector strong approximation of an operator in the bicommutant of a unital
star subalgebra. The proof uses the projection onto the closed orbit of a tuple.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.BicommutantStrongDensity

open ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

private abbrev Batch (ι H : Type*) := PiLp 2 (fun _ : ι => H)
private abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →L[ℂ] H

private def diagonal (A : Operator H) (y : Batch ι H) : Batch ι H :=
  WithLp.toLp 2 (fun i => A (y i))

omit [CompleteSpace H] [Fintype ι] in
private theorem diagonal_continuous (A : Operator H) : Continuous (diagonal (ι := ι) A) := by
  change Continuous ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm ∘
    (fun y : Batch ι H => fun i => A (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => H) i y)))
  apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous
  exact continuous_pi fun i => A.continuous.comp (PiLp.proj (𝕜 := ℂ) 2 _ i).continuous

private theorem inner_diagonal_right (A : Operator H) (y z : Batch ι H) :
    ⟪y, diagonal A z⟫_ℂ = ⟪diagonal (star A) y, z⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (adjoint_inner_left A (z i) (y i)).symm

private def orbit (S : StarSubalgebra ℂ (Operator H)) (x : Batch ι H) :
    Submodule ℂ (Batch ι H) where
  carrier := Set.range (fun A : S => diagonal (A : Operator H) x)
  zero_mem' := ⟨0, PiLp.ext fun i => by
    change (0 : Operator H) (x i) = 0
    rfl⟩
  add_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A + B, PiLp.ext fun _ => rfl⟩
  smul_mem' := by
    rintro c _ ⟨A, rfl⟩
    exact ⟨c • A, PiLp.ext fun _ => rfl⟩

private theorem diagonal_mem_closedOrbit (S : StarSubalgebra ℂ (Operator H))
    (x : Batch ι H) {A : Operator H} (hA : A ∈ S) {y : Batch ι H}
    (hy : y ∈ (orbit S x).topologicalClosure) :
    diagonal A y ∈ (orbit S x).topologicalClosure := by
  apply map_mem_closure (diagonal_continuous A) hy
  intro z hz
  change z ∈ Set.range (fun B : S => diagonal (B : Operator H) x) at hz
  obtain ⟨B, rfl⟩ := hz
  exact ⟨⟨A * (B : Operator H), mul_mem hA B.property⟩, PiLp.ext fun _ => rfl⟩

private theorem projection_diagonal (S : StarSubalgebra ℂ (Operator H)) (x : Batch ι H)
    {A : Operator H} (hA : A ∈ S) (y : Batch ι H) :
    (orbit S x).topologicalClosure.starProjection (diagonal A y) =
      diagonal A ((orbit S x).topologicalClosure.starProjection y) := by
  let U := (orbit S x).topologicalClosure
  change U.starProjection (diagonal A y) = diagonal A (U.starProjection y)
  apply U.eq_starProjection_of_mem_orthogonal
  · exact diagonal_mem_closedOrbit S x hA (U.starProjection_apply_mem y)
  · have he : diagonal A y - diagonal A (U.starProjection y) =
        diagonal A (y - U.starProjection y) := by
      ext i
      exact (map_sub A (y i) (U.starProjection y i)).symm
    rw [he]
    apply (U.mem_orthogonal _).2
    intro z hz
    rw [inner_diagonal_right]
    exact U.inner_right_of_mem_orthogonal
      (diagonal_mem_closedOrbit S x (star_mem hA) hz) (U.sub_starProjection_mem_orthogonal y)

private def single [DecidableEq ι] (i : ι) : H →L[ℂ] Batch ι H :=
  LinearMap.mkContinuous
    { toFun := PiLp.single 2 (β := fun _ : ι => H) i
      map_add' x y := PiLp.single_add 2 (β := fun _ : ι => H) i
      map_smul' c x := by
        ext j
        by_cases h : j = i <;> simp [h] }
    1 (fun y => by
      change ‖PiLp.single 2 (β := fun _ : ι => H) i y‖ ≤ 1 * ‖y‖
      rw [PiLp.norm_single, one_mul])

omit [CompleteSpace H] in
private theorem diagonal_single [DecidableEq ι] (A : Operator H) (i : ι) (y : H) :
    diagonal A (single i y) = single i (A y) := by
  ext j
  change A (PiLp.single 2 (β := fun _ : ι => H) i y j) = PiLp.single 2 (β := fun _ : ι => H) i (A y) j
  by_cases h : j = i <;> simp [PiLp.single_apply, h]

omit [CompleteSpace H] in
private theorem sum_single [DecidableEq ι] (y : Batch ι H) :
    (∑ i, single i (y i)) = y := by
  ext j
  let p : Batch ι H →L[ℂ] H := PiLp.proj (𝕜 := ℂ) 2 _ j
  change p (∑ i, single i (y i)) = p y
  rw [map_sum, Finset.sum_eq_single j]
  · exact PiLp.single_eq_same (p := 2) (β := fun _ : ι => H) j (y j)
  · intro i _ hi
    exact PiLp.single_eq_of_ne (p := 2) (β := fun _ : ι => H) (Ne.symm hi) (y i)
  · simp

private def entry [DecidableEq ι] (P : Batch ι H →L[ℂ] Batch ι H) (j i : ι) :
    Operator H :=
  (PiLp.proj (𝕜 := ℂ) 2 _ j).comp (P.comp (single i))

private theorem entry_centralizes [DecidableEq ι] (S : StarSubalgebra ℂ (Operator H))
    (x : Batch ι H) (j i : ι) :
    entry (orbit S x).topologicalClosure.starProjection j i ∈ Set.centralizer (S : Set (Operator H)) := by
  intro A hA
  ext y
  have he := congrArg (fun z : Batch ι H => z j) (projection_diagonal S x hA (single i y))
  rw [diagonal_single] at he
  exact he.symm

omit [CompleteSpace H] in
private theorem operator_eq_sum_entries [DecidableEq ι] (P : Batch ι H →L[ℂ] Batch ι H)
    (y : Batch ι H) (j : ι) : P y j = ∑ i, entry P j i (y i) := by
  let f := (PiLp.proj (𝕜 := ℂ) 2 _ j).comp P
  change f y = ∑ i, f (single i (y i))
  rw [← map_sum, sum_single]

/-- Every bicommutant operator can be approximated by one element of the algebra
simultaneously on an arbitrary finite family of vectors. -/
theorem exists_approximation (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i, ‖A (x i) - T (x i)‖ < ε := by
  classical
  let u : Batch ι H := WithLp.toLp 2 x
  let U := (orbit S u).topologicalClosure
  let P := U.starProjection
  have hu : u ∈ U := by
    apply (orbit S u).le_topologicalClosure
    change u ∈ Set.range (fun A : S => diagonal (A : Operator H) u)
    exact ⟨1, PiLp.ext fun _ => rfl⟩
  have hP : P u = u := U.starProjection_eq_self_iff.mpr hu
  have hcomm : P (diagonal T u) = diagonal T (P u) := by
    ext j
    rw [operator_eq_sum_entries P (diagonal T u) j]
    change (∑ i, entry P j i (T (u i))) = T (P u j)
    rw [operator_eq_sum_entries P u j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : entry P j i * T = T * entry P j i := hT _ (entry_centralizes S u j i)
    exact DFunLike.congr_fun he (u i)
  have hmem : diagonal T u ∈ U := U.starProjection_eq_self_iff.mp (hcomm.trans (congrArg _ hP))
  change diagonal T u ∈ closure (Set.range (fun A : S => diagonal (A : Operator H) u)) at hmem
  obtain ⟨z, ⟨A, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  refine ⟨A, A.property, fun i => ?_⟩
  have h := (PiLp.dist_apply_le (diagonal T u) (diagonal (A : Operator H) u) i).trans_lt hdist
  rw [dist_comm, dist_eq_norm] at h
  exact h

end Omega.BicommutantStrongDensity
