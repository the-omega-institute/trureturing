/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/ActualLeech
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/ActualLeech
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict words in finite fixed-source representatives span the actual Leech odd sector. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOneSpanning
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddFixedModeIrreducibility
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

/-! Homogeneous fixed-source representatives and cyclic spanning for the Leech odd sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOne

open OddDifferenceOneSpanning
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixedMode)
open LatticePositiveEnergy (grade stateEnergies stateEnergies_nonneg
  gradeProjection_eq_self_of_mem_grade gradeProjection_zero_of_mem_grade_ne
  positive_actual_mode_grade)
open FixedGradedDuality (fixedGradeSubmodule fixedGradeProjection fixedGradeProjection_sum)
open Lattice.ActualFixedC2 (fixedC2 leech_fixed_c2_cofinite)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open HalfFock.LatticeHalfFockOddFixedModeIrreducibility (fixedParitySlice_odd_irreducible)
open ActualLeechHyperbolic (leechData leech_spec)
open private theta_projection from D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open private gradeProjection_zero_of_not_mem from D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private fixedModeInSource fixedModeInSource_apply from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField
open private lettersIn from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOneSpanning

variable {D : LatticeData} {hu : IsUnit D.G.det}

private abbrev project (n : ℤ) : Module.End ℂ (FixedCarrier D) :=
  (fixedGradeSubmodule D n).subtype.comp (fixedGradeProjection D (theta_projection D) n)

private def component (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : FixedCarrier D) (i : {n // n ∈ stateEnergies D a.val}) : Homogeneous D :=
  ⟨project i.val a, i.val.toNat, by
    have h := Int.toNat_of_nonneg (stateEnergies_nonneg hD a.val i.val i.prop)
    rw [h]
    exact (fixedGradeProjection D (theta_projection D) i.val a).property⟩

private theorem sum_components (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : FixedCarrier D) :
    (∑ i ∈ (stateEnergies D a.val).attach, (component hD a i).state) = a := by
  classical
  exact (Finset.sum_attach _ (fun n => project n a)).trans
    (fixedGradeProjection_sum D (theta_projection D) a)

private theorem project_c2_mem (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (X : Finset (Homogeneous D)) (n : ℕ) :
    fixedC2 D ≤ (Submodule.span ℂ (sourceGenerators X n)).comap (project n) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, rfl⟩
  let S := Submodule.span ℂ (sourceGenerators X n)
  let mode := fixedModeInSource D (-2)
  have mode_apply (v w : FixedCarrier D) : mode v w = fixedMode D v (-2) w :=
    congrArg (fun (f : Module.End ℂ (FixedCarrier D)) => f w) (fixedModeInSource_apply D (-2) v)
  have expand : mode a b =
      ∑ i ∈ (stateEnergies D a.val).attach, ∑ j ∈ (stateEnergies D b.val).attach,
        mode (component hD a i).state (component hD b j).state := by
    conv_lhs => rw [← sum_components hD a, ← sum_components hD b]
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_comm
  change project n (fixedMode D a (-2) b) ∈ S
  rw [← mode_apply, expand, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [mode_apply]
  let x := component hD a i
  let y := component hD b j
  let k := x.weight + y.weight + 1
  let z := fixedMode D x.state (-2) y.state
  change project n z ∈ S
  have hz : z.val ∈ grade D (k : ℤ) := by
    have h := positive_actual_mode_grade D hD x.weight y.weight (-2) _ _ x.graded y.graded
    change z.val ∈ grade D ((x.weight : ℤ) + y.weight - (-2) - 1) at h
    have hk : (x.weight : ℤ) + y.weight - (-2) - 1 = (k : ℤ) := by
      dsimp only [k]
      push_cast
      ring
    rwa [hk] at h
  by_cases he : k = n
  · have hp : project n z = z := Subtype.ext
      (gradeProjection_eq_self_of_mem_grade D n z.val (by simpa only [he] using hz))
    rw [hp]
    exact Submodule.subset_span (Or.inr ⟨x, y, he, rfl⟩)
  · have hp : project n z = 0 := Subtype.ext
      (gradeProjection_zero_of_mem_grade_ne D n k (by exact_mod_cast he) z.val hz)
    rw [hp]
    exact S.zero_mem

private theorem finite_homogeneous_generators
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    [Module.Finite ℂ (FixedCarrier D ⧸ fixedC2 D)] :
    ∃ X : Finset (Homogeneous D),
      ∀ a : Homogeneous D, a.state ∈ Submodule.span ℂ (sourceGenerators X a.weight) := by
  classical
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin (R := ℂ) (M := FixedCarrier D ⧸ fixedC2 D)
  choose r hr using fun i : Fin k => (fixedC2 D).mkQ_surjective (f i)
  let X : Finset (Homogeneous D) := Finset.univ.biUnion fun i : Fin k =>
    (stateEnergies D (r i).val).attach.image (component hD (r i))
  refine ⟨X, fun a => ?_⟩
  have hR : Submodule.span ℂ (Set.range r) ⊔ fixedC2 D = ⊤ := by
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span]
    have e : (fixedC2 D).mkQ '' Set.range r = Set.range f := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hr i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨r i, ⟨i, rfl⟩, hr i⟩
    rw [e, hf]
  let S := Submodule.span ℂ (sourceGenerators X a.weight)
  have reps : Submodule.span ℂ (Set.range r) ≤ S.comap (project a.weight) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change project a.weight (r i) ∈ S
    by_cases hi : (a.weight : ℤ) ∈ stateEnergies D (r i).val
    · let j : {n // n ∈ stateEnergies D (r i).val} := ⟨a.weight, hi⟩
      let x := component hD (r i) j
      have hx : x ∈ X :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image.mpr
          ⟨j, Finset.mem_attach _ _, rfl⟩⟩
      exact Submodule.subset_span (Or.inl ⟨x, hx, Int.toNat_natCast _, rfl⟩)
    · rw [show project a.weight (r i) = 0 from Subtype.ext
        (gradeProjection_zero_of_not_mem D a.weight (r i).val hi)]
      exact S.zero_mem
  have hle : Submodule.span ℂ (Set.range r) ⊔ fixedC2 D ≤ S.comap (project a.weight) :=
    sup_le reps (project_c2_mem hD X a.weight)
  have ha : a.state ∈ Submodule.span ℂ (Set.range r) ⊔ fixedC2 D := by rw [hR]; trivial
  have himage : project a.weight a.state ∈ S := hle ha
  rwa [show project a.weight a.state = a.state from Subtype.ext
    (gradeProjection_eq_self_of_mem_grade D a.weight a.state.val a.graded)] at himage

/-- A nonzero seed in the actual Leech negative sector has a difference-one
spanning set from finitely many homogeneous fixed-source representatives. -/
theorem leech_odd_difference_one
    (u : paritySpace leechData leech_spec.2.1 (-1)) (hu₀ : u ≠ 0) :
    ∃ X : Finset (Homogeneous leechData),
      strictSpan X u = ⊤ ∧
      ∀ a : Homogeneous leechData, a.state ∈ Submodule.span ℂ (sourceGenerators X a.weight) := by
  classical
  let hD := leech_spec.2.2.1
  let : Module.Finite ℂ ActualLeechExtensionC2.LeechFixedQuotient := leech_fixed_c2_cofinite
  obtain ⟨X, hX⟩ := finite_homogeneous_generators hD
  refine ⟨X, ?_, hX⟩
  have hseed : u ∈ strictSpan X u :=
    Submodule.subset_span ⟨[], by simp [lettersIn],
      List.Pairwise.nil, rfl⟩
  have stable (a : FixedCarrier leechData) (n : ℤ) (v : paritySpace leechData leech_spec.2.1 (-1))
      (hv : v ∈ strictSpan X u) : ((fixedParitySlice leechData leech_spec.2.1 (-1) a)[[n]]) v ∈
      strictSpan X u := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨t, _, _, rfl⟩ := hv
      change mixedMode leechData leech_spec.2.1 n a (wordMap t u) ∈ strictSpan X u
      have expand : mixedMode leechData leech_spec.2.1 n a (wordMap t u) =
          ∑ i ∈ (stateEnergies leechData a.val).attach,
            mixedMode leechData leech_spec.2.1 n (component hD a i).state (wordMap t u) := by
        conv_lhs => rw [← sum_components hD a]
        simp only [map_sum, LinearMap.sum_apply]
      rw [expand]
      exact Submodule.sum_mem _ fun i _ =>
        word_mem_strictSpan hD X u hX ((component hD a i, n) :: t)
    | zero => simpa only [map_zero] using (strictSpan X u).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using (strictSpan X u).add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using (strictSpan X u).smul_mem c ih
  rcases fixedParitySlice_odd_irreducible leechData leech_spec.2.1
      (by rw [leech_spec.1]; norm_num) (strictSpan X u) stable with h | h
  · rw [h] at hseed
    exact (hu₀ (by simpa only [Submodule.mem_bot] using hseed)).elim
  · exact h

#print axioms leech_odd_difference_one

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOne
