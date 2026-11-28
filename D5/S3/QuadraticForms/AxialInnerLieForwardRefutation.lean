/- GID: D5/S3/QuadraticForms/AxialInnerLieForwardRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/AxialInnerLieForwardRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.claim; result=D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.result; claim=D5/S3/QuadraticForms/AxialInnerLieForwardRefutation.claim
   digest: The simple rational spin factor J₄ has a selected-axis inner Lie algebra with a proper nonzero ideal. -/

/- proof_shape: result: content
   admission_basis: open-problem-resolution (issue #35124)
   escape_witness: simplicity of the rational spin factor and the proper nonzero kernel of a split projection
   Direct frozen dependencies: OrthogonalLieStructure. -/

import D5.S3.QuadraticForms.OrthogonalLieStructure
import D5.S3.Algebra.RationalSpinFactor

/-!
The forward implication in Gorshkov–Shpectorov, Problem 3.20 (journal
Problem 2.20), specialized to rational primitive Jordan-half axial algebras.
The carrier is the spin factor with four vector coordinates. The designated
refutation result is exempt from four-slot escape registration.
-/

open scoped Matrix
open Matrix LieAlgebra OmegaMath.RationalSpinFactor
open D5.S3.QuadraticForms

namespace D5.S3.QuadraticForms.AxialInnerLieForwardRefutation

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem spin_comm (x y : J (Fin 4)) : spinLeft x y = spinLeft y x := by
  simp only [spinLeft_apply, dotProduct_comm x.2 y.2, mul_comm x.1 y.1,
    add_comm (x.1 • y.2)]

private theorem spin_simple : AlgebraSimple (spinLeft (n := Fin 4)) := by
  intro I hI
  by_cases hbot : I = ⊥
  · exact Or.inl hbot
  right
  have hunit : ((1, 0) : J (Fin 4)) ∈ I := by
    obtain ⟨x, hx, hx0⟩ := I.ne_bot_iff.mp hbot
    have from_scalar (a : ℚ) (ha : a ≠ 0) (h : ((a, 0) : J (Fin 4)) ∈ I) :
        ((1, 0) : J (Fin 4)) ∈ I := by
      simpa [smul_eq_mul, ha] using I.smul_mem a⁻¹ h
    by_cases hu : x.2 = 0
    · apply from_scalar x.1
      · intro ha
        exact hx0 (Prod.ext ha hu)
      · simpa only [← hu] using hx
    obtain ⟨i, hi⟩ : ∃ i, x.2 i ≠ 0 := by
      by_contra! h
      exact hu (funext h)
    let j : Fin 4 := if i = 0 then 1 else 0
    have hji : j ≠ i := by
      by_cases h : i = 0 <;> simp [j, h, Ne.symm]
    let u : J (Fin 4) := (0, coord j)
    let v : J (Fin 4) := (0, coord i)
    let w : Fin 4 → ℚ := (skewPair (coord j) (coord i)).val *ᵥ x.2
    have hw : ((0, w) : J (Fin 4)) ∈ I := by
      rw [← spinBracket_apply u v x]
      change spinLeft u (spinLeft v x) - spinLeft v (spinLeft u x) ∈ I
      exact I.sub_mem (hI _ _ (hI _ _ hx)) (hI _ _ (hI _ _ hx))
    have hw0 : w ≠ 0 := by
      intro heq
      have hj := congrFun heq j
      have hwj : w j = x.2 i := by
        change ((vecMulVec (coord j) (coord i) - vecMulVec (coord i) (coord j)) *ᵥ x.2) j = _
        simp [sub_mulVec, vecMulVec_mulVec, coord, Pi.single_apply, hji, Ne.symm hji]
      exact hi (hwj ▸ hj)
    have hw2 : w ⬝ᵥ w ≠ 0 := fun h => hw0 (dotProduct_self_eq_zero.mp h)
    apply from_scalar (w ⬝ᵥ w) hw2
    simpa [spinLeft_apply] using hI (0, w) (0, w) hw
  apply top_unique
  intro x _
  simpa [spinLeft_apply] using hI x (1, 0) hunit

private theorem selected_has_proper_ideal :
    ∃ I : LieIdeal ℚ (selectedLie spinLeft (signedAxes : Set (J (Fin 4)))),
      I ≠ ⊥ ∧ I ≠ ⊤ := by
  let K := Orthogonal.so (Fin 3) ℚ
  let e : selectedLie spinLeft (signedAxes : Set (J (Fin 4))) ≃ₗ⁅ℚ⁆ K × K :=
    (signedAxesLieEquiv (n := Fin 4)).symm.trans OrthogonalLieStructure.soFourEquiv
  let p := (LieHom.snd ℚ K K).comp e.toLieHom
  let r : K := skewPair (coord (0 : Fin 3)) (coord 1)
  have hr : r ≠ 0 := by
    intro h
    have h01 := congrArg (fun M : K => M.val 0 1) h
    norm_num [r, skewPair, coord, vecMulVec_apply, Pi.single_apply] at h01
  refine ⟨p.ker, ?_, ?_⟩
  · intro h
    have hx : e.symm (r, 0) ∈ p.ker := LieHom.mem_ker.mpr (by simp [p])
    rw [h, LieSubmodule.mem_bot] at hx
    have he := congrArg (fun a => (e a).1) hx
    exact hr (by simpa using he)
  · intro h
    have hx : e.symm (0, r) ∈ p.ker := h.symm ▸ LieSubmodule.mem_top _
    have he := LieHom.mem_ker.mp hx
    exact hr (by simpa [p] using he)

/-- The printed forward implication restricted to finite-dimensional
rational primitive Jordan-half axial algebras with a chosen generating set. -/
def claim : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℚ A] [FiniteDimensional ℚ A]
    (L : A →ₗ[ℚ] Module.End ℚ A) (X : Set A),
    (∀ a b, L a b = L b a) → (∀ a ∈ X, IsAxis L a) → Generates L X →
      AlgebraSimple L → IsSimple ℚ (selectedLie L X)

theorem result : ¬ claim := by
  intro h
  letI := h (J (Fin 4)) spinLeft signedAxes spin_comm signedAxes_are_axes signedAxes_generate
    spin_simple
  obtain ⟨I, hbot, htop⟩ := selected_has_proper_ideal
  exact (IsSimple.eq_bot_or_eq_top I).elim hbot htop

end D5.S3.QuadraticForms.AxialInnerLieForwardRefutation
