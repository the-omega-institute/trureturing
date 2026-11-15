/- GID: D5/S3/Quantum/Analysis/GNSOrderCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/GNSOrderCoordinates
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal]
   utility: none
   digest: Dominated positive functionals have canonical positive GNS commutant coordinates. -/

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import D5.S3.Quantum.Algebra.StateApproximation.IrreducibleBoundedLift
import Mathlib.Tactic

/-! Classical order-Radon--Nikodym coordinates for the actual completed GNS.
This is a foundational supplier, not the full-curvature centralizer theorem.
No faithfulness, normalization, separability or nonzero hypothesis is imposed. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace
open UniformSpace.Completion ContinuousLinearMap

namespace D5.S3.Quantum.Analysis.GNSOrderCoordinates

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Order comparison on the positive cone, rather than pointwise on all complex inputs. -/
def Dominated (φ ψ : A →ₚ[ℂ] ℂ) : Prop := ∀ a, 0 ≤ a → φ a ≤ ψ a

/-- The unnormalized cyclic vector, also in a zero GNS space. -/
def cyclicVector (ψ : A →ₚ[ℂ] ℂ) : ψ.GNS := (ψ.toPreGNS 1 : ψ.GNS)

private theorem orbit_eq (ψ : A →ₚ[ℂ] ℂ) (a : A) :
    ψ.gnsStarAlgHom a (cyclicVector ψ) = (ψ.toPreGNS a : ψ.GNS) := by
  change ψ.gnsNonUnitalStarAlgHom a ((ψ.toPreGNS 1) : ψ.GNS) = _
  simp [PositiveLinearMap.leftMulMapPreGNS]

private theorem dense_pre (ψ : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => (ψ.toPreGNS a : ψ.GNS)) :=
  UniformSpace.Completion.denseRange_coe.comp ψ.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

private theorem pre_norm_le (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (x : ψ.PreGNS) :
    ‖φ.toPreGNS (ψ.ofPreGNS x)‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp := h (star (ψ.ofPreGNS x) * ψ.ofPreGNS x) (star_mul_self_nonneg _)
  have hφ := congrArg Complex.re (φ.preGNS_norm_sq (φ.toPreGNS (ψ.ofPreGNS x)))
  have hψ := congrArg Complex.re (ψ.preGNS_norm_sq x)
  simp only [← Complex.ofReal_pow, Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS] at hφ hψ
  exact hφ.trans_le ((Complex.le_def.mp hp).1.trans_eq hψ.symm)

private def preComparison (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    ψ.PreGNS →L[ℂ] φ.PreGNS :=
  (φ.toPreGNS.toLinearMap.comp ψ.ofPreGNS.toLinearMap).mkContinuous 1
    (fun x => by simpa using pre_norm_le φ ψ h x)

/-- The canonical comparison contraction, defined on pre-GNS and then completed. -/
def comparison (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) : ψ.GNS →L[ℂ] φ.GNS :=
  (preComparison φ ψ h).completion

private theorem comparison_coe (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a : A) :
    comparison φ ψ h (ψ.toPreGNS a : ψ.GNS) = (φ.toPreGNS a : φ.GNS) := by
  simp [comparison, preComparison]

/-- Domination controls the comparison map on the entire completion. -/
theorem comparison_norm_le (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    ‖comparison φ ψ h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    simpa [comparison, preComparison] using pre_norm_le φ ψ h x

/-- Intertwining is proved on the dense pre-GNS range and extended by continuity. -/
theorem comparison_intertwines (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a : A) :
    comparison φ ψ h ∘L ψ.gnsStarAlgHom a =
      φ.gnsStarAlgHom a ∘L comparison φ ψ h := by
  apply DFunLike.coe_injective
  apply (dense_pre ψ).equalizer <;> try fun_prop
  funext b
  change comparison φ ψ h (ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS b : ψ.GNS)) = _
  simp [comparison_coe, PositiveLinearMap.leftMulMapPreGNS,
    show φ.gnsStarAlgHom a = φ.gnsNonUnitalStarAlgHom a from rfl]

/-- Taking the adjoint at star a gives the reverse intertwining identity. -/
theorem comparison_adjoint_intertwines (φ ψ : A →ₚ[ℂ] ℂ)
    (h : Dominated φ ψ) (a : A) :
    (comparison φ ψ h).adjoint ∘L φ.gnsStarAlgHom a =
      ψ.gnsStarAlgHom a ∘L (comparison φ ψ h).adjoint := by
  have he := congrArg ContinuousLinearMap.adjoint (comparison_intertwines φ ψ h (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using he.symm

/-- The Radon--Nikodym operator is constructed, not assumed. -/
def coordinate (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) : ψ.GNS →L[ℂ] ψ.GNS :=
  (comparison φ ψ h).adjoint ∘L comparison φ ψ h

private theorem coordinate_inner (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a b : A) :
    inner ℂ (ψ.toPreGNS a : ψ.GNS) (coordinate φ ψ h (ψ.toPreGNS b : ψ.GNS)) =
      φ (star a * b) := by
  simp [coordinate, ContinuousLinearMap.adjoint_inner_right, comparison_coe,
    UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

/-- The constructed coordinate belongs to the positive commutant unit interval. -/
theorem coordinate_mem (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    0 ≤ coordinate φ ψ h ∧ coordinate φ ψ h ≤ 1 ∧
      ∀ a, Commute (coordinate φ ψ h) (ψ.gnsStarAlgHom a) := by
  have hp : (coordinate φ ψ h).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self _
  refine ⟨ContinuousLinearMap.nonneg_iff_isPositive.mpr hp, ?_, ?_⟩
  · rw [ContinuousLinearMap.le_def]
    refine ⟨ContinuousLinearMap.isPositive_one.isSymmetric.sub hp.isSymmetric, ?_⟩
    intro x
    have hn := (comparison φ ψ h).le_opNorm x
    have hb := comparison_norm_le φ ψ h
    have hn' : ‖comparison φ ψ h x‖ ≤ ‖x‖ :=
      hn.trans (mul_le_of_le_one_left (norm_nonneg x) hb)
    have hs := (comparison φ ψ h).apply_norm_sq_eq_inner_adjoint_left x
    change 0 ≤ (inner ℂ (x - coordinate φ ψ h x) x).re
    have hx := norm_sq_eq_re_inner (𝕜 := ℂ) x
    simp only [RCLike.re_eq_complex_re] at hx hs
    rw [inner_sub_left, Complex.sub_re, ← hx]
    change 0 ≤ ‖x‖ ^ 2 - (inner ℂ (((comparison φ ψ h).adjoint ∘L
      comparison φ ψ h) x) x).re
    rw [← hs]
    nlinarith [norm_nonneg ((comparison φ ψ h) x), norm_nonneg x]
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    change (comparison φ ψ h).adjoint (comparison φ ψ h (ψ.gnsStarAlgHom a x)) =
      ψ.gnsStarAlgHom a ((comparison φ ψ h).adjoint (comparison φ ψ h x))
    rw [show comparison φ ψ h (ψ.gnsStarAlgHom a x) =
      φ.gnsStarAlgHom a (comparison φ ψ h x) from
        congrArg (fun F => F x) (comparison_intertwines φ ψ h a)]
    exact congrArg (fun F => F (comparison φ ψ h x))
      (comparison_adjoint_intertwines φ ψ h a)

/-- Exact coefficient formula for the original positive functional. -/
theorem coordinate_represents (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) (a : A) :
    φ a = inner ℂ (cyclicVector ψ)
      (coordinate φ ψ h (ψ.gnsStarAlgHom a (cyclicVector ψ))) := by
  rw [orbit_eq]
  simpa [cyclicVector] using (coordinate_inner φ ψ h 1 a).symm

/-- Use the existing continuous coefficient functional, with the actual GNS arguments. -/
abbrev coefficient (ψ : A →ₚ[ℂ] ℂ) (T : ψ.GNS →L[ℂ] ψ.GNS) : A →ₗ[ℂ] ℂ :=
  (Physicslib4.GNS.coeffFunctional ψ.gnsStarAlgHom (cyclicVector ψ) T).toLinearMap

/-- The coefficient determines every commutant operator, without positivity. -/
theorem coefficient_injective (ψ : A →ₚ[ℂ] ℂ)
    (T S : ψ.GNS →L[ℂ] ψ.GNS)
    (hT : ∀ a, Commute T (ψ.gnsStarAlgHom a))
    (hS : ∀ a, Commute S (ψ.gnsStarAlgHom a))
    (h : coefficient ψ T = coefficient ψ S) : T = S := by
  have hcyc : Physicslib4.GNS.IsCyclicVector ψ.gnsStarAlgHom (cyclicVector ψ) := by
    change DenseRange (fun a : A => ψ.gnsStarAlgHom a (cyclicVector ψ))
    simpa only [orbit_eq] using dense_pre ψ
  have hz : T - S = (0 : ℂ) • 1 :=
    Physicslib4.GNS.eq_smul_one_of_commute_of_cyclic hcyc
      (fun a => ((hT a).sub_left (hS a)).eq.symm) (fun a => by
        have he := congrArg (fun f : A →ₗ[ℂ] ℂ => f a) h
        change inner ℂ (cyclicVector ψ) (T (ψ.gnsStarAlgHom a (cyclicVector ψ))) =
          inner ℂ (cyclicVector ψ) (S (ψ.gnsStarAlgHom a (cyclicVector ψ))) at he
        simp only [sub_apply, inner_sub_right, he, sub_self, zero_mul])
  exact sub_eq_zero.mp (by simpa using hz)

/-- Positivity of a commutant operator is equivalent to positivity of its actual coefficient.
The reverse direction extends its quadratic form from the dense cyclic range. -/
theorem coefficient_nonneg_iff (ψ : A →ₚ[ℂ] ℂ) (T : ψ.GNS →L[ℂ] ψ.GNS)
    (hc : ∀ a, Commute T (ψ.gnsStarAlgHom a)) :
    (∀ a, 0 ≤ a → 0 ≤ coefficient ψ T a) ↔ 0 ≤ T := by
  have hdiag (a : A) : coefficient ψ T (star a * a) =
      inner ℂ (ψ.toPreGNS a : ψ.GNS) (T (ψ.toPreGNS a : ψ.GNS)) := by
    change Physicslib4.GNS.coeffFunctional ψ.gnsStarAlgHom (cyclicVector ψ) T
      (star a * a) = _
    simpa only [orbit_eq] using
      Physicslib4.GNS.coeffFunctional_star_mul (π := ψ.gnsStarAlgHom)
        (Ω := cyclicVector ψ) (T := T) (fun a => (hc a).eq.symm) a
  constructor
  · intro h
    have hq (x : ψ.GNS) : 0 ≤ inner ℂ x (T x) := by
      have hd : DenseRange (fun a : A => (ψ.toPreGNS a : ψ.GNS)) := dense_pre ψ
      have hp : ∀ x : ψ.GNS, 0 ≤ inner ℂ x (T x) := by
        apply isClosed_property hd (isClosed_le continuous_const (by fun_prop))
        intro a
        rw [← hdiag]
        exact h _ (star_mul_self_nonneg a)
      exact hp x
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
    intro x
    have hl : 0 ≤ inner ℂ (T x) x := by
      rw [← inner_conj_symm]
      change 0 ≤ star (inner ℂ x (T x))
      exact star_nonneg_iff.mpr (hq x)
    exact ⟨by apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hl).2.symm],
      (Complex.nonneg_iff.mp hl).1⟩
  · intro h a ha
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    rw [hdiag]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp h).inner_nonneg_right _

/-- Order is reflected as well as preserved; no representing operator is postulated. -/
theorem coefficient_order_iff (ψ : A →ₚ[ℂ] ℂ) (T S : ψ.GNS →L[ℂ] ψ.GNS)
    (hT : ∀ a, Commute T (ψ.gnsStarAlgHom a))
    (hS : ∀ a, Commute S (ψ.gnsStarAlgHom a)) :
    (∀ a, 0 ≤ a → coefficient ψ T a ≤ coefficient ψ S a) ↔ T ≤ S := by
  have hc : ∀ a, Commute (S - T) (ψ.gnsStarAlgHom a) := fun a => (hS a).sub_left (hT a)
  have he := coefficient_nonneg_iff ψ (S - T) hc
  change (∀ a, 0 ≤ a → 0 ≤ inner ℂ (cyclicVector ψ)
    ((S - T) (ψ.gnsStarAlgHom a (cyclicVector ψ)))) ↔ 0 ≤ S - T at he
  change (∀ a, 0 ≤ a → inner ℂ (cyclicVector ψ)
    (T (ψ.gnsStarAlgHom a (cyclicVector ψ))) ≤ inner ℂ (cyclicVector ψ)
    (S (ψ.gnsStarAlgHom a (cyclicVector ψ)))) ↔ T ≤ S
  simpa only [sub_nonneg, sub_apply, inner_sub_right] using he

/-- A positive commutant operator defines an actual positive functional. -/
def functional (ψ : A →ₚ[ℂ] ℂ) (T : ψ.GNS →L[ℂ] ψ.GNS)
    (hp : 0 ≤ T) (hc : ∀ a, Commute T (ψ.gnsStarAlgHom a)) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (coefficient ψ T) ((coefficient_nonneg_iff ψ T hc).mpr hp)

private theorem coefficient_one (ψ : A →ₚ[ℂ] ℂ) :
    coefficient ψ 1 = ψ.toLinearMap := by
  ext a
  change inner ℂ (ψ.toPreGNS 1 : ψ.GNS)
    (ψ.gnsStarAlgHom a (cyclicVector ψ)) = ψ a
  rw [orbit_eq, UniformSpace.Completion.inner_coe]
  simp [PositiveLinearMap.preGNS_inner_def]

private theorem functional_dominated (ψ : A →ₚ[ℂ] ℂ) (T : ψ.GNS →L[ℂ] ψ.GNS)
    (hp : 0 ≤ T) (hu : T ≤ 1) (hc : ∀ a, Commute T (ψ.gnsStarAlgHom a)) :
    Dominated (functional ψ T hp hc) ψ := by
  have he := (coefficient_order_iff ψ T 1 hc (fun _ => Commute.one_left _)).mpr hu
  intro a ha
  change coefficient ψ T a ≤ ψ a
  simpa only [coefficient_one, PositiveLinearMap.coe_toLinearMap] using he a ha

private theorem coefficient_coordinate (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    coefficient ψ (coordinate φ ψ h) = φ.toLinearMap := by
  ext a
  exact (coordinate_represents φ ψ h a).symm

/-- Each dominated functional has exactly one positive commutant contraction coordinate. -/
theorem existsUnique_coordinate (φ ψ : A →ₚ[ℂ] ℂ) (h : Dominated φ ψ) :
    ∃! T : ψ.GNS →L[ℂ] ψ.GNS,
      0 ≤ T ∧ T ≤ 1 ∧ (∀ a, Commute T (ψ.gnsStarAlgHom a)) ∧
        coefficient ψ T = φ.toLinearMap := by
  have hm := coordinate_mem φ ψ h
  have he := coefficient_coordinate φ ψ h
  refine ⟨coordinate φ ψ h, ⟨hm.1, hm.2.1, hm.2.2, he⟩, ?_⟩
  intro S hS
  exact coefficient_injective ψ S _ hS.2.2.1 hm.2.2 (hS.2.2.2.trans he.symm)

/-- The actual dominated positive functionals; order is comparison on positive elements. -/
abbrev DominatedFunctional (ψ : A →ₚ[ℂ] ℂ) := {φ : A →ₚ[ℂ] ℂ // Dominated φ ψ}

private theorem dominated_antisymm (φ χ : A →ₚ[ℂ] ℂ)
    (h : Dominated φ χ) (h' : Dominated χ φ) : φ = χ := by
  have he : φ.toLinearMap = χ.toLinearMap :=
    LinearMap.ext_on CStarAlgebra.span_nonneg_inter_unitClosedBall
      (fun a ha => le_antisymm (h a ha.1) (h' a ha.1))
  exact DFunLike.ext _ _ fun a => congrArg (fun f : A →ₗ[ℂ] ℂ => f a) he

instance dominatedFunctionalPartialOrder (ψ : A →ₚ[ℂ] ℂ) :
    PartialOrder (DominatedFunctional ψ) where
  le φ χ := Dominated φ.val χ.val
  le_refl φ a _ := le_refl (φ.val a)
  le_trans φ χ η h h' a ha := (h a ha).trans (h' a ha)
  le_antisymm φ χ h h' := Subtype.ext (dominated_antisymm φ.val χ.val h h')

/-- The actual positive unit interval of the commutant of the GNS representation. -/
abbrev CommutantInterval (ψ : A →ₚ[ℂ] ℂ) :=
  {T : ψ.GNS →L[ℂ] ψ.GNS // 0 ≤ T ∧ T ≤ 1 ∧ ∀ a, Commute T (ψ.gnsStarAlgHom a)}

/-- Constructed order isomorphism, with the usual orders on both sides. -/
def orderCoordinates (ψ : A →ₚ[ℂ] ℂ) : DominatedFunctional ψ ≃o CommutantInterval ψ where
  toFun φ := ⟨coordinate φ.val ψ φ.property, coordinate_mem φ.val ψ φ.property⟩
  invFun T := ⟨functional ψ T.val T.property.1 T.property.2.2,
    functional_dominated ψ T.val T.property.1 T.property.2.1 T.property.2.2⟩
  left_inv φ := by
    apply Subtype.ext
    apply PositiveLinearMap.ext
    intro a
    exact (coordinate_represents φ.val ψ φ.property a).symm
  right_inv T := by
    apply Subtype.ext
    apply coefficient_injective ψ _ _
      (coordinate_mem _ ψ _).2.2 T.property.2.2
    exact coefficient_coordinate _ ψ _
  map_rel_iff' := by
    intro φ χ
    change coordinate φ.val ψ φ.property ≤ coordinate χ.val ψ χ.property ↔
      Dominated φ.val χ.val
    have he := coefficient_order_iff ψ (coordinate φ.val ψ φ.property)
      (coordinate χ.val ψ χ.property) (coordinate_mem _ ψ _).2.2
      (coordinate_mem _ ψ _).2.2
    simpa only [coefficient_coordinate, PositiveLinearMap.coe_toLinearMap, Dominated] using he.symm

/-- Convert the existing positive continuous dual input to Mathlib's positive-map GNS input. -/
def positiveOfDual (ρ : StrongDual ℂ A) (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ ρ.toLinearMap hρ

/-- Source-level specialization to the original two arbitrary positive dual functionals.
No individual faithfulness or nonzero premise is needed. -/
theorem original_pair_coordinate (ρ σ : StrongDual ℂ A)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a) :
    let ψ := positiveOfDual (ρ + σ) (fun a ha => add_nonneg (hρ a ha) (hσ a ha))
    ∃! C : ψ.GNS →L[ℂ] ψ.GNS,
      0 ≤ C ∧ C ≤ 1 ∧ (∀ a, Commute C (ψ.gnsStarAlgHom a)) ∧
        coefficient ψ C = ρ.toLinearMap ∧ coefficient ψ (1 - C) = σ.toLinearMap := by
  let ψ := positiveOfDual (ρ + σ) (fun a ha => add_nonneg (hρ a ha) (hσ a ha))
  have hd : Dominated (positiveOfDual ρ hρ) ψ := by
    intro a ha
    change ρ a ≤ ρ a + σ a
    exact le_add_of_nonneg_right (hσ a ha)
  obtain ⟨C, hC, hunique⟩ := existsUnique_coordinate (positiveOfDual ρ hρ) ψ hd
  refine ⟨C, ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2, ?_⟩, ?_⟩
  · ext a
    have hs : coefficient ψ (1 - C) a = coefficient ψ 1 a - coefficient ψ C a := by
      change inner ℂ (cyclicVector ψ) ((1 - C) (ψ.gnsStarAlgHom a (cyclicVector ψ))) =
        inner ℂ (cyclicVector ψ)
          ((1 : ψ.GNS →L[ℂ] ψ.GNS) (ψ.gnsStarAlgHom a (cyclicVector ψ))) -
        inner ℂ (cyclicVector ψ) (C (ψ.gnsStarAlgHom a (cyclicVector ψ)))
      rw [sub_apply, inner_sub_right]
    rw [hs, coefficient_one, hC.2.2.2]
    change (ρ a + σ a) - ρ a = σ a
    exact add_sub_cancel_left (ρ a) (σ a)
  · intro S hS
    exact hunique S ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1⟩

#print axioms comparison_norm_le
#print axioms comparison_intertwines
#print axioms comparison_adjoint_intertwines
#print axioms coordinate_mem
#print axioms coordinate_represents
#print axioms coefficient_injective
#print axioms coefficient_nonneg_iff
#print axioms coefficient_order_iff
#print axioms existsUnique_coordinate
#print axioms orderCoordinates
#print axioms original_pair_coordinate

end D5.S3.Quantum.Analysis.GNSOrderCoordinates
