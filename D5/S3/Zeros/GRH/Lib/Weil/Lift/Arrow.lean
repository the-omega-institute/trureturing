/- GID: D5/S3/Zeros/GRH/Lib/Weil/Lift/Arrow
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Lift/Arrow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Lift.Arrow. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Lift/Arrow.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.DatumLevel
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Edge
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Joint harmonics and global theta lifts between discrete series types (known result; see
Lib.Weil.Lift.Edge).

This file: Theta lift on forms: equivariance, adjoint, matched real data lift types to types. -/

noncomputable section


open ComplexConjugate Space InnerProductSpace Submodule LinearMap
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {s t X} [NormedAddCommGroup X]
  [NormedSpace ℂ X] [CompleteSpace X] {S : Space E n s} {T : Space E n' t} (K : ThetaKernel X S T)
  (e e') {φ φ'}

/-- A chosen bilinear map (φ, y) ↦ L_φ y to forms of type e' on T, equal to `Space.lift`
when y is rapid and its lift is such a form. -/
def formLift : X →ₗ[ℂ] S.Form e →ₗ[ℂ] T.Form e' := (K.liftBilin.compl₂
  (S.rapidFunctions.1.subtype.leftInverse ∘ₗ Submodule.subtype _)).compr₂ (Submodule.subtype
  _).leftInverse

/-- For the kernel K, the datum φ is an arrow e → e': forms of type e on S are rapid, and their
lifts by φ are forms of type e' on T. -/
def IsArrow φ := ∀ y : S.Form e, ↑y ∈ S.rapidFunctions ∧ T.IsForm e' (lift K φ y)

variable {K e e'}

/-- Complex conjugation F ↦ conj(F), as a conjugate-linear map from forms of type e to forms of
type e', when e' is the conjugate of e. -/
def conjForm (h : e' = star e) : S.Form e →ₗ⋆[ℂ] S.Form e' :=
  (starLinearEquiv _).1.restrict fun _ ↦ h ▸ .conj

@[simp] lemma coe_conjForm h (y : S.Form e) : (conjForm h y : S.Form e') = (conj <| y ·) := rfl

/-- Let Φ be an edge e → e' for the real Weil representation of weights γ, γ', a, b characters
of these weights, and f ∈ 𝒲_f. Then for ω_{a,b}, Φ ⊗ f is an arrow e → e' and, for the
swapped pair, ē' → ē.

Known result: Joint harmonics and global theta lifts between discrete series types. -/
lemma IsEdge.isArrow [WeilData E] {γ γ' Φ ψ ψ' f} (h : IsEdge (realPairWeil γ γ') e e' Φ) (a b :
  AutChar E) [a.HasWeight γ ψ] [b.HasWeight γ' ψ'] (hf : f ∈ (S.hom T).finitePart) :
  IsArrow (pairThetaKer S T a b) e e' (integrated _ Φ f) ∧ IsArrow (pairThetaKer S T a b).swap
  (star e') (star e) (integrated _ Φ f) := (exists_level_pairWeil a b hf).elim fun K ⟨L,
  _⟩ ↦ by use fun y ↦ ⟨y.2.mem_rapidFunctions h.isCuspKernel_source,
  ((h.lift_isForm_and_eq_realConv _ ⟨0, rfl⟩).choose_spec _ ?_ y.2).1 L ?_⟩, fun y ↦
  ⟨y.2.mem_rapidFunctions h.2.1, ((h.2.3 _ ⟨0, rfl⟩).choose_spec _ ?_ y.2).1 K ?_⟩ <;>
  simp_all [lift_mul_right, ← Prod.mk_one_one, pairWeil_integrated]

namespace IsArrow

variable (h : IsArrow K e e' φ) {ε ε'} (h' : IsArrow K.swap ε' ε φ)
include h

lemma eq_formLift_of_coe_eq {y} z (a : z.1 = lift K φ' y.1) : z = formLift K e e' φ' y :=
  have l := @leftInverse_apply_of_inj; l (ker_subtype _) z ▸
  congrArg _ (a.trans congr(K.liftBilin φ' $(l (by simp) ⟨_, (h y).1⟩)).symm)

attribute [irreducible] formLift

/-- If φ is an arrow e → e' from S to T, then for every form y of type e on S, `formLift` of φ
and y equals, as a function, the theta lift `Space.lift` of y. -/
lemma coe_formLift y : formLift K e e' φ y = lift K φ y :=
  h.eq_formLift_of_coe_eq ⟨_, (h _).2⟩ rfl ▸ rfl

/-- If φ is an arrow e → e', then for k, k' in the finite groups of S, T and a form y of type e,
the right translate by k' of L_φ y equals L_{ω(k,k')φ} applied to the translate of y by k. -/
lemma formRep_formLift k k' y : T.formRep _ k' (formLift K e _ φ y) =
  formLift K e e' (K.ω ((1, k), 1, k') φ) (S.formRep e k y) :=
  h.eq_formLift_of_coe_eq _ (h.coe_formLift y ▸ funext (K.lift_equivariant y.2.1 _ _ _) :)

lemma formRep_formLift_of_eq_smul {k k'} {c : ℂ} (H : K.ω ((1, k), 1, k') φ = c • φ') y :
  T.formRep _ k' (formLift K e _ φ y) =
  c • formLift K e e' φ' (S.formRep e k y) := by simp [h.formRep_formLift k, *]

include h'

/-- Lift and descent are transposes: if φ is an arrow e → e' and, for the swapped pair, an arrow
ε' → ε, then ∫_{[T]} z·L_φ y = ∫_{[S]} y·D_φ z for forms y of type e and z of type ε'. -/
lemma integral_mul_formLift_swap y z : ∫ g, z g * formLift K e e' φ y g ∂T.quotMeasure = ∫ g,
  y g * formLift K.swap ε' ε φ z g ∂S.quotMeasure :=
  by simp [coe_formLift, K.integral_lift_eq_integral_descent, h _, h' _, *]

/-- If φ is an arrow e → e' and, for the swapped pair, an arrow between the conjugate types,
then ⟨x, L_φ y⟩ = ⟨conj(D_φ conj(x)), y⟩: the adjoint of the lift is the conjugate of the
descent. -/
lemma inner_formLift_adjoint b b' x y : ⟪formLift K e e' φ y, x⟫_ℂ = ⟪y,
  conjForm b' (formLift K.swap ε' ε φ (conjForm b x))⟫_ℂ := star_inj.1 (by simp [inner, petersson,
  ← integral_conj, mul_comm, ← h.integral_mul_formLift_swap h'])
