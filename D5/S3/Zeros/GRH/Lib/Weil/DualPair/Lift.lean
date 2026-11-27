/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/Lift
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/Lift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.Lift. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/Lift.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.Petersson
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: Moderate growth of theta kernels; lifts converge, are equivariant, adjoint to
descents. -/

noncomputable section

attribute [-instance] Prod.isMulCommutative CommMonoid.toCommSemigroup


open MeasureTheory Space
variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [Fintype n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {X : Type _} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {S : Space E n s}
  {T : Space E n' t} {φ : X} {y : G E s → ℂ} {y' : G E t → ℂ} (K : ThetaKernel X S T)
  (hr : y ∈ S.rapidFunctions)

/-- The theta lift from S with datum φ: the function h ↦ ∫_{[S]} θ(ω(g, h)φ) y(g) dg on the
group of the second space. -/
def Space.lift φ (y : _ → ℂ) h := ∫ g, K.θ (K.ω (g, h) φ) * y g ∂S.quotMeasure

variable (S T) in
/-- A continuous function M of moderate growth on the adelic group of S, and a continuous map j
to that of T with ht(j g) ≤ C·ht(g) for some C. -/
structure Space.ModerateWeight where
  (weightFn : C(G E s, ℂ)) (groupMap : C(G E s, G E t)) isModerate : S.IsModerate weightFn
  height_le : ∃ C, ∀ g, T.height (groupMap g) ≤ S.height g * C

attribute [local simp] lift mul_pow rep_apply_apply le_of_lt
attribute [local simp ←] integral_const_mul mul_assoc

omit [CompleteSpace X] in
lemma lift_mul_right h k : lift K φ y (h * k) = lift K (K.ω (1, k) φ) y h := by simp

namespace ThetaKernel

/-- The theta kernel for (T, S) obtained from K by exchanging the two groups: the representation
(h, g) ↦ ω(g, h) with the same functional θ. -/
@[simps] abbrev swap : ThetaKernel X T S :=
  ⟨K.ω.comp MulEquiv.prodComm.toMonoidHom, K.θ, by simp; fun_prop, by simp_all [K.4]⟩

omit [CompleteSpace X] in
lemma theta_rat_mul {h} : ∀ γ ∈ S.Γ, ∀ g, K.θ (K.ω (γ * g, h) φ) = K.θ (K.ω (g, h) φ) := by
  grind [K.4, one_mul h, one_mem]

omit [CompleteSpace X] in
lemma isAutomorphic (L : OpenSubgroup _) (a : ∀ k ∈ L, K.ω ((1, k), 1) φ = φ) h : S.IsAutomorphic
  (K.θ <| K.ω ⟨·, h⟩ φ) := ⟨by fun_prop, K.theta_rat_mul, L, (by nth_rw 2 [← a · ·]; simp)⟩

/-- Moderate growth of a theta kernel for S, T on a Banach space X: there are a real C and a
natural number A with |θ(ω(g, h)φ)| ≤ C‖φ‖(ht(g)·ht(h))^A for all g, h and all φ in X.

Known result: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay. -/
lemma moderate_growth : ∃ C A, ∀ g h φ, ‖K.θ (K.ω (g, h) φ)‖ ≤
  C * ‖φ‖ * (S.height g * T.height h) ^ A := by
  choose A a _ _ b using
    ((K.swap.exists_rat_norm_le_height 1).and (K.exists_rat_norm_le_height 1)).exists
  choose _ _ a using a
  exact ⟨_ * (2 * 2) ^ A, _, fun g h φ ↦ by simpa [*, mul_right_comm, K.4] using
    (K.θ.le_opNorm_of_le ((_ ∘L _).le_of_opNorm_le (norm_mul_le_of_le (a g) (b h)) φ))⟩

lemma isModerate φ h : S.IsModerate (K.θ <| K.ω ⟨·, h⟩ φ) :=
  ⟨_, _, (by simpa using K.swap.moderate_growth.choose_spec.choose_spec h · φ)⟩

section

omit [CompleteSpace X]

lemma fixesLeft_lift : T.Γ.FixesLeft (lift K φ y) := fun _ ↦ (by simp [← K.4 (one_mem _) · _ ·])

lemma lift_equivariant (hy : S.IsAutomorphic y) φ k l h : lift K φ y (h * l) =
  lift K (K.ω (k, l) φ) (y <| · * k) h
  := by cases hy; simpa using (integral_comp_mul_right k (by grind [theta_rat_mul])).1.symm

lemma lift_omega_left (hy : S.IsAutomorphic y) k : lift K (K.ω (k, 1) φ) y =
  lift K φ (y <| · * k⁻¹) := funext (by simpa using K.lift_equivariant hy (K.ω (k, 1) φ) k⁻¹ 1)

end

include hr

lemma exists_norm_theta_mul_le : ∃ C A, ∀ φ g h, ‖K.θ (K.ω (g, h) φ) * y g‖ ≤
  T.height h ^ A * |C| * ‖φ‖ := have ⟨C, A, H⟩ := K.moderate_growth; (hr.2 A).elim (⟨|C| * ·, A, by
  introv; grw [norm_mul, H, le_abs_self C, ← le_abs_self, ← ·] <;> simp [field]⟩)

lemma integrable_theta_mul φ h : Integrable (fun g ↦ K.θ (K.ω (g, h) φ) * y g) S.quotMeasure :=
  (hr.2.mul (isModerate ..)).integrable (hr.1.rec (by fun_prop))

/-- The theta lift (φ, y) ↦ `Space.lift` K φ y as a ℂ-bilinear map from X and rapidly
decaying automorphic functions for S to functions on the group of T. -/
def liftBilin : X →ₗ[ℂ] S.rapidFunctions.1 →ₗ[ℂ] G E t → ℂ := by
  refine' .mk₂ ℂ (lift K · ·) .. <;> simp [add_mul, funext_iff, mul_add, integral_add,
    integrable_theta_mul]
  ac_nf; simp

/-- For y automorphic of rapid decay for S and each h in the group of T, the value at h of the
theta lift of y is a continuous linear functional of the datum φ. -/
lemma exists_clm_lift : ∃ L : _ → X →L[ℂ] ℂ, ∀ φ h, lift K φ y h = L h φ := ⟨(strongIntegral
  S.quotMeasure fun g ↦ y g • K.θ ∘L K.ω ⟨g, ·⟩), by simp [strongIntegral_apply, mul_comm (y _),
  integrable_theta_mul, *]⟩

/-- Let y and F be automorphic of rapid decay for S and U, and w = (M, j) a `Space.ModerateWeight`
from U to T. Then (u, g) ↦ M(u)F(u)θ(ω(g, j u)φ)y(g) is integrable for the product of the
quotient measures. -/
lemma integrable_prod_weightFn {m} [Fintype m] {u F} {U : Space E m u} (w : U.ModerateWeight T) (r :
  F ∈ U.rapidFunctions) φ : Integrable (fun p ↦ (⇑w.weightFn * F) p.1 *
  (K.θ ((K.ω (p.2, w.groupMap p.1)) φ) * y p.2)) (U.quotMeasure.prod S.quotMeasure) := .of_bound
  (hr.1.rec (r.1.rec (by fun_prop))) _ (.of_forall (by
  grw [norm_mul, (K.exists_norm_theta_mul_le hr).choose_spec.choose_spec, w.4.choose_spec ·.1,
    le_abs_self (_ ^ _)] <;> simp [-Pi.mul_apply, abs_of_pos]; grw [(r.2.mul w.3 _).choose_spec]))

/-- The theta lifts in the two directions are transposes: for y, y' automorphic of rapid decay
for S, T, ∫_{[T]} y'·(lift of y by φ) = ∫_{[S]} y·(lift of y' by φ along the swapped
kernel). -/
lemma integral_lift_eq_integral_descent (hr' : y' ∈ T.rapidFunctions) :
    ∫ h, y' h * lift K φ y h ∂T.quotMeasure = ∫ g, y g * lift K.swap φ y' g ∂S.quotMeasure := by
  simp; rw [integral_integral_swap]; ac_rfl
  simpa using! K.integrable_prod_weightFn hr ⟨1, .id _, ⟨1, 0, by simp⟩, 1, by simp⟩ hr' φ
