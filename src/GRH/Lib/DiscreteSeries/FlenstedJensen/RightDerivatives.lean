import GRH.Lib.DiscreteSeries.FlenstedJensen.RepresentationDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series (known
result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Smooth functions on U(p,q) as gl_n-module by right derivatives; chain rule. -/

noncomputable section


open Complex Matrix NormedSpace Topology U Norms.L2Operator VectorField ContDiff Ring Module

section

variable {n} [Fintype.{0} n] {ε : n → ℤˣ} {J X : Matrix n n ℂ} {E M : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M] (ρ : GlModule n M)

variable (n E) in
def SmoothMat : Submodule ℂ (Matrix n n ℂ → E) := by
  use! {f | ContDiff ℝ ∞ f}, (·.out.add), contDiff_const (n := ∞); simp; fun_prop

lemma SmoothMat.differentiable (f : SmoothMat n E) : Differentiable ℝ f.1 :=
  ContDiff.differentiable (n := ∞) f.2 nofun

open SmoothMat IsHermInvolution ContinuousLinearMap

@[simp] lemma expU_zero : expU 0 = (1 : U J) := by aesop

@[fun_prop] lemma U.continuous_mat : Continuous (·.1.1 : U J → _) := by fun_prop

@[fun_prop] lemma continuous_expU [IsHermInvolution J] : Continuous (expU (J := J)) :=
  continuous_U_iff_matrix.2 ((@exp_continuous _ _ (.restrictScalars ℚ ℂ _) _).comp (by fun_prop))

lemma hasDerivAt_expU (Y : unitaryLie J) g t : let γ (t : ℝ) := (g * expU (t • Y)).1.1
        HasDerivAt γ (γ t * Y) t := by simp [mul_assoc, (hasDerivAt_exp_smul_const ..).const_mul]

variable (ε X E)

-- Smooth functions on `U(p,q)`.
/-- The space of smooth E-valued functions on U(J) for J=diag(ε), ε a vector of signs. -/
abbrev SmoothU := (.funLeft ℂ E (·.1.1 : USign ε → _) ∘ₗ (SmoothMat ..).subtype).range

attribute [local simp] mul_add add_mul det_ne_zero mul_sub sub_mul mul_assoc
attribute [local instance] LieRing.ofAssociativeRing

/-- For a linear map ι whose kernel is stable under ρ, a gl_n(ℂ)-module structure on the range
of ι, together with the proof that ι is equivariant. -/
@[irreducible] def GlModule.onRange {N} [AddCommGroup N] [Module ℂ N] (ι : M →ₗ[ℂ] N) (h : ∀ X x, ι
  x = 0 → ι (ρ X x) = 0) : {σ : GlModule n _ // ∀ X x, σ X (ι.rangeRestrict x) = ι.rangeRestrict (ρ
  X x)} := by use! fun X ↦
  ι.quotKerEquivRange.conj (ι.ker.mapQ _ _ (h X)) <;> aesop (add simp [map_bracket,
  DFunLike.ext_iff, LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image])

/-- For signs ε, J = diag(ε) and a complex matrix X, the element ½(X − J⁻¹X*J) of the Lie
algebra of U(J). -/
def unitaryLiePart : unitaryLie (signMatrix ε) := ⟨(2⁻¹ : ℝ) • (X - (signMatrix ε)⁻¹ * Xᴴ *
  signMatrix ε), by simp [unitaryLie, isHermitian.inv.eq, isHermitian.eq]⟩

lemma eq_unitaryLiePart_add_I_smul X : X =
  unitaryLiePart ε X + I • unitaryLiePart ε (-I • X) := by ext; simp [unitaryLiePart]; grind [I_sq]

/-- The gl_n(ℂ)-module of smooth E-valued functions on all matrices: Y in the Lie algebra of
U(diag ε) differentiates along the field x ↦ xY, extended complex linearly. -/
def rightDerivMat : GlModule n (SmoothMat n E) := let r X : End ℂ (SmoothMat n E) := (by
    use! fun f ↦ ⟨_, (contDiff_infty_iff_fderiv.1 f.2).2.clm_apply ((mul ℝ _).flip
    (unitaryLiePart ε X).1).contDiff⟩ <;> aesop (add simp [fderiv_add, fderiv_const_smul,
      (SmoothMat.differentiable _ _)])); by
    refine ⟨⟨⟨fun X ↦ r X + I • r (-I • X), ?_⟩, fun ⟨_, _⟩ ↦ ?_⟩, fun _ _ ↦ .trans ?_ (lie_def ..)⟩
    all_goals intros; ext f; simp +decide [r, lieBracket, -flip_apply, ← fderiv_apply_lieBracket
      (contDiffAt (n := ∞) f.2)]; simp [unitaryLiePart, mk_eq_add_mul_I, add_smul, smul_sub,
      mul_smul, smul_smul I, @smul_comm ℂ]; module

/-- The gl_n(ℂ)-module of smooth E-valued functions on U(diag ε) under complexified right
derivatives. -/
def rightDeriv : GlModule n (SmoothU ε E) := ((rightDerivMat ε E).onRange _ fun X f h ↦
  funext fun g ↦ by have k Y := ((SmoothMat.differentiable f _).hasFDerivAt.comp_hasDerivAt _
  (hasDerivAt_expU Y g 0)).deriv.symm.trans congr(deriv ($h ∘ _) _); simp_all [rightDerivMat]).1

variable {ε X E}

@[fun_prop] lemma SmoothU.continuous : ∀ f : SmoothU ε E, Continuous f.1
  | ⟨_, F, rfl⟩ => (SmoothMat.differentiable F).continuous.comp continuous_mat

/-- Chain rule along a curve γ in U(J): if γ'(t) = γ(t)X, then for smooth f the derivative of f
∘ γ at t is the right derivative of f along X at γ(t). -/
lemma hasDerivAt_curve f {γ : ℝ → USign ε} {t} (h : HasDerivAt (γ · |>.1.1) ((γ t).1 * X) t) :
    HasDerivAt (f.1 <| γ ·) ((rightDeriv ε E X f).1 (γ t)) t := have ⟨_, F, rfl⟩ := f
  ((SmoothMat.differentiable ..).hasFDerivAt.comp_hasDerivAt t h).congr_deriv (by
    erw [(GlModule.onRange ..).2]; simp [rightDerivMat, unitaryLiePart,
      ← two_smul ℝ, by simpa [logDerivU, h.deriv,
      ← mul_assoc, mem_U.1, isHermitian.eq] using (conjTranspose_logDerivU h.differentiableAt 1)])

lemma hasDerivAt_rightDeriv_expU f g Y t : let γ (t : ℝ) := g * expU (t • Y)
  HasDerivAt (f.1 <| γ ·) ((rightDeriv ε E Y f).1 (γ t)) t :=
  hasDerivAt_curve f (hasDerivAt_expU ..)

lemma rightDeriv_eq_fderiv {f F g} {D : _ →L[ℂ] _} (hF : HasFDerivAt F D g.1.1) (h : ∀ g, F g.1.1 =
  f.1 g) X : (rightDeriv ε E X f).1 g = D (g * X) := eq_unitaryLiePart_add_I_smul ε X ▸ have k Y :=
    ((funext h ▸ hasDerivAt_rightDeriv_expU ..).unique
    ((hF.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 (hasDerivAt_expU Y g _) (by simp))); by aesop

lemma rightDeriv_comp_clm {f f' g} (L : E →L[ℂ] ℂ) (h : f'.1 =ᶠ[𝓝 g] L ∘ f.1) :
  (rightDeriv ε ℂ X f').1 =ᶠ[𝓝 g] L ∘ (rightDeriv ε E X f).1 :=
  h.eventually_nhds.mono fun y h ↦ have k Y := ((hasDerivAt_rightDeriv_expU ..).unique
    (((hasDerivAt_rightDeriv_expU f y Y 0).map_clm L).congr_of_eventuallyEq (Continuous.tendsto'
    (by fun_prop) 0 y (by simp) h))); eq_unitaryLiePart_add_I_smul ε X ▸ by simp_all

lemma one_le_cast_card n [Fintype n] [Nonempty n] : (1 : ℝ) ≤
  Fintype.card n := mod_cast NeZero.one_le
