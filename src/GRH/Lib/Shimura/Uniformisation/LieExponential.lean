import GRH.Lib.General.Analysis.HolomorphicIntegral
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Theta functions on complex tori, Riemann form, semicharacters, Heisenberg translations,
basic API. Exponential map of a compact commutative complex Lie group has lattice kernel. -/

noncomputable section

section


open Complex LinearMap Submodule FourierTransform

open scoped Real

instance : SMulCommClass ℂ ℝ ℂ := inferInstance

instance : ContinuousAdd ℂ := inferInstance

/-- The standard additive character of the reals, as a complex exponential. -/
@[simp] lemma coe_fourierChar_eq_exp t : 𝐞 t = exp (2 * π * I * t) := by
  simp [Real.fourierChar_apply, mul_right_comm]

/-- A finite-dimensional complex normed space. -/
class FinComplexSpace V extends NormedAddCommGroup V, NormedSpace ℂ V, Module.Finite ℂ V

attribute [instance 100] FinComplexSpace.toNormedAddCommGroup FinComplexSpace.toNormedSpace

instance : FinComplexSpace ℂ where

instance {ι V} [Fintype ι] [FinComplexSpace V] : FinComplexSpace (ι → V) where

/-- The continuous complex-valued forms B(u, v) on V that are real-linear in u and
complex-linear in v. -/
abbrev RealComplexForm V [FinComplexSpace V] := V →L[ℝ] V →L[ℂ] ℂ

variable {V V'} [FinComplexSpace V] [FinComplexSpace V'] (L : Submodule ℤ V)

instance : FinComplexSpace (V × V') where

/-- A lattice of full rank. -/
class abbrev IsFullRankLattice := DiscreteTopology L, IsZLattice ℝ L

variable {L} (φ : V' →L[ℂ] V) (B : RealComplexForm V) (χ : V → ℂ) (u v : V)

/-- The type `RealComplexForm` V of forms on V, tagged with a subgroup L of V (the lattice) that
`RealComplexForm.thetaSpace` and `RealComplexForm.dualLattice` read from the type; no condition is
imposed. -/
abbrev LatticeForm (_ : Submodule ℤ V) := RealComplexForm V

/-- The pull-back (u, v) ↦ B(φu, φv) of B along a continuous complex-linear map φ from V' to V. -/
@[simps! apply_apply] def RealComplexForm.pullForm :=
  (φ.precomp ℂ).restrictScalars ℝ ∘L B ∘L φ.restrictScalars ℝ

/-- The complex vector space of entire functions f on V with f(z + l) = χ(l)·exp(B(l, z) + B(l,
l)/2)·f(z) for all l in L and all z. -/
def RealComplexForm.thetaSpace (B : LatticeForm L) :=
  ofLinearComb (R := ℂ) {f | Differentiable ℂ f ∧ ∀ l ∈ L, ∀ z, f (z +
  l) = χ l * (B l z + B l l / 2).exp * f z} ⟨0, by simp⟩ (by simp +contextual [field]; fun_prop)

/-- The Riemann form of B: the real bilinear form (u, v) ↦ Im(B(u, v) − B(v, u))/(2π) on V, as
an additive map in B. -/
def RealComplexForm.riemannForm : RealComplexForm V →+ LinearMap.BilinForm ℝ V := .mk' (fun B ↦ by
  apply mk₂ ℝ fun u v ↦ (B u v - B v u).im / (2 * π) <;> simp <;> grind) (by simp [ext_iff₂]; grind)

/-- The complex number exp(2πi E(u, v)) of modulus one, where E is the Riemann form
`RealComplexForm.riemannForm` of B. -/
abbrev RealComplexForm.riemannPhase : ℂ := 𝐞 (B.riemannForm u v)

lemma riemannForm_def : B.riemannForm u v = (B u v - B v u).im / (2 * π) := rfl

/-- Appell–Humbert data: Re B is symmetric, and on L one has |χ| = 1 and χ(l + m) =
χ(l)χ(m)·exp(πi E(m, l)), E the Riemann form of B. -/
@[mk_iff] class IsAppellHumbert (B : LatticeForm L) (χ : V → ℂ) where
  re_symm u v : (B u v).re = (B v u).re
  norm_eq_one : ∀ l ∈ L, ‖χ l‖ = 1
  semicharacter : ∀ᵉ (l ∈ L) (m ∈ L), χ (l + m) = χ l * χ m * exp (π * I * B.riemannForm m l)

/-- The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0. -/
@[mk_iff pr_iff] class IsPosRiemann where riemannForm_pos : ∀ u ≠ 0, 0 < B.riemannForm u (I • u)

/-- Twisted translation by a: the complex-linear map sending a function f on V to z ↦ exp(−B(a,
z) − B(a, a)/2)·f(z + a). -/
@[simps! -isSimp apply] def RealComplexForm.thetaShift a := (fun z ↦
  (-(B a z + B a a / 2)).exp) • funLeft ℂ ℂ (· + a)

/-- The dual of L for the Riemann form E of B: the subgroup of all v in V with E(v, l) an
integer for every l in L. -/
def RealComplexForm.dualLattice (B : LatticeForm L) := (B.riemannForm.dualSubmodule L).copy
  {v | ∀ l ∈ L, ∃ n : ℤ, B.riemannForm v l = n} (by simp [BilinForm.dualSubmodule, eq_comm])

export RealComplexForm
  (pullForm pullForm_apply_apply riemannForm thetaShift thetaShift_apply thetaSpace)

attribute [local simp] isAppellHumbert_iff exp_add exp_neg mul_add mul_pow ofLinearComb
  exp_eq_one_iff thetaSpace mul_div Real.pi_pos add_div pr_iff exp_sub funext_iff fieldEq
  riemannForm add_right_comm thetaShift_apply

attribute [local simp ←] exp_nsmul zsmul_eq_mul'

@[fun_prop] lemma differentiable_of_symm (s : ∀ u v, B u v = B v u) : Differentiable ℂ B :=
  { B with map_smul' := by aesop }.differentiable

@[fun_prop, local simp] lemma differentiable_thetaShift {f} : Differentiable ℂ f →
    Differentiable ℂ (B.thetaShift u f) := (.mul (by fun_prop) <| ·.comp (by simp))

lemma riemannForm_pullForm u v : riemannForm (B.pullForm φ) u v = B.riemannForm (φ u) (φ v) := rfl

variable {B B' f g} (n : ℕ)

lemma riemannForm_swap : B.riemannForm v u = -B.riemannForm u v := by simp

@[simp] lemma riemannForm_self : B.riemannForm u u = 0 := by simp

lemma eq_zero_of_exp_eq_one {W} [AddCommGroup W] [Module ℝ W] (φ : W →ₗ[ℝ] ℝ) : (∀ x,
  (𝐞 (φ x)).1 = 1) → φ = 0 := by grind [(φ.surjective · 2⁻¹).mt, coe_fourierChar_eq_exp,
  exp_pi_mul_I, ofReal_inv, ofReal_ofNat 2]

@[simp] lemma thetaShift_zero : B.thetaShift 0 f = f := by simp

@[simp] lemma thetaShift_mul : (B + B').thetaShift u (f * g) =
  B.thetaShift u f * B'.thetaShift u g := by simp

@[simp] lemma thetaShift_pow : (n • B).thetaShift u (f ^ n) = B.thetaShift u f ^ n := by simp

lemma isPosRiemann_of_re_pos (h : ∀ u ≠ 0, 0 < (B u u).re) : IsPosRiemann B := by
  have := (h <| I • ·); simp_all; grind

lemma IsPosRiemann.nsmul (h : IsPosRiemann B) {n} : n ≠ 0 →
  IsPosRiemann (n • B) := by simp_all [zero_lt_iff]

instance [h : IsPosRiemann B] [NeZero n] : IsPosRiemann (n • B) := h.nsmul NeZero.out

variable {B B' : LatticeForm L} {χ χ' l m a} [hB : IsAppellHumbert B χ] (ha :
  a ∈ B.dualLattice) (hf : f ∈ B.thetaSpace χ)

/-- The term exp(B(x, y − x + l) − B(l,y) − B(l,l)/2)/χ(l) of the Poincaré series at (x, y), for
l in L. -/
def IsAppellHumbert.poincareTerm (_ : IsAppellHumbert B χ) x y (l : L) :=
  (B x (y - x + l) - B l y - B l l / 2).exp / χ l

/-- The Poincaré series K(x, y) = ∑_{l ∈ L} exp(B(x, y − x + l) − B(l,y) − B(l,l)/2)/χ(l) of
Appell–Humbert data (B, χ). -/
def IsAppellHumbert.poincareSeries x y := tsum (hB.poincareTerm x y)

lemma mem_dualLattice_nsmul : a ∈ ((m : ℕ) • B).dualLattice ↔ m • a ∈ B.dualLattice :=
  forall_congr' (by simp)

include hB

attribute [-simp] riemannForm ofReal_div

lemma IsAppellHumbert.sub_eq_riemannForm :
  B u v - B v u = 2 * π * I * B.riemannForm u v := by simp_all [Complex.ext_iff, riemannForm]

lemma IsAppellHumbert.thetaShift_thetaShift u v : B.thetaShift u (B.thetaShift v f) = exp (π * I *
  B.riemannForm u v) • B.thetaShift (u + v) f := by simp [← exp_add]; grind [sub_eq_riemannForm]

lemma IsAppellHumbert.add : IsAppellHumbert B' χ' → IsAppellHumbert (B + B') (χ * χ') := by aesop

lemma IsAppellHumbert.neg : IsAppellHumbert (-B) χ⁻¹ := by aesop

instance IsAppellHumbert.nsmul : IsAppellHumbert (n • B) (χ ^ n) := by simp_all [mul_left_comm]

instance IsAppellHumbert.shift a (C : RealComplexForm V := B) : IsAppellHumbert B fun l ↦
  χ l * C.riemannPhase l a := by simp_all

lemma IsAppellHumbert.thetaShift_comm u v : B.thetaShift u (B.thetaShift v f) =
    B.riemannPhase u v • B.thetaShift v (B.thetaShift u f) := by simp [← hB.sub_eq_riemannForm]

lemma IsAppellHumbert.ne_zero : l ∈ L → χ l ≠ 0 := by grind [IsAppellHumbert, norm_zero]

lemma IsAppellHumbert.le_dualLattice : L ≤ B.dualLattice := fun l _ _
  _ ↦ by
  have := hB.3 l; have := @hB.ne_zero; simp_all [riemannForm_swap l, add_comm l, ← ofReal_intCast]

lemma IsAppellHumbert.exp_riemannForm_pow_eq_one {n m b} : n • a ∈ L → m • b ∈ L →
  exp (π * I * B.riemannForm a b) ^ (2 * n * m) = 1 :=
  (by simpa [← @ofReal_inj (_ * _)] using hB.le_dualLattice · _ ·)

lemma IsAppellHumbert.of_riemannForm_eq (h : IsAppellHumbert B' χ') (e : B.riemannForm =
  B'.riemannForm) (k : ∀ l ∈ L, χ l = χ' l) : f ∈
  B.thetaSpace χ → (fun z ↦ ((B' z z - B z z) / 2).exp * f z) ∈ B'.thetaSpace χ' := by
  apply And.imp (((differentiable_of_symm (B' - B) _).clm_apply _).mul_const _).cexp.mul <;> intros
    <;> simp [← exp_add, ← mul_rotate (exp _), *] <;> grind [sub_eq_riemannForm]

include hf

omit hB in lemma thetaShift_of_mem : l ∈ L → B.thetaShift l f = χ l • f := by aesop

lemma IsAppellHumbert.thetaShift_add_mem u : l ∈ L → B.thetaShift (u + l) f =
  (exp (-(π * I * B.riemannForm u l)) * χ l) • B.thetaShift u f := by simp_all [mul_smul,
  ← map_smul (B.thetaShift u), ← thetaShift_of_mem hf, hB.thetaShift_thetaShift]

lemma IsAppellHumbert.thetaShift_mem a : B.thetaShift a f ∈ B.thetaSpace fun l ↦
  χ l * B.riemannPhase l a := by simp_all [← hB.sub_eq_riemannForm]

include ha in lemma IsAppellHumbert.thetaShift_mem_of_dual : B.thetaShift a f ∈ B.thetaSpace χ :=
  (thetaShift_mem hf a).imp_right (forall₂_imp (ha · · |>.rec (by simp_all [riemannForm_swap a])))

/-- For Appell–Humbert data and a in the dual lattice of L, the twisted translation `thetaShift` by
a, as an endomorphism of the theta functions of type (B, χ). -/
abbrev IsAppellHumbert.thetaShiftEnd (a : B.dualLattice) := (B.thetaShift a).restrict fun _ ↦
  hB.thetaShift_mem_of_dual a.2

omit hB

lemma thetaSpace.mul : g ∈ B'.thetaSpace χ' → f * g ∈ (B + B').thetaSpace (χ * χ') := by aesop

lemma thetaSpace.pow n : f ^ n ∈ (n • B).thetaSpace (χ ^ n) := by aesop

end

open Filter Topology Submodule AddSubgroup tangentConeAt Ultrafilter

/-- Exponential map: a compact abelian group G with a chart at 0 in V in which addition is
analytic has a homomorphism e : V → G, analytic at 0 with derivative 1, image of finite
index, kernel a lattice; homomorphisms from complex spaces, continuous and differentiable at
0, factor linearly through e. -/
lemma exists_lie_exponential {G V} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [FinComplexSpace V] {φ ψ} (h0 : φ 0 = 0) (hs : ∀ᶠ x in 𝓝 0, ψ (φ x) =
  x) (hc : ∀ᶠ x in 𝓝 0, ContinuousAt φ x) (H : φ ∘ ψ =ᶠ[𝓝 0] id) (hg : ContinuousAt ψ 0) (hφ :
  AnalyticAt ℂ (fun p : V × V ↦ φ (ψ p.1 + ψ p.2)) 0) : ∃ e : V →+ G,
  IsFullRankLattice e.ker.toIntSubmodule ∧ ψ ∘ φ ∘ e =ᶠ[𝓝 0] e ∧ AnalyticAt ℂ (φ ∘ e) 0 ∧
  HasFDerivAt (φ ∘ e) (.id ℂ V) 0 ∧ e.range.FiniteIndex ∧ ∀ {P} [FinComplexSpace P] (γ : P →+ G),
  ContinuousAt γ 0 → DifferentiableAt ℂ (φ ∘ γ) 0 → ∃ F : P →L[ℂ] V, ∀ z, e (F z) = γ z := by
  obtain ⟨o, u, C, _, c, s⟩ := h0 ▸ hs.self_of_nhds, tendsto_norm_atTop_atTop.comp
    (tendsto_natCast_atTop_iff.2 (of_le _)), exists_mem_nhds_isClosed_subset (hs.and hc)
  obtain ⟨hψ, E⟩ := hg.fst'.fun_add hg.snd' (by aesop : C ∈ _), hφ.hasStrictFDerivAt.congr_fderiv
    (g' := .coprod 1 1) (by ext1 <;> simpa using! HasFDerivAt.unique (.comp 0
    (by exact hφ.differentiableAt.hasFDerivAt) (ContinuousLinearMap.hasFDerivAt _)) ((hasFDerivAt_id
    0).congr_of_eventuallyEq (H.mono (by aesop))))
  let T v x := ∃ b : ℕ → _, Tendsto (fun n ↦ @n.cast ℝ _ • b n) (of atTop).1 (𝓝 v) ∧ Tendsto
    (fun n ↦ n • ψ (b n)) (of atTop).1 (𝓝 x)
  have B {v w x y} : T v x → T w y → T ..
    | ⟨_, h, i⟩, ⟨_, k, j⟩ => have := (lim_zero _ u h).prodMk_nhds (lim_zero _ u k)
      ⟨_, by simpa [*] using (hasFDerivWithinAt_univ.2 (E.hasFDerivAt.restrictScalars ℝ)).lim this
               univ_mem (h.prodMk_nhds k), (i.add j).congr' (.mono (this hψ) (by grind [smul_add]))⟩
  have Q {ε} hε : ∀ᶠ v in _, ∀ {x}, T v x → ψ (φ x) = x ∧ ‖φ x - v‖ ≤ ε * ‖v‖
  choose r hr H using Metric.mem_nhds_iff.1 ((E.isLittleO.def hε).and (continuousAt_snd hψ))
  have Y {b} (n : ℕ) : let v := (n : ℝ) • b; (1 + ε) * ‖v‖ < r → ‖φ (n • ψ b) - v‖ ≤ ε * ‖v‖ ∧
      n • ψ b ∈ C := n.rec (by simp [*, mem_of_mem_nhds]) fun n ih ↦ by simpa [add_smul,
    SameRay.norm_add] using (fun hn ↦ (ih (hn.trans_le' (by bound))).rec fun i a ↦ by
    simpa [mul_add, ← sub_sub, o, (s a).1] using (@H ((φ (n • ψ b), 0), φ (n • ψ b), b) (by
      simp [dist_eq_norm]; grw [← hn, norm_le_norm_sub_add, i, ← sub_nonneg]; ring; bound)).imp_left
      (norm_sub_le_of_le i))
  exact ((tendsto_norm_zero.const_mul _).eventually_lt_const (by simpa)).eventually_nhds.mono fun v
    k _ ⟨b, h, i⟩ ↦ (s (c.mem_of_tendsto i (.mono (h k) (Y · · |>.2)))).imp_right fun a ↦ .mono (h
    k) (Y · · |>.1) |> le_of_tendsto_of_tendsto (.norm (.sub (.comp a i) h)) (h.norm.const_mul _)
  choose f hf using (⟨_, _, (hasFDerivAt_id 0).lim _ u, le_nhds_lim (.map ..)⟩ : ∀ {v}, ∃ x, T v x)
  have Z {v x} (h : T v x) : -@f (-v) = x
  grind [by simpa using (Q one_pos).self_of_nhds (add_neg_cancel v ▸ B h hf)]
  let e := AddMonoidHom.mk' @f fun _ _ ↦ Z hf ▸ Z (B hf hf)
  obtain ⟨L, D : HasFDerivAt (φ ∘ e) (.id ℂ _) 0⟩ := (Q one_pos).mono fun v h ↦ (@h (e v) hf).1,
    .of_isLittleO (.of_bound (@Q · · |>.mono fun v h ↦ by simpa [h0] using! (h hf).2))
  have a := analyticAt_of_eventually_differentiable (f := φ ∘ e) (.mp (D.continuousAt (by simpa [*]
    using! hφ.eventually_analyticAt.curry_nhds)) (L.mono fun x _ k ↦ add_zero x ▸
    (differentiableAt_comp_add_left x).1 (.congr_of_eventuallyEq (.comp 0 (by simpa [*] using
    k.self_of_nhds.curry_right.differentiableAt) D.differentiableAt) (L.mono (by grind)))))
  have M := map_congr L ▸ le_map_of_right_inverse hs (.mono_right (by simpa using! hc.self_of_nhds)
    (a.hasStrictFDerivAt.map_nhds_eq_of_surj (by simp [D.fderiv])).ge)
  use e, {toDiscreteTopology := ((Metric.mem_nhdsWithin_iff.1 (D.eventually_ne ⟨1, .id⟩)).elim
    fun _ h ↦ .of_forall_le_norm h.1 fun y k ↦ by_contra (h.2 ⟨by simpa using ·, by simpa⟩ (congrArg
    φ y.2))), span_top := eq_top_iff'.2 fun v ↦ by_contra (exists_le_ker_of_notMem · |>.rec fun l
    ⟨_, k⟩ ↦ (mapClusterPt_zero_atTop_nsmul (e v)).frequently (M (image_mem_map
    (l.toContinuousLinearMap.2.abs.continuousAt (gt_mem_nhds (by simpa : _ < |l v|))))) (.mono
    (mem_atTop 1) fun n a ⟨b, c, h⟩ ↦ by simp_all [l.sub_mem_ker_iff.1 (k (subset_span (by simp [h]
    : b - n • v ∈ _)))]))}, L, a, D, ⟨(quotient_finite_of_isOpen _ (isOpen_of_mem_nhds _ (M
    range_mem_map))).card_pos.ne'⟩, fun γ h k ↦ ⟨_, fun z ↦ Z hf ▸ Z ⟨_,
    (k.hasFDerivAt.restrictScalars ℝ).lim z u, EventuallyEq.tendsto ((u.eventually_ne_atTop 0).mp
    (.mono (u.inv_tendsto_atTop.zero_smul_const z (h (γ.map_zero ▸ hs))) (by simp_all [← map_nsmul,
    ← smul_assoc])))⟩⟩
