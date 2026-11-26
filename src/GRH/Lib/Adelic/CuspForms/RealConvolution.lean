import GRH.Lib.Adelic.CuspForms.Definite
import GRH.Lib.DiscreteSeries.Rigidity.KernelFixes
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Adelic unitary groups unimodular; quotient integral on definite groups equals weighted
class sum. Right convolution at infinity: continuity, composition; discrete series kernels are cusp
kernels. -/

open MeasureTheory Measure Set DoubleCoset Subgroup HasFiniteType ProbabilityTheory

attribute [-simp] MonoidHom.coe_range

variable {E n} [Field E] [CMType E] [Fintype n] {s : n → ℤˣ} {W} [RCLike W] {V : Space E n 1}

instance : (@volume (Gf E n) _).IsMulRightInvariant := isMulRightInvariant_of_finite_covolume
  (isFiniteMeasure_quotMeasure_of_cocompact _ (stdSpace ..).exists_isCompact_finitePart)

instance : (@volume (G E s) _).IsMulRightInvariant := by
  apply_rules [prod.instIsMulRightInvariant, pi.isMulRightInvariant]

/-- Let V be definite, F continuous and left Γ-invariant on G, f(g) = ∫_{G_∞} F(x, g) dx, and K
⊂ K₀ an open subgroup fixing f on the right. Then ∫_{Γ\G} F is [K₀ : K]⁻¹ times the class
sum of f over Γ\G_f/K. -/
lemma Space.integral_quotMeasure_eq_classSum {F f} (hi : V.Γ.FixesLeft F) (hx : ∀ g, ∫ x, F (x, g) =
  f g) K [o : IsLevel K] (H : K ≤ rightStab f) (hF : Continuous F := by fun_prop) :
  V.quotMeasure[F] = (stdLevelIndex K : W)⁻¹ * classSum V.Γf K f := by
  choose s hs s' using
    exists_transporter (u := fun γ : V.Γ ↦ γ.1.2) V.Γf (V.fact_embFin_injective.1.injOn_range
    (g := Prod.snd)).injective (range_subset_iff.2 (⟨⟨_, ·, rfl⟩, rfl⟩)) K
  have i u := (fun k ↦ k.integrableOn F (ν := volume).integrable_indicator
    k.measurableSet) (isCompact_univ.prod (o.isCompact.image_auto (u * ·)))
  erw [mul_finsum, finsum_eq_sum_of_fintype]
  convert! integral_finsetSum (μ := V.quotMeasure) _ fun (c : Quotient _ _) _ ↦
    (measurePreserving_orbitMeasure.fubini
    (i c.out)).1.integral_prod_left.smul ((s c.out c.out).card⁻¹ : ℝ) with g d
  simp [← indicator_comp_right (Subtype.val · * g), out_eq', s', smul_def, hi, real_def,
    ← mul_assoc, apply_ite, Function.comp_def, Finset.measurableSet, preimage, -mem_classAut,
    ← (hs · · · |>.trans (and_iff_right (‹V.Γ›.2.choose_spec ▸ ⟨_, rfl⟩)))]
  erw [integral_smul, (measurePreserving_orbitMeasure.fubini (i _)).2, integral_prod_symm _ (i _),
    ←integral_mul_left_eq_self _ d.out, (congrArg _ (funext
    (by by_cases · ∈ K <;> simp [*]; apply H ‹_›))).trans (integral_indicator_const _
    o.2.measurableSet)]
  simp [*, Algebra.smul_def, real_def,
    inter_eq_left.2 o.1 ▸ measure_inter_eq_inv_relIndex isCompact_Kf o.2]; ring

instance : IsMulCommutative (Gf E Unit) := ⟨⟨by aesop (add simp [Matrix.mul_apply, mul_comm])⟩⟩

lemma measureReal_pos_of_isLevel (K : Subgroup (Gf E n)) [o : IsLevel K] : 0 < volume.real
  (SetLike.coe K) := ENNReal.toReal_pos (o.2.measure_ne_zero _ (by simp)) o.isCompact.measure_ne_top

open Finset Matrix.Norms.L2Operator CompactlySupported Asymptotics

attribute [local simp] realConv mul_assoc Prod.mul_def typeKernel U.one_le_norm

variable {E n : _} [Field E] [CMType E] [Fintype n] {s : _} {V : Space E n s} {F : _ → ℂ} {α :
  GInf E s → ℂ}

/-- For smooth compactly supported functions α_w on U(diag s), one per infinite place w, the
compactly supported continuous function x ↦ ∏_w α_w(x_w⁻¹) on G_∞. -/
noncomputable def bumpProduct (α : _ → Bumps s) := (⟨⟨fun x ↦ ∏ w, (α w).1.1 (x w)⁻¹, by fun_prop⟩,
  .intro (isCompact_univ_pi (α · |>.2.inv)) (by grind [prod_eq_zero_iff,
  image_eq_zero_of_notMem_tsupport, Set.mem_inv])⟩ : C_c(GInf E s, ℂ))

lemma le_prod_opNorm [Nonempty n] (g : GInf E s) : 1 ≤ ∏ w, ‖(g w).1.1‖ ∧ ∀ w, ‖(g w).1.1‖ ≤
    ∏ w, ‖(g w).1.1‖ := ⟨by simp [one_le_prod₀], (by grw [← Finset.subset_univ {·}] <;> simp)⟩

/-- A cusp kernel of order B on G_∞: a kernel e with ‖x‖^j e(x) integrable for j ≤ B+1, ‖x‖^B
e(x) bounded (‖x‖ = ∏‖x_w‖), and α ∗ e = e for some continuous compactly supported α. -/
structure IsCuspKernel B (e : GInf E s → ℂ) extends IsIdempotentKernel e where
  integrable_moment : Integrable fun x ↦ ‖e x‖ * (∏ w, ‖(x w).1.1‖) ^ (B + 1)
  exists_bump : ∃ α : C_c(_, ℂ), ∀ y, ∫ x, α x * e (x⁻¹ * y) = e y
  decay : ∃ C, ∀ x, ‖e x‖ * (∏ w, ‖(x w).1.1‖) ^ B ≤ C

attribute [local simp ←] prod_mul_distrib integral_fintype_prod_volume_eq_prod Finset.prod_pow

/-- For n nonempty, if every l_w = 2λ_w is a Harish-Chandra parameter whose entries λ_i, λ_j of
different signs s are at least 500|n|³ + B apart, then the product kernel `typeKernel` l s is a
cusp kernel of order B. -/
lemma isCuspKernel_typeKernel [Nonempty n] {l B} (h : ∀ w, (toHCParam s (l w)).HasLargeGap B) :
  IsCuspKernel B (typeKernel (E := E) l s) :=
  ⟨by use by fun_prop, .fintype_prod (h · |>.isIdempotentKernel_dsKernel.2) <;> simp [← (h
  _).isIdempotentKernel_dsKernel.3, (h _).isIdempotentKernel_dsKernel.4,
  prod_eq_zero_iff, ← prod_div_distrib, ← (h _).isIdempotentKernel_dsKernel.5],
  .congr (.norm (.fintype_prod (h · |>.integrable_norm_pow_smul_dsKernel
  B.succ))) (by simp), ⟨bumpProduct (h · |>.exists_bump_conv_dsKernel.choose),
  fun y ↦ by simp [← (h _).exists_bump_conv_dsKernel.choose_spec (y _), bumpProduct]⟩,
  _, by simp_intro g [dsKernel]; grw [norm_dsCoeff_le_pow (h _) (c := B)] <;> simp [field, div_pow]⟩

@[simp] lemma Space.formRep_apply k y g : V.formRep α k y g = y (g * (1, k)) := rfl

lemma Space.mem_levelSpace_formRep_iff {J y} : y ∈ levelSpace (V.formRep α) J ↔ HasLevel y J := by
  simp [(show · = y ↔ _ from Subtype.ext_iff), funext_iff]

variable (K : OpenSubgroup _) (b : IsBoundedMeasurable F) (r : V.Γ.FixesLeft F) (l :
  HasLevel F K) (o : Integrable α)
include o

lemma eventually_norm_realConv_sub_le {ε} (p : 0 < ε) : ∀ᶠ z in nhds 1, ∀ {F} C,
  IsBoundedMeasurable F → HasLevel F K → ∀ g, (∀ x, α (z.1⁻¹ * x) ≠ α x → ‖F (g * (x, 1))‖ ≤
  C) → ‖realConv α F (g * z) - realConv α F g‖ ≤ ε * ‖C‖ := by
  filter_upwards [prod_mem_nhds ((Lp.instContinuousSMulDomMulAct.1.comp
    (f := (.mk ·⁻¹, o.toL1)) (by fun_prop)).continuousAt (eventually_norm_sub_lt _ p))
    K.mem_nhds_one] with ⟨u, a⟩ ⟨e, ha⟩ F C m l (g, k) b
  have d := (o.comp_mul_left u⁻¹).sub (o.comp_mul_left 1⁻¹)
  grw [← e.trans_eq' (L1.norm_of_fun_eq_integral_norm d), ← C.le_norm_self]
  simpa [sub_mul, integral_sub, ← integral_mul_left_eq_self (α · * _) u⁻¹, *, m.integrable_mul_comp
    _ (g * ·, k), o.comp_mul_left, by simpa using l a ha] using norm_integral_le_of_norm_le
    (d.norm.mul_const C) (.of_forall (by_cases (by simp_all) <| norm_mul_le_of_le le_rfl ∘ b ·))

include b

/-- Fubini for right convolution: for c, k integrable, j measurable and F bounded measurable on
G, ∫ c(z) R(k)F(j z) dν(z) = ∫_{G_∞} k(x) ∫ c(z) F(j(z)x) dν(z) dx, with ν s-finite. -/
lemma integral_mul_realConv {Z} [MeasurableSpace Z] {ν : Measure Z} [SFinite ν] {c} (i : Integrable
  c ν) j (h : Measurable j := by fun_prop) : ∫ z, c z * realConv α F (j z) ∂ν = ∫ x, α x * ∫ z, c z
  * F (j z * (x, 1)) ∂ν := by simp_rw [realConv, ← integral_const_mul, ← mul_assoc, mul_comm (α _)]
                              exact integral_integral_swap (b.integrable_mul_comp (i.mul_prod o) _)

lemma realConv_realConv {p} (hp : Integrable p) a : realConv α (realConv p F <| · * (a, 1)) =
  realConv (fun y ↦ ∫ x, α x * p ((x * a)⁻¹ * y)) F := by ext; simpa using
  (_root_.integral_conv (· * a) o hp (b.comp (_ * ·, _))).2

lemma Space.petersson_realConv_right {F'} (c : IsBoundedMeasurable F') :
  V.petersson F' (realConv α F) = ∫ x, α x * V.petersson F' (F <| · * (x, 1)) :=
  integral_mul_realConv b o (c.memLp_top.star.integrable le_top) _

include r l

/-- If F on G is measurable, bounded, left Γ-invariant and right invariant under an open
subgroup of G_f, and α is integrable on G_∞, then R(α)F is automorphic (continuous,
Γ-invariant, with a level) and bounded. -/
lemma Space.isAutomorphic_realConv : V.IsAutomorphic (realConv α F) ∧
  IsBoundedMeasurable (realConv α F) := b.2.elim fun C _ ↦ by
  refine (fun c ↦ ⟨⟨c, ?_, K, ?_⟩, .of ⟨_, fun g ↦ norm_integral_le_of_norm_le
    (o.norm.mul_const C) ?_⟩ c⟩) (.of_at fun g ↦ tendsto_sub_nhds_zero_iff.1 (map_mul_left_nhds_one
    g ▸ (IsLittleO.of_bound fun _ p ↦ (eventually_norm_realConv_sub_le K o p).mono fun _ h ↦
    h C b l g (by tauto)).tendsto_zero_of_tendsto tendsto_const_nhds)) <;> simp_all [mul_le_mul]

omit o

/-- Let e be a kernel on G_∞ (`IsIdempotentKernel`), K open in G_f, and F bounded, measurable, left
Γ-invariant and right K-invariant. Then R(e)F is a form of type e fixed by K. -/
lemma Space.exists_form_eq_realConv (k : IsIdempotentKernel α) : ∃ y : levelSpace (V.formRep α) K.1,
  y.1.1 = realConv α F := ⟨⟨⟨_, (isAutomorphic_realConv K b r l k.2).elim (⟨·, ·.2, (by
    simpa [-realConv, k.convolution_self] using realConv_realConv b · k.2 1)⟩)⟩,
  mem_levelSpace_formRep_iff.2 (by aesop)⟩, rfl⟩
