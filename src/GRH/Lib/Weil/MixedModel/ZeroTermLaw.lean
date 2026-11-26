import GRH.Lib.Weil.MixedModel.MixedModelIntegrable
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: the Schrödinger and mixed models of the Weil representation and the action of
parabolic subgroups. This file treats adelic unitary groups over a CM field and uses vectors with
integrable coefficients instead of Schwartz functions. The representation is normalised by its
vacuum coefficient, so the parabolic and split-place formulas are proved rather than taken as the
definition. Source: C. Mœglin, M.-F. Vignéras, J.-L. Waldspurger, Correspondances de Howe sur un
corps p-adique, LNM 1291, 1987; S. Kudla, Splitting metaplectic covers of dual reductive pairs,
Israel J. Math. 87 (1994) 361–401; A. Weil, Acta Math. 111 (1964) n° 16–19, 41.

This file: Parabolic subgroup acts on the zero term by an explicit character of the determinant. -/

open Circle Complex ComplexOrder Finset G MatMul Matrix MeasureTheory WeilData Heisenberg.IsVacuum

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s n₀ p} [Fintype n₀]
  [Fintype p] {s₀} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) {g} (g₀ :
  G E s₀) (hi : D.iCoord * (g.mat * D.iAdelic) = g₀.mat) (a : GL p (𝔸 E)) (hk : D.ActsOnFrame g a)

namespace Space.Splitting

attribute [local simp ←] coe_inv_eq_conj conjTranspose_mul mixedTerm_zero

attribute [local simp] star_eq_conjTranspose levi_mul_iAdelic levi_mul_kAdelic levi_mul_lAdelic
  radicalElt_mul_iAdelic ω_ϱ

/-- For a in GL_p(𝔸) and x the point of the space `hypSpace` of p hyperbolic planes, some g₁ in
the adelic unitary group has matrix x⁻¹ diag(a*⁻¹, a) x, and Δ(g₁)υ(det a) is a nonnegative
real number. -/
lemma exists_hyp_levi_multiplier_nonneg : ∃ g₁ : G E (hypSigns p), 0 ≤ weilMultiplier g₁ * υ.1
  a.det ∧ g₁.mat = (hypSpace E p).x⁻¹.1 * fromBlocks a⁻¹.1ᴴ 0 0 a.1 * (hypSpace E p).x := by
  refine ⟨(hypSpace ..).toRatCoords.symm ⟨blockGL (star a⁻¹, a), by simp [U]⟩, ?_, ?m⟩
  erw [upsilon_eq_prod_mul_of_v_eq (a.map (.snd ..)).det (by simp [a.map_det]), mul_mul_mul_comm,
    ← prod_mul_distrib]
  refine mul_nonneg (b := glMultiplier (.map _ _) * _) (prod_nonneg fun w ↦ ?_) ?_
  erw [realMultiplier, ← principalMinor_conjTranspose, principalMinor, ← det_reindex_self
    (.trans (.subtypeEquivRight (by simp)) .sumIsRight), congr((($(?m)).map _)ᴴ.toBlocks₂₂.det)]
  simp [-coe_units_inv, ← evalInf_apply, RingHom.map_det]
  repeat rw [(rfl : .map _ _ = (_ : ℂ) • fromBlocks 1 _ _ 1)]
  simp [fromBlocks_smul, ← smul_add, ← det_mul, field, div_nonneg, conjTranspose_map
    (evalInf w) (by tauto), (PosSemidef.one.add (posSemidef_conjTranspose_mul_self _)).det_nonneg]
  simp
  rw [glMultiplier_mul_of_mem _ (inv_mem ?hx) ?hx, glMultiplier_fromBlocks _ _ (.refl _),
    glMultiplier_star_inv_mul]
  simp [chiFin, chiAdelic, field]
  exacts [fromBlocks_map .., mem_intGL.2 (isOrthoIntegral_hypSpace.imp (·.2) (·.2)), rfl]

lemma integrable_dataInner_mixedTerm f f' : Integrable fun x ↦
  V₀.dataInner (D.mixedTerm x f) (D.mixedTerm x f') := .mono'
  (by simp; fun_prop) (by fun_prop) (.of_forall fun _ ↦ (V₀.dataInner ∘SL D.zeroTerm).le_opNorm₂ ..)

lemma integral_dataInner_mixedTerm : ∃ C, ∀ f f', ∫ x, V₀.dataInner (D.mixedTerm x f)
  (D.mixedTerm x f') = C * V.dataInner f f' := ⟨_, integral_form_eq_mul_modelInner (fun _ ↦
  V₀.dataInner.bilinearComp ..) D.integrable_dataInner_mixedTerm fun _ _ _ ↦
  .trans (congr(∫ x, V₀.dataInner $(isMixedLaw_mixedTerm ..) $(isMixedLaw_mixedTerm ..)).trans
  (by simp [← mul_assoc]; rfl)) (integral_add_right_eq_self ..)⟩

include hi hk in
lemma exists_zeroTerm_omega_eq_smul : ∃ c : ℂ, ∀ f, D.zeroTerm (V.ω g f) =
  c • V₀.ω g₀ (D.zeroTerm f) := by
  obtain ⟨r, k, h, -⟩ :=
    D.isMixedLaw_comp_rho (V₀.ω g₀⁻¹ ∘L D.zeroTerm ∘L V.ω g) (by aesop) (by simp [*, ← mat_mul,
    ← D.lCoord.mul_assoc, D.lCoord_mul_mat hk]), D.exists_isAdapted_and_frame_eq 1
  obtain ⟨⟨c', ⟨⟩⟩, c, hc⟩ := h.mixedTerm_omega_vacElem, h.exists_omega_vacElem_of_isMixedLaw r
  exact ⟨_, by simpa [rep_apply_apply] using (congr(V₀.ω g₀ <| $(V.ext_of_vacElem k (T' := (c /
    c') • _) fun _ ↦ (V.ω_ϱ .. ▸ r 0 .. :).trans (by simp [↓hc, *, smul_smul]; field_simp)) ·))⟩

/-- If g is the Levi element of a splitting attached to a in GL_p(𝔸) and g₀ in the group of V₀,
then ev(ω(g)f) = χ_𝔸(det a)⁻¹ ω(g₀) ev(f) for all f in 𝒮(V), where χ_𝔸 = υ|·|^(−½), |·| the
idele norm. -/
lemma zeroTerm_omega_levi f : D.zeroTerm (V.ω (D.levi (a, g₀)) f) =
  (chiAdelic a.det)⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  set g := D.levi _
  obtain ⟨⟨c, hc⟩, ⟨_, hC⟩, ⟨g₁, ⟨L⟩⟩, k, hg, e, hs, h⟩ := D.exists_zeroTerm_omega_eq_smul g₀
    (by simp) a (D.levi_mul_kAdelic a g₀), D.integral_dataInner_mixedTerm,
    exists_hyp_levi_multiplier_nonneg a, D.exists_isAdapted_and_frame_eq 1
  have : weilMultiplier (k⁻¹ * g * k) = weilMultiplier g₁ * weilMultiplier g₀ :=
    weilMultiplier_fromBlocks hs (.trans (by
    rw [← submatrix_one_equiv e, ← mat_one, ← inv_mul_cancel k]
    simp [↓mat_mul, submatrix_mul _ _ _ id, ← h]
    simp [*, g, frameAt, ← Matrix.mul_assoc]) (one_mul _))
  cases hg.mixedTerm_omega_vacElem; set u := V.ω k _
  obtain ⟨P, e₁⟩ := integral_pos_of_integrable_nonneg_nonzero (x := 0) (by fun_prop)
    (D.integrable_dataInner_mixedTerm u u).norm (by simp_intro _) (by simp [*, vacuumFn]),
    (hC u (V.ω g u)).symm, this ▸ V.dataInner_omega_of_vacElem _, (hC u u).symm,
    V.dataInner_omega g u u ▸ hC .., left_ne_zero_of_mul_eq_one
    (conj_delta_mul_weilRep_vacElem adelicAction (k⁻¹ * g * k)), volume_map_mulVec_adele (star a) ▸
    (integral_map (by fun_prop) ((cont (adelicHeis E 1)).norm.pow 4).aestronglyMeasurable).symm
  simp [by simpa [↓ω_ϱ, ↓mulVec_mulVec] using fun x ↦ hc (V.ϱ (D.lAdelic *ᵥ a.1ᴴ *ᵥ x) u), u, g,
    ↓dataInner_omega, dataInner_omega_left, *, chiAdelic] at *
  ring_nf at *; simp [mul_assoc, *] at *; norm_cast at *
  simp [*, field, mul_conj] at *
  simp [by simpa [field, c.norm_def, *] using norm_of_nonneg' (div_nonneg
    (pos_of_mul_pos_left (e₁.le.trans_lt' (mod_cast P)) (by positivity)).le (star_nonneg_iff.2 L))]

/-- If gk = ka with a in GL_p(𝔸) and gι = ιg₀ + kc with g₀ in the adelic group of V₀, then
ev(ω(g)f) = υ(det a)⁻¹ |det a|^{1/2} ω(g₀) ev(f) for all f.

Known result: Schrödinger and mixed models of the Weil representation; action of parabolic
subgroups. -/
lemma zeroTerm_omega (hi : D.iCoord * (g.mat * D.iAdelic) = g₀.mat) {a} (hk : D.ActsOnFrame g a) d
  (h : a.det = d.1) f : D.zeroTerm (V.ω g f) = (chiAdelic d)⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  obtain ⟨c, b, t, _, rfl, rfl, e⟩ := D.exists_eq_radicalElt_mul_levi hk
  choose d _ using (D.exists_zeroTerm_omega_eq_smul 1 (by simp) 1 <| D.radicalElt_mul_kAdelic c ·)
  obtain ⟨⟨⟩, ⟨⟩, _, _, e⟩ := t.det.ext h, ext_mat (hi ▸ e), D.exists_levi_mul_radicalElt_eq c b
  rw [← zeroTerm_omega_levi, ← mul_inv_cancel_left (_ * _) (levi _ _)]; nth_rw 3 [e]
  simp [↓map_mul, *, -mixedTerm_zero, zeroTerm_omega_levi]; module
