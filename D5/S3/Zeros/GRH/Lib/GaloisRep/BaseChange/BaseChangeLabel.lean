/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLabel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLabel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.BaseChange.BaseChangeLabel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/BaseChange/BaseChangeLabel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.ParahoricTypeLabel
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.BaseChangeEigenchar
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Base change keeps a depth-zero label at an inert place via Shintani lift. -/


open NumberField Representation Function Fint ComplexConjugate FiniteField Module SemidirectProduct
  algebraMap
variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Fintype n] {w :
  FinPlace E} (χ : GL n (ResField w) → ℂ)

/-- The function on GL_n(E_w) equal to the complex conjugate of χ(g mod w) for g in GL_n(O_w),
and 0 elsewhere. -/
noncomputable def inflateConj g := if h : _ then conj (χ (reduceGL ⟨g, h⟩)) else 0

attribute [local simp] inflateConj mem_localCongruence_zero mul_mem_cancel_left mul_mem_cancel_right
  locMap_mem_Kw atPlace_baseChangeGf atPlace_galoisGf
attribute [local simp ←] MulMemClass.mk_mul_mk algebraMap_ResField_eq_zero

lemma exists_rep_inflateConj hw {κ} : let π := ((stdSpace E n).formTranslation κ).comp (atSplit hw)
  let K := levelSpace π (localCongruence n w 0)
  ∀ W : Subrepresentation π, ∃ ρ : Representation ℂ _ ↥(K ⊓ W.1), ∀ χ v,
  let x := ρ.asAlgebraHom (groupAlgElem (conj <| χ ·)) v
  heckeFun π (localCongruence n w 0) (inflateConj χ) v = x ∧ (HasLabel v.1.1 hw χ ↔ x ≠ 0) := by
  intro π K W
  have H : K = invariants ((π.comp (Kw ..).subtype).comp reduceGL.ker.subtype) := by aesop
  refine ⟨(Units.coeHom _).comp
    (reduceGL.liftOfSurjective reduceGL_surjective ⟨(subrepresentation (π.comp
    (Kw ..).subtype) _ fun k v ↦ H ▸ .imp (le_comap_invariants _ _ _ ·) (W.2 _ ·)).asGroupHom, fun k
    h ↦ by ext v : 3; exact H.le v.2.1 ⟨k, h⟩⟩), fun X v ↦ ⟨(heckeFun_eq_sum (r := (·.1) ∘ surjInv
    reduceGL_surjective) (s := ⊤) ?_ v.2.1 ?_ ?_).2.trans ?_, (and_iff_right (congr($(H.le v.2.1
    ⟨·, ·⟩).1))).trans ?_⟩⟩ <;> simp +contextual [surjInv_eq, asAlgebraHom_eq_sum, Subtype.ext_iff,
    Set.InjOn, inv_mul_eq_one, QuotientGroup.eq, ← InvMemClass.coe_inv, -Subgroup.coe_inv] <;> rfl

lemma reduceGL_map_locMap [CMType E'] {u : FinPlace _} {ι} (e : u.comap ι = w) ψ (hψ : ∀ x, ψ
  (algebraMap _ _ x) = ↑(.mapRingHom ι x : 𝓞 E')) g a : reduceGL ⟨.map (n := n) _ g, a⟩ = (reduceGL
  ⟨g, (locMap_mem_Kw e).1 a⟩).map ψ := by
  ext
  refine (algebraMap_ResField_surjective ..).rec fun x hx ↦ ((hx ▸ hψ x).trans ?_).symm
  erw [residue_eq_iff_valuation_sub_lt_one] at *
  simpa using! (isEquiv_comap_locMap ι e).lt_one_iff_lt_one (x := (x : E) - _) |>.2 hx

variable [Algebra E E']

variable [CMOver E E'] {u : FinPlace E'} {μ} [hμ : IsStep E' μ] (hw) (hu : _ ≠ u) (h : ∀ u',
  .below E u' = w ↔ u' = u) (hD : ∀ x, μ (locIdele w x) = 1) [Algebra (ResField w) (ResField u)]
  (hR : ∀ x : 𝓞 E, ((x : ResField w) : ResField u) = (x : 𝓞 E')) (hq :
  finrank (ResField w) (ResField u) = finrank E E') {Ξ : Hall (ResField w)}
include h hD hR hq
attribute [-simp] SemidirectProduct.mk_eq_inl_mul_inr

/-- For a step E'/E inert at a split w, μ_w = 1, u split above w, and a class function S on
GL_n(k_u) ⋊ Gal(k_u/k_w) that is a Shintani lift of Ξ: for some σ ≠ 1 and φ, the inflated Ξ
and S(·, φ) match at principal level (`IsLocalMatching`). -/
lemma isLocalMatching_shintani {S : GalSemidirect (ResField w) _ n → ℂ} (c : IsClassFunction S) (L :
  DescendsTo S Ξ) : ∃ φ, IsLocalMatching μ {w} (atSplit hw) (atSplit hu) (localCongruence n w 0)
  (localCongruence n u 0) {()} (fun _ ↦ inflateConj Ξ.evalGL) fun _ ↦ inflateConj (S ⟨·, φ⟩) := by
  let φ := frobeniusAlgEquivOfAlgebraic (ResField w) (ResField u)
  obtain ⟨o : orderOf φ = _, ⟨⟩, σ, hσ⟩ := hq ▸ orderOf_frobeniusAlgEquivOfAlgebraic ..,
    (h u).2 rfl, IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(E'/E) u.1
  have hφ := (o ▸ hμ.out).ne_one ∘ orderOf_eq_one_iff.2
  replace hσ (x : 𝓞 E') : φ x = ↑(σ • x) := .symm (by
    simpa [φ, card_ResField, ← Nat.card_eq_fintype_card] using! hσ x)
  have := by simpa [hσ, AlgEquiv.ext_iff, (algebraMap_ResField_surjective u).forall] using hφ
  obtain ⟨⟨m, -, l, -, m₁⟩, hs, R⟩ := exists_baseChange_level (n := n) (σ := σ) (by bound)
    isOpen_Kf, (h _).1 (below_comap σ u), isLocalRetraction_atSplit n h hu hw
  obtain ⟨-, -, coh, -, H⟩ := l _ _ (R.2.2.symm.trans (by ext; exact forall₂_congr (m₁ _
    (h · |>.1 · ▸ ⟨⟨σ, by simpa⟩, by simp [hD]⟩) (by simp) · · ▸ .rfl)))
  have N a ha m : ∃ h, (⟨reduceGL ⟨a.atPlace u, ha⟩, φ⟩ : GalSemidirect _ _ n) ^ m =
    ⟨reduceGL ⟨(twistedNorm (galoisGf σ) m a).atPlace u,
    h⟩, φ ^ m⟩ := m.rec (by simp [twistedNorm, ← OneMemClass.one_def]; rfl) fun m ⟨h, e⟩ ↦ by
    simp [pow_succ', twistedNorm_succ', *, reduceGL_map_locMap hs φ hσ]; rfl
  refine ⟨φ, σ, by bound, Gf.atPlace _, Gf.atPlace u, ⟨fun _ ↦ by constructor <;> exact
    ⟨(finite_quotient_image_of_isCompact isOpen_localCongruence (isCompact_Kw _)).subset fun q _ ↦
    ⟨_, by aesop, q.out_eq⟩, by simp +contextual⟩, ?_⟩, ?_,
    isOpen_localCongruence.preimage_of_continuous, _, ⟨fun _ ↦ (·.1), R.2.2.ge⟩, coh, fun _ _ ↦
    ⟨show ∀ k ∈ _, ∀ δ, (_ : _ → ℂ) (k⁻¹ * δ * galoisGf σ k) = _ from ?_, fun P c ↦ by
    peel 7 H P (by revert c; gcongr <;> simp +contextual); exact this.imp (fun C _ i e ↦ dite_congr
    (by simpa using congr($(C _ i e) ≠ 0))
      (fun _ ↦ congr(conj $(L _ ((fixed_eq_range_iff_ne_one (hq ▸ hμ.out)).2 hφ) _ _ rfl
      ((N ..).2.trans (by simp [o ▸ i ▸ e, reduceGL_map_locMap _ _ hR]; rfl)))).symm) (by simp)) (by
    simp; tauto)⟩⟩ <;> simp +contextual [EmbeddingLike.map_eq_one_iff, *, SetLike.ext_iff,
    reduceGL_map_locMap hs φ hσ, reduceGL_map_locMap _ _ hR, eq_ite_iff,
    Matrix.GeneralLinearGroup.ext_iff, fun δ x ↦ show S ⟨x⁻¹ * δ * x.map φ, φ⟩ = _ from c ⟨δ,
    φ⟩ (inl _), fun a h ↦ show reduceGL ⟨_, inv_mem h⟩ = _ from reduceGL.map_inv ⟨a, h⟩]

/-- Take a step E'/E, w split with μ_w = 1, u split the only place above w, of residue degree
[E':E]. If f has as label a character Ξ with lift Ξ' (`Lift` over ℕ), some eigenform
over E', a weak base change of f off w, has label Ξ' at u. -/
lemma exists_baseChange_hasLabel [StablyUnram E'] {κ f} (hf : f ∈ (stdSpace E n).forms κ) (hΞ :
  IsChar (Ξ.evalGL (n := n))) {Ξ'} (hsh : Lift ℕ Ξ Ξ') (hl : HasLabel f hw Ξ.evalGL) :
  ∃ f' ∈ (stdSpace E' n).forms κ.baseChange, ∃ P, IsEigenform f' P ∧ IsWeakBaseChange μ {w} f f' ∧
  HasLabel f' hu Ξ'.evalGL := have ⟨_, c, L, K⟩ := hsh.exists_descendsTo n
  have C := isChar_of_mem_virtualChars c
  (isLocalMatching_shintani hw hu h hD hR hq C.isClassFunction L).elim fun φ M ↦
    (exists_isWeakBaseChange_of_matching ⟨_,
    hf⟩ M ![] 0 _ rfl (by simp) nofun (by rw [iInf_of_empty, inf_top_eq]; exact (fun V hV _ h H ↦
    (exists_rep_inflateConj _ V).rec fun ρ hρ ↦ (hρ _ ⟨_, by simpa [Subtype.ext_iff] using hl.1,
    hV⟩).2.1 hl congr($(hΞ.groupAlgElem_eq_zero_iff.2
    (by simpa [classInner, character, asAlgebraHom_eq_sum, finMean] using (congrArg _ (LinearMap.ext
    (Subtype.ext <| hρ _ · |>.1.symm))).trans H)) _)))).elim fun f' ⟨_, a, b, _, ⟨v, hv, e⟩, _⟩ ↦
    (exists_rep_inflateConj hu ⊤).rec fun ρ hρ ↦ have E := e.symm.trans (hρ _ ⟨v, hv, ⟨⟩⟩).1
    ⟨_, f'.2, _, a, b, E ▸ (hρ ..).2.2 (DescendsTo.iff_comp_inl_eq_evalGL.1 K ▸ fun H ↦
      a.1 (by simpa [*, ← mk_eq_inl_mul_inr] using (congr(ρ.asAlgebraHom
      $(((irreducible_criteria_of_isClassFunction ℤ (C.comp inl).star.isClassFunction).2.2 _ fun _ ↦
      C.star.groupAlgElem_eq_zero _ (inr φ) ∘ (C.comp inl).groupAlgElem_eq_zero_iff.1).choose_spec)
      ⟨v, hv, ⟨⟩⟩))))⟩
