import GRH.Lib.Shimura.Uniformisation.ThetaCoords
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Theta group of an ample line bundle: span of sections, K(L), symmetric theta structures
(known result; see Lib.Shimura.ThetaGroup.RigidFibres).

Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number (known
result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Sections over a valuation ring as theta functions; lifted translations, commutators,
orbit lattices. -/


open CategoryTheory AlgebraicGeometry Over ValuativeArc Function IsSchemeTheoreticallyDominant
variable {V ι κ : Type} [FinComplexSpace V] {O} [CommRing O] [ValuativeArc O] {A : Over (Spec ⟨O⟩)}

/-- Let A be a smooth proper scheme over a valuation ring O with fraction field ℂ, and s a family
exhausting its sections. Then A is reduced and the complex points of the s(z) are dense in A. -/
lemma isSeparatingFamily_atGeneric [Smooth A.hom] [IsProper A.hom] {Z s} (h : @Surjective Z (_ ⟶ A)
  s) : IsSeparatingFamily (atGeneric s) := ⟨isReduced (Limits.pullback.fst A.3 genericPt),
  .of_fibres (eq_const_of_subsingleton ‹ValuativeArc O›.genericPt _ ▸ genericPt.denseRange) _ fun _
  y _ ↦ (bijective_restrict_genericPt.2.comp h (homMk y)).rec (⟨·, congr($(·).1)⟩)⟩

lemma HasThetaCoords.holomorphicAt [Finite κ] {Λ s L B χ θ} (h :
  @HasThetaCoords _ κ V _ Λ (atGeneric s) L B χ θ)
  (hL : L.IsProjEmbedding A.hom) z : HolomorphicAt (atGeneric s) z := .of_isHomogCoords hL
  (analyticAt_of_eventually_differentiable <| .of_forall <| h.3 · |>.1) (.of_forall h.4)

variable [IsAbelianScheme A] {L : LineBundle _ κ} (u : Uniformisation A V) {B χ θ} (h :
  HasThetaCoords u.L (atGeneric u.expMap) L B χ θ)

/-- For an abelian scheme A over O, a valuation ring with fraction field ℂ, uniformised by u with
theta coordinates θ_i for L,
r ↦ θ_i·r_i embeds H⁰(L) O-linearly into functions on V, sending coordinates to the θ_i and lifts of
translation by u.expMap a to multiples of `RealComplexForm.thetaShift` a. -/
lemma exists_theta_evaluation {Λ s B} (h : HasThetaCoords Λ (atGeneric s) L B χ θ) : ∃ T :
  _ →ₗ[O] _, (∀ r g, T r = g ↔ ∀ i z, θ z i ≠ 0 → r.1 i _ (atGeneric s z) = g z / θ z i) ∧ (∀ i, T
  (coordSection h.1 i) = (θ · i)) ∧ ∀ u : Uniformisation A V, Λ = u.L → s = u.expMap → Injective T ∧
  ∀ a Φ, IsTranslationLift L (s a) Φ → ∃ c : ℂ, ∀ r, T (Φ r) = c • B.thetaShift a (T r) := by
  choose p n using (h.4 · |>.ne_zero)
  have := (h.4 · ·)
  let T : L.H0 O →ₗ[O] _ := .pi fun z ↦ θ z (p z) • ⟨⟨(·.1 (p z) _ (atGeneric s z)), by simp⟩,
    by simp [H0_smul, atGeneric, ValuativeArc.genericPt_eq, Algebra.smul_def]⟩
  exact have E r g := ⟨(· ▸ fun i z _ ↦ by simp [T, r.2.1.2 i (p z), field, *]), by simp_all [T,
      funext_iff, mul_div_cancel₀]⟩; ⟨T, E, by simp +contextual [*, coordSection, field], by
    rintro u rfl rfl; use fun s r _ ↦ H0_ext ((isSeparatingFamily_atGeneric
      u.4).pointFn_ext · · (by simp +contextual [(E ..).1 rfl, *])), fun a Φ ⟨w, b, e⟩ ↦
      (h.riemannForm_eq_of_isFrame (h.pull_translate (u.atGeneric_add a)) b).2.2.imp fun c K s ↦
    by ext z; simp [e _ _ (p (z + a)), *, ← u.atGeneric_add, thetaShift_apply, T, field]⟩

include h

/-- Weil pairing: let L have theta coordinates for B, and let Φ, Ψ lift to L^m the translations
by the images of a, b. Then ΦΨ = c·ΨΦ on all coordinates if and only if c = exp(2πi m
E(a,b)), E the Riemann form of B. -/
lemma lift_commutator_iff_weil_pairing {m a b c Φ Ψ} (p : IsTranslationLift (L.pow m) (u.expMap a)
  Φ) (q : IsTranslationLift _ (u.expMap b) Ψ) : (∀ l i, Φ (Ψ (coordSection
  l i)) = c • Ψ (Φ (coordSection l i))) ↔ algebraMap O ℂ c = (m • B).riemannPhase a b := by
  have ⟨T, _, G, K⟩ := exists_theta_evaluation (h.pow m)
  choose I _ e using K u rfl rfl
  suffices ∀ s, T (Φ (Ψ s)) = _ • T _ from ⟨fun E ↦ smul_left_injective ℂ (((I.comp (q.mul
    p).injective).ne_iff' (by simp)).2 (ne_zero_of_map ((G _).trans_ne (ne_iff.2 ⟨0, ((h.pow m).4
    0).ne_zero.choose_spec⟩)))) (.trans (by aesop) (this _)), (by simp [← I.eq_iff, this, ← ·])⟩
  simp [e a, e b, *, (h.pow m).2.thetaShift_comm a, funext_iff, field]

/-- Let N, an O-module of sections containing the coordinates, be stable under lifts of
translations by Λ^∨; nΛ^∨ ⊂ Λ, n a unit, B positive. Finitely many theta functions f_j, not
all zero, have multiples γf_j in N, γ ≠ 0, not all vanishing on any Λ^∨-orbit of a
field-valued point. -/
lemma exists_sections_of_translation_stable [Finite κ] [IsPosRiemann B] {n : ℕ} (hn :
  IsUnit (n : O)) {N : Submodule O _} (H : ∀ a ∈ B.dualLattice, n • a ∈ u.L ∧ ∃ Φ,
  IsTranslationLift L (u.expMap a) Φ ∧ N ≤ N.comap Φ) (hN : ∀ k, coordSection h.1 k ∈ N)
  {f : ι → _} [Finite ι] (hf : ∀ j, f j ∈ B.thetaSpace χ) i (f0 : f i ≠ 0) : ∃ γ ≠ 0, ∃ r : ι → N,
  (∀ j i z, θ z i ≠ 0 → (r j).1.1 i _ (atGeneric u.expMap z) = γ * f j z / θ z i) ∧ ∀ K [Field K] t,
  ¬∀ a ∈ B.dualLattice, ∀ j i, (r j).1.1 i ⟨K⟩ (t ≫ (translation (u.expMap a)).left) = 0 := by
  obtain ⟨⟨Q, E, G, K⟩, p, o⟩ := exists_theta_evaluation h, L.exists_landsIn (u.expMap 0).1
  obtain ⟨⟨J, K⟩, y⟩ := K u rfl rfl, ((h.4 ..).1.1 (o.comp _)).ne_zero
  choose! l Φ hΦ s using H
  choose! c hc using (K _ _ <| hΦ · ·)
  peel h.2.exists_proportional_orbit_lattice (⟨_, hf ·⟩) (⟨_, h.3 ·⟩) i p c hn l (by simpa)
    (y congr($(·).1 _)) fun a n ↦ ((hΦ a n).mul (hΦ _ (neg_mem n))).elim fun _ ⟨b, e⟩ ↦
    ⟨(b.2 (p, p) _ _ (by simpa)).unit, by simpa [↓G, ↓hc, *, h.2.thetaShift_thetaShift,
    ValuativeArc.genericPt_eq, field, coordSection, b.1.1 _ _, L.5, o.comp, atGeneric, -map_zero]
    using (e (coordSection h.1 p) p p _ _ · · ▸ (E (Φ a _) _).1 rfl p _ y :)⟩ with γ _ H
  replace H N := by
    simpa +contextual [E _ (γ • _), ← G, ← hc, J.eq_iff, -Subtype.exists,
      -Subtype.forall] using H (.map Q N)
  choose r m e using (H N s).1 hN
  use (⟨_, m ·⟩), e, fun K _ t Z ↦ (L.exists_landsIn t).elim fun i o ↦ by simpa [coordSection, L.5,
    o] using ((H ⟨⟨⟨{r | ∀ a ∈ _, ∀ i, r.1 i _ (t ≫ (translation (u.expMap a)).1) = 0}, by aesop⟩,
         by simp⟩, by grind [H0_smul]⟩ fun z e r a w k i ↦ by_cases ((hΦ z e).choose_spec.2 _
    _ _ _ _ · (L.exists_landsIn _).choose_spec |>.trans (by simpa [← comp_left, add_assoc] using
    (Or.inr (a _ (add_mem k e) _)))) ((Φ z r).2.2 i _ _)).2 (⟨_, (Z · · _), e ·⟩) i 0 · i)
