/- GID: D5/S3/Zeros/GRH/New/Selmer/OnePlaceDefect
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/OnePlaceDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.OnePlaceDefect. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/OnePlaceDefect.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.CrystallineBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Crystalline defect of the dual of a block at one place, by cases. -/

open Lift CoeffRing Module Nat Classical NeZero NumberField Data Finset

/-- Local loss at one place above ℓ. For O large take lattices: one of rank r with row jumps J,
others with single jump c ∈ [0, t); and a class `Lift.InClass` with jumps among theirs, crystalline,
or tame for ℓ ∣ g. For L among them and in the class, Z_f(L^∨(1)) modulo `Lift.cupOrthogonal` has
normalised length ≤ [G_ℓ : j(Γ)]·rk L·loss/x, x = 1 for the row, else D.t.

Crystalline losses above ℓ are affordable. -/
lemma block_defect_le_at_place {P ℓ Γ} {D : Data P} [hp : ThePrime ℓ] [PadicIso ℓ] [Group Γ] [𝒥 :
  OverGp Γ ℓ] [TopologicalSpace Γ] {e r t J} (hJ : IsRowType D r t J) (hj :
  IsCompletionGroup e 𝒥.toGp) : ∀ᶠ O : CoeffRing ℓ in .atTop, ∀ {L : _ → GalLattice O Γ} {F K U},
  (∃ n, ℓ = D.g n ∧ ∀ s, IsWeilPair (toGp s) 0 → Lift.IsTameType ℓ D.r ((D.r + D.t) * D.r) (K s)) ∨
  F = ⊤ ∧ K = ⊥ → (∀ g, ∀ a ∈ U g, ∃ i, jump (L i).ρ g a ≠ 0) →
  (∀ i g, HasJumps (L i).ρ (coeffEmb O g) (i.elim (J (complexEmbOf e g)) fun c : Fin t ↦ {↑c})) →
  finrank O (L none) = r → ∀ c, let x := ite (c = none) 1 D.t; InClass F K U (L c) →
    O.normLength (relLength (crysCocycles (L c).tateDual.ρ) (cupOrthogonal (InClass F K U) _)) ≤
    𝒥.toGp.range.index * ↑(finrank O (L c) * (loss D ℓ / x)) := by
  obtain ⟨⟨k, -, he, un, y, A, hy⟩, N, ⟨i, a, m⟩⟩ := exists_kummer_chart Γ,
    D.nat_le_of_hasLogBound (B := D.k * D.t).trans' ∘
    le_of_dvd one_le ∘ hp.out.dvd_of_dvd_pow ∘ (dvd_trans · P.N₁_mul_d_dvd_M_omega), hJ.low_or_high,
    D.t_odd.pos, D.k_pos, hJ.t_le, (D.nat_le_of_hasLogBound : 3 * D.t ≤ D.h₂), D.h₂.le_mul_self
  filter_upwards [eventually_primitiveRoot (ℓ ^ k.f.val - 1)] with O ⟨ζ, z⟩ L F K U Y B T rfl c x H
  choose r R using @coeffEmb_surjective _ _ O; replace T i g a := R g ▸ T i _ a
  simp [T, Option.exists, Fin.exists_iff] at B
  have W g : let σ := complexEmbOf e (r g)
    let v := (IsInJumpWindow (D.h₂ ^ 2 + 1) · (ite (id (.mk σ ∈ D.thick)) D.b₁ D.b₂ + (i * D.h +
      D.h₂ - 2 * D.t)) (4 * D.t)); v (-cmSign σ) (U g) ∧ v (cmSign σ) ((U g).image (-· - 1)) := by
    intro σ; simpa [IsInJumpWindow, ← forall_and] using
      fun u h ↦ by obtain ⟨h, ⟨⟩⟩ := (B g u h).imp_left (m σ u),
      Int.units_eq_one_or (cmSign σ) <;> simp [*, w, abs_le] at h ⊢ <;> lia
  obtain ⟨hD, ⟨X⟩, ⟨n, ⟨⟩, Y⟩ | ⟨⟨⟩, ⟨⟩⟩⟩ := H.dual, (by lia : x ≤ D.t ∧ 0 < x), Y
  · have G g := (hj.2 g).2 (fixes_emb_of_fixes_rootsOfUnity fun z hz ↦
      (exists_apply_eq_pow (P.not_dvd_N₁_mul_d_of_modEq_one (D.g_modEq_one _)) hz
      g).elim (by simp [pow_eq_pow_of_modEq ((D.g_modEq_one _).pow _) hz]))
    refine normLength_defect_le hD.isPotCrys ?_ (tame_types_exponent (Γ :=
      ⟨Γ⟩) hj.1 G hD Y (hj.complexEmbOf_eq_iff.2
      (G (_ / 1)) ▸ W ·) (by grw [sub_le, a]; split <;> use D.nat_lt_of_hasLogBound))
    grw [finrank_linearMap_self, loss, ← one_le_padicValNat_of_dvd out, ← le_self_add, X]
    gcongr; rify; use D.le_of_hasLogBound
    clear * -; revert n; simp [gProd]
  let F := (coeffEmb O · ζ)
  have C {g g' k} (this : F g' = F g ^ k) :=
    cycCharMod_eq_iff.1 (cycCharMod_eq_of_isPrimitiveRoot (g := g' * g⁻¹) (.map_of_injective
    (.coe_submonoidClass_iff.2 z) g.injective) (by simpa [coeffEmb, F, ← map_pow]))
  let w z g := ite (ℓ ∣ D.cycloConductor) (.mk (complexEmbOf e g) ∈ D.thick) (F g = z)
  have u h := un fun _ ↦
    (hj.2 _).2 ∘ fixes_emb_of_fixes_rootsOfUnity ∘ apply_eq_self_of_mem_inertiaGroup h
  have σ h g g' (H : F g = F g' ^ 1) :=
    hj.complexEmbOf_eq_iff.2 (k.chart_isChartOf _ ⟨(fixes_roots_iff_fixesLambda (g * g'⁻¹)).1
    (by simpa using C H), sub_eq_iff_eq_add.2 (u h).1 ▸ by simp [k.theta_E]⟩)
  refine crystalline_defect_le (Γ := ⟨Γ⟩) _ D.m D.h₂ (finrank O (L c) * D.m / (D.k * x))
    D.nat_le_of_hasLogBound D.nat_le_of_hasLogBound D.nat_le_of_hasLogBound
    D.nat_le_of_hasLogBound D.lt_of_hasLogBound (by grw [sub_le, a]; use D.nat_lt_of_hasLogBound)
    D.nat_le_of_hasLogBound (W · |>.1) (fun g _ h ↦ (W g).2 _
    (filter_subset (jump (L c).tateDual.ρ g · ≠ 0) _ h)) (hD.imp_right (by simp +contextual)) ?_ (by
    simp [loss, finrank_linearMap]; grw [cast_div_le, cast_div_le, ← X]; field
    norm_cast; clear * -
    lia) k ⟨ζ, by erw [card_units, card_flatFq, z.1]⟩ (∃ g, .mk (complexEmbOf e g) ∈ D.thick ∧
    F g = ·) (cmSign ∘ complexEmbOf e ∘ epsilon ∘ w) hj.1 he (by
    grw [Nat.le_mul_of_pos_right k.e k.f.pos, he, hj.index_eq_card_range, Finite.card_subtype_le]
    simpa [Embeddings.card, finrank_eq_two_mul_card_infinitePlace] using D.nat_le_of_hasLogBound)
    (fun g H ↦ by clear * - R σ H N C; grind [cmSign_eq_of_thick, @epsilon_spec _ (w (g ζ)) (by
    grind)]) (if h : _ then .inr ⟨N h, by simp [w, h]⟩ else .inl ⟨u h, le_of_not_ge (h ∘ (dvd_trans
    · (.trans (by cbv) ((P.3.mul_right _).mul_right _))) ∘ hp.out.dvd_primorial_iff.2)⟩) (by
    rintro h _ a p b q ⟨_, c, ⟨⟩⟩ ⟨_, _, E⟩ ⟨_, v, B⟩
    rcases (pow_sub_one_mul out _).trans (apply_eq_pow_of_isFrob hy (not_dvd_ordCompl hp.out out)
      ((P.isPrimitiveRoot_zeta.pow_of_dvd out (ordProj_dvd ..)).map_of_injective
      e.injective).1).symm,
      log_mono .refl hp.out.one_lt (D.nat_le_of_hasLogBound : D.h₂ ^ 3 ≤ (2 ^ D.s) ^ 12) with X
    simp [(hj.2 _).1 A, P.isPrimitiveRoot_zeta.ne_zero out, ← pow_mul 2] at *
    apply not_thick_of_short_arc c v (C B _ X) (C (by rwa [E, ← pow_mul, ← pow_add]) _ X)
      h <;> omega)
  cases c <;> [left; right] <;> simp [jump_tateDual H.isPotCrys, x,
    le_div_iff_mul_le, *] <;> clear W T H hD C
  exact fun g ↦ ⟨by grind [Int.units_natAbs], (hJ.card_low_le _).trans' (by
    gcongr; induction J _ using Multiset.induction <;> simp [Multiset.count_cons,
    Multiset.countP_cons, sub_eq_iff_eq_add, neg_eq_iff_eq_neg]; lia)⟩
  grind
