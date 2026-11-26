/- GID: D5/S3/Zeros/GRH/New/Seesaw/SeesawTheorem
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/SeesawTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.SeesawTheorem. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/SeesawTheorem.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.FillingTheorem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Seesaw identity for a chain of theta lifts. For ramified columns φ and every twist, the
restricted definite chain of lifts of φ, with data of controlled support and denominators, is a
non-zero constant, independent of φ and the twist, times the indefinite chain of lifts of the
Poincaré series of φ, with jets giving size and divisibility and the series giving the filling of
the rows. Transfer of a Bessel or Fourier–Jacobi period under one theta lift is known, locally and
globally. Related work: B. Wang, Global theta lifting and periods associated to nilpotent orbits,
2025; Gomez–Zhu, Local theta lifting of generalized Whittaker models, 2014; Gan–Ichino, The
Gross–Prasad conjecture and local theta correspondence, 2016.

Unfolded periods as finite sums with controlled denominators. Each period in the seesaw unfolding is
a constant times a finite sum over cosets of a small level, weighted by reciprocals of stabiliser
indices that divide powers of the norm of the twist's conductor, so the coefficients of the definite
chain get no new denominators away from the conductor. Periods on definite groups as finite coset
sums weighted by inverse stabiliser orders, used for integrality, are standard, and the prime-power
index is an elementary remark on pro-q groups. Related work: Gross, Algebraic modular forms, 1999;
Hsieh–Namikawa, Bessel periods and non-vanishing of Yoshida lifts modulo a prime, 2015; X. Zhang,
Non-vanishing mod p of theta lifts for (O(2n+1), Mp(4n)), 2022.

This file: Seesaw identity for the chain of lifts, by downward induction with finite cuts. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Function Gf IsTopologicalGroup MeasureTheory MulAction ProbabilityTheory TensorChain

namespace Data

seal SmoothForm chain

variable {P} (D : Data P)

/-- Some compact open A ⊇ K_k gives each ϑ, n = ∏_Q Nv, a finite (A ∩ B_k)-stable set T of cosets of
𝒥_k = `Data.levelY` ϑ k, integral away from n (in K(g) if k = 0), whose multiplicity
`coverMultiplicity` divides a power
of n on T and where a stage-k function of a ramified column, y₀ ∈ K(g), is non-zero.
Here K_k = `Data.columnLevel` k, B_k = `Grading.besselFin`, K(g) = `Data.chosenLevel`.

Unfolded periods as finite sums with controlled denominators. -/
lemma exists_stage_cut k hk : let Y := gradingY k hk; ∃ A, IsLevel A ∧ D.columnLevel k ≤ A.comap
    Y.inclXFin ∧ ∀ ϑ, ∃ T : Finset (_ ⧸ levelY ϑ k), (∀ p : Y.besselFin, ↑p ∈ A → ∀ t, t ∈ T ↔ p • t
    ∈ T) ∧ (∀ ⦃x⦄, ⟦x⟧ ∈ T → x ∈ localLevel _ {w | ↑ϑ.levelNorm ∉ w.1} ∧ (k = 0 → x ∈ chosenLevel))
    ∧ ∀ x, (⟦x⟧ ∈ T ∨ ∃ φ ∈ D.ramifiedColumns, ∃ ξ y g, unfoldStage ϑ φ ξ y k hk.step Y (g, x) ≠ 0 ∧
    y 0 ∈ chosenLevel) → ∃ j, coverMultiplicity Y.besselFin A T ⟦x⟧ ∣ ϑ.levelNorm ^ j := by
  intro Y; simp_rw [← Subgroup.mem_iInf, ← Subgroup.mem_inf]
  obtain rfl | e := eq_or_ne k 0
  · exact ⟨D.chosenLevel, inferInstance, fun a h ↦ D.filling_fits.mem_stdPrincipalLevel_iff.2
      (D.filling_fits.finiteEquiv_inclX (1, a) ▸ D.columnLevel_zero_eq_comap.le h), fun ϑ
      ↦ have b := (by simp [levelOf_le_Kf.trans Kf_le_localLevel]); exists_cut_coverMultiplicity_dvd
        (levelY_le_chosenLevel ..) IsLevel.isCompact
      b (fun x a ↦ ⟨b a, 0, fun u b ↦ by simp_all [mul_mem, levelY_le_chosenLevel _ _ b]⟩) fun x ⟨_,
        _, _, _, _, e, _⟩ ↦ (D.filling_fits.exists_besselFin_mul_mem_of_ne_zero _ e :)⟩
  choose b β hb using Y.exists_isAdaptedAt
  have l {x y b β w} (h : Y.IsAdaptedAt y b β) (e : x.atPlace w = y.atPlace w) :=
    (hb x).ideleLogVal_eq h (by simpa)
  let Φ Q d i (w : ↥(star '' Q ∪ Q)) := ideleLogVal (β d i) w.1 - ideleLogVal (β 1 i) w.1
  have ⟨_, _, f, n⟩ :=
    Y.hasNearLines_zero (D.spansLattice_gradingY ..) le_rfl (x := 1) (Q := ∅) ⟨1, by simp⟩
  refine ⟨Kf .., inferInstance, fun _ ↦ (Y.inclXFin_mem_Kf (D.spansLattice_gradingY ..)
    D.piIdele_spec ·.2), fun ϑ ↦ exists_cut_coverMultiplicity_dvd levelOf_le_Kf (((Set.finite_Icc
    (-↑k) ↑k).image (componentOn _ ϑ.Q ∘ invFun (Φ ϑ.Q))).isCompact.mul isCompact_Kf) (by simp [e,
    Kf_le_localLevel]) (fun x ⟨_, ⟨y, _, rfl⟩, z, hz, d⟩ ↦ ⟨⟨fun w o ↦ by simp [← d,
    mem_Kf_iff.1 hz, not_or.1 (o <| D.levelNorm_mem_and_notMem_of_mem_Q ϑ · |>.1)],
    by simp [e]⟩, (ϑ.Q.eventually_all.2 fun w o ↦ (eventually_localCongruence_subset (((isOpen_Kw
    w).preimage (continuous_conj (x.atPlace w))).mem_nhds (by simp))).mono fun n H u (hu :
    u ∈ levelY ϑ k) ↦ H (pow_pow_mem_localCongruence (D.levelNorm_mem_and_notMem_of_mem_Q ϑ
    (.inl o)).1 (mem_localCongruence_zero.2 ⟨mem_Kf_iff.1 (levelOf_le_Kf hu) w,
    congrFun (mem_levelOf.1 hu).2 (.inr ⟨w, o⟩)⟩) n)).exists.imp fun n H u hu ↦ mem_Kf_iff.2 fun w ↦
    by_contra fun a ↦ a ?_⟩) fun x ⟨_, r, _, _, _, b, a⟩ ↦ (hasNearLines_of_unfoldStage_ne_zero ϑ _
    _ ⟨_, r⟩ a _ _ _ b).elim fun _ ⟨_, g, o⟩ ↦ by clear * - o n l g f hb; exact
    (g.exists_mem_besselFin (hb _) (by grind [l g, atPlace_componentOn, by
    simpa [funext_iff] using invFun_eq (f := Φ ϑ.Q) ⟨x, rfl⟩])).elim fun z a ↦ ⟨_,
    a.2, _, ⟨Φ _ x, by simp [Pi.le_def]; grind, rfl⟩, z, a.1, eq_mul_of_mul_inv_eq rfl⟩⟩
  simp [mem_Kf_iff.1 hz, ← d, mem_supportedOn.1 componentOn_mem_supportedOn w
    (a <| by simpa using H w · u hu) (a <| atPlace_star_mem_iff.1 <| by simpa using H _ · u hu),
    mul_mem, pow_mem (mem_Kf_iff.1 (levelOf_le_Kf hu) _)]

/-- Given a, some κ works for all ϑ, S: an admissible combination w of values of S (denominator 1,
size cutBound^k), fixed by linear maps inducing the level action on S, has ∫ z·lift^k(𝒫φ) = κL(w)
for ramified φ and linear L, if the integrable periods of z·`Data.unfoldStage` at (ξ, y), y₀ of
level g, y_m = 1, equal a(ξ)L(S(y)). -/
lemma exists_isAdmissibleComb_unfolding k l {X s} [Fintype X] (Y : Grading (D.spaceY k) _ X s) (hs :
  s = 2 * D.ϱ + 1 - k) (a : _ → ℂ) : ∃ κ, ∀ {ϑ} {M : ModuleCat ℂ} (S : (∀ i, _ ⧸ levelY ϑ i) → M),
  ∃ w, IsAdmissibleComb (fun y : ∀ i, localLevel _ {w | ↑ϑ.levelNorm ∉ w.1} ↦ S (⟦y · |>.1⟧)) .univ
  ϑ.levelNorm 1 (ϑ.Q = ∅) (D.cutBound ^ k) w ∧ (∀ (b : ∀ i, D.columnLevel i) (ω : _ →ₗ[ℂ] _),
  (∀ q, ω (S q) = S fun i ↦ (if _ : i < k then (D.gradingY i).inclXFin (b i) else 1) • q
  i) → ω w = w) ∧ ∀ (z : (D.spaceY k).Form (star (typeKernel (D.paramY k) _))) (φ :
  D.ramifiedColumns) (L : _ →ₗ[ℂ] _), (∀ ξ y, y (2 * D.ϱ + 2) = 1 → y 0 ∈ D.chosenLevel →
  let F := unfoldStage ϑ φ ξ y k l Y * z; Integrable F Y.ratBessel.qms → Y.ratBessel.qms[F] = a ξ *
    L (S (y ·))) → (D.spaceY k).quotMeasure[z * (liftChainY ϑ k (D.poincare φ)).1] = κ * L w := by
  subst hs; induction' k with k ih generalizing X a
  · exact ⟨a 1, fun S ↦ ⟨_, .single 1 trivial, by simp +contextual, fun z φ L H ↦ .trans
      (D.filling_fits.poincareMap.2 _ ▸ (D.filling_fits.integral_poincare _ le_rfl z.2).2 :)
      ((D.filling_fits.integral_poincare _ inf_le_left
      z.2).symm.elim (·.symm.trans <| (mul_comm _ z.1 ▸ H 1 1 rfl (one_mem _)) ·))⟩⟩
  choose A hA hA' T c₁ c₃ c₄ using D.exists_stage_cut k (by omega)
  let Y := D.gradingY k
  choose κ H₂ using fun ξ ↦ Y.exists_integral_eq_sum_over_cut A (a <| update ξ k ·)
  refine (ih (by omega) κ Y).imp fun _ H ϑ _ S ↦ (H fun y ↦ ∑ t ∈ T ϑ,
    (coverMultiplicity Y.besselFin A (T ϑ) t : ℂ)⁻¹ • S (update y k t)).imp fun w ↦
    .imp (·.bind 1 D.cutBound (fun y _ ↦ .of_eq_isOfFinOrder_smul (.of_sum (Quot.ind fun t a ↦
    div_mem_integralAway ((c₄ ϑ t (.inl a)).choose_spec.mul_left 1)) fun e _ ↦ ?_) (Quot.ind fun t
    a ↦ ⟨1, .one, _, trivial, ((one_smul ..).trans congr(S $(funext (apply_update (fun _ x ↦ ⟦x.1⟧)
    y k ⟨t, (c₃ ϑ a).1⟩)))).symm⟩)) dvd_rfl (by simp [pow_succ])) (.imp (fun H b ω e ↦ H b ω fun y ↦
    ?_) fun H z φ L G ↦ (isArrow_datumY ϑ (D.m_eq_two_mul_varrho_add_two ▸ l)).elim fun A B ↦ ?_)
  · refine .trans (by erw [mul_comm ?z.1, mul_smul_comm, ← smul_mul_assoc]; exact
      (A.integral_mul_formLift_swap B _ ((_ : ℂ) • _))) (H ?z φ L fun ξ y y₁ y₀ h ↦ (H₂ ξ (L <| S <|
      update (y ·) k ·) (isGeneric_unfoldStage ..)
      ?z.2.1 h (c₁ ϑ) (fun g e ↦ ne_zero_of_dvd_ne_zero (by simp [prod_eq_zero_iff]) (c₄ ϑ _ (.inr
      ⟨φ, φ.2, ξ, y, _, left_ne_zero_of_mul e, y₀⟩)).choose_spec) fun t i ↦ .trans ?_ (congrArg _
      ((Grading.integral_besselGroup_unfold _ _ _ (isGeneric_unfoldStage ..) _ z.2.1 (B _).1.2).elim
      fun j ↦ (·.trans (funext (apply_update (fun _ ↦ (⟦·⟧)) y k t.2) ▸ G _ _
      (by simp [Nat.ne_of_gt l, y₁]) (by cases k <;> simp [c₃ ϑ i, *]) j))))).trans (by simp))
    simp [unfoldStage_update]; rw [← integral_const_mul]; congr; ext; erw [mul_left_comm,
      B.coe_formLift]; rfl
  · grw [sum_le_card_nsmul _ _ 1, nsmul_eq_mul, ← Nat.card_eq_finsetCard,
      (relIndex_principalLevel_le D.piGBar_ne_zero).trans' (Finite.card_le_of_injective' (f :=
      fun t ↦ ⟦⟨t.1.out, by simpa [e, mem_Kf_iff, localLevel, Ideal.one_notMem] using (c₃ ϑ
      (by simp)).1⟩⟧) (fun _ _ d ↦ by simpa using QuotientGroup.eq.2 (D.chosenLevel_inf_trivialOn_le
      ϑ ⟨D.principalLevel_le_chosenLevel dvd_rfl (QuotientGroup.eq.1 d :), by
      simp [e]⟩)) (absurd · (have := Fact.mk D.piGBar_ne_zero; relIndex_ne_zero_of_isLevel _))),
      absNorm_piGBar, ← pow_mul, card_Y_le] <;> simp [m_eq_two_mul_varrho_add_two, NeZero.one_le,
      Nat.cast_inv_le_one, NeZero.pos]; omega
  simp [e]
  refine sum_equiv (toPerm _) (c₁ ϑ ⟨_, Y.snd_mem_besselFin (Y.inclX_mem_besselGroup _)⟩ (hA' (b
    k).2)) fun t _ ↦ congr(($(coverMultiplicity_smul _ _ t) : ℂ)⁻¹ • S $(update_eq_iff.2 ?_)).symm
  simp +contextual [le_iff_lt_or_eq]; rfl

/-- The seesaw identity: there is a non-zero complex number c such that for every twist ϑ some good
datum Ψ (`Data.IsGoodDatum`) has ι(𝒫(cφ)) = B^Ψ φ for all ramified columns φ; 𝒫 is the Poincaré
series, ι = `Data.ι` the chain of m theta lifts through the spaces Y_j, and B^Ψ = `Data.Bμ` the
chain
through the definite spaces X_j with finite datum Ψ, restricted to Y_m.

Seesaw identity for a chain of theta lifts. -/
lemma seesaw : ∃ c : ℂˣ, ∀ ϑ, ∃ Ψ, IsGoodDatum ϑ Ψ ∧ ∀ φ,
  ι ϑ (D.poincare ((c.1 • D.ramifiedColumns.subtype) φ)) = Bμ ϑ Ψ φ := by
  choose C hC using D.exists_isAdmissibleComb_reducedVacuum
  choose R B c A using D.exists_last_stage_map D.m_eq_two_mul_varrho_add_two
  choose T H using (unfoldStage_even · _ .refl _ (by simp [pairEvalY]; rfl) 1)
  choose a w s₁ s₂ G using D.exists_isAdmissibleComb_unfolding _ le_rfl
    (D.lastGrading D.m_eq_two_mul_varrho_add_two) (by omega) (c ∘ T)
  refine ⟨normUnit (a * C / (D.cutBound ^ (2 * D.m))), fun ϑ ↦ (D.exists_isGoodDatum_of_invariant ϑ
    (.normUnit_smul a NeZero.out ((s₁ fun q ↦ pure (evaluatedDatum ϑ (q · |>.out)) _).bind _ 1 fun
    y _ ↦ by simpa [evaluatedDatum_out] using hC ϑ _ (y · |>.2))) fun b a ↦ ?_).imp
    fun Ψ ↦ .imp_right fun e φ ↦ B (.trans (ext_inner_left ℂ fun Ξ ↦ ?_) congr(R $(e _)))⟩
  · simp; congr; apply s₂ _ b
    simp only [← Quotient.mk_smul_out, evaluatedDatum_out, twoKernelAction, TensorChain.map_pure]
    clear * - a
    exact fun q ↦ (pure_congr fun i hi ↦ by cases hi <;> simp (disch := lia) only [evaluatedDatum,
      translatedUpsilon, *, smul_eq_mul, ← Prod.mk_mul_mk, map_mul, pairEvalY, Module.End.mul_apply,
      dite_eq_left, dite_eq_right] <;> apply_rules [ArrowPair.finEval_inclXFin, map_one]).symm
  simpa [inner_smul_right] using! G _ ⟨_, Ξ.2.conj⟩ φ (innerₛₗ ℂ Ξ ∘ₗ R ∘ₗ lift
    (TensorChain.liftInPairs (D.liftKernel ϑ · |>.lift)) φ (_ + 1)) fun ξ y a b _ ↦
    (A _ Ξ (by simpa [a] using! H ξ ϑ φ y b)).trans (by simp [evaluatedDatum_out, chain₂])
