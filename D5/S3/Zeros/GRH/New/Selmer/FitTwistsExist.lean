/- GID: D5/S3/Zeros/GRH/New/Selmer/FitTwistsExist
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/FitTwistsExist
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.FitTwistsExist. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/FitTwistsExist.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.RowVolume
import D5.S3.Zeros.GRH.New.Selmer.TwistForRows
import D5.S3.Zeros.GRH.New.Selmer.RowsExist
import D5.S3.Zeros.GRH.New.Selmer.DenominatorBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! A twist with few congruences for each prime. For each prime ℓ and each identification of the
complex numbers with the algebraic closure of the ℓ-adic numbers there is a twist whose first m
powers have few congruences, and the denominators of projections to theta lifts and the divisibility
of ratios of Hecke values sum over all ℓ to at most `Data.B₀` per rank and dimension, resp. x^999
(`Data.IsFitFamily`). It is known that
denominators of projections to lifts give Selmer classes and that twisting lowers Selmer ranks.
Related work: Prasanna, Integrality of a ratio of Petersson norms, 2006 (after Ribet, 1976; Wiles);
Klosin, Congruences among modular forms on U(2,2) and the Bloch–Kato conjecture, 2009; Mazur–Rubin,
Ranks of twists of elliptic curves, 2010.

This file: Existence of twists, one per embedding, whose first m powers have few congruences. -/

open Submodule Data Polynomial Multiset Finset Real

/-- All data D have m-fold twists ϑ_ι, one for each prime ℓ and isomorphism ι: ℂ ≅ ℚ̄_ℓ, such that
the family (ϑ_ι^n) is fit (`Data.IsFitFamily`) for 1 ≤ n ≤ m.

A twist with few congruences for each prime. -/
lemma exists_isFitFamily {P} (D : Data P) : ∃ θ, D.IsFitFamily θ := by
  choose R' F' using fun {ℓ} {_ : ThePrime ℓ} {ι : PadicIso ℓ} (p : {p : D.Pair × D.LiftIndex //
    p.1.IsRankOne p.2}) ↦ exists_row_for_all_twists ι (isApt_rank_one 1 p.2) 1 (fun _ ↦ {0}) 1 (by
    have := (@isFiniteTypeAt_char ℓ _ _ D.E _ _ · 1 Unit _ _ continuous_one (by simp))
    simp_rw [← C_1]
    use! continuous_one <;> simp_all [IsTraceNondeg, Matrix.trace, ← Matrix.ext_iff, IsLabelledAt,
      ↓aroots_X_sub_C, isGoodAt_iff]) (by simp) (by use ?_, ?_, ⟨p.1.2, ?_⟩ <;> simp [← cons_zero,
         countP_cons] <;> grind [Pair.IsRankOne,
    Int.units_natAbs, !(D.nat_lt_of_hasLogBound : 2 * D.h₂ ^ 2 + D.t < D.w _ _)])
  choose R F using fun {ℓ} {_ : ThePrime ℓ} {ι} (a : _ × (D.finite_eigenPart _
    (D.goodForms _)).toFinset) ↦ exists_hasRow_auxPair ι ((Set.Finite.mem_toFinset _).1 a.2.2) a.1
  choose τ H using fun κ : PrimePadicIso ↦ @exists_mFoldTwist_selmerLengthLe _ D κ.1 ⟨⟩ ⟨κ.2⟩ _ _
    (·.getRight?.map 0 |> @RowBlockIndex _ 1) _
    (Sum.rec _ _) (Sum.rec (⟨_, F · |>.1⟩) (⟨_, F' · |>.1⟩)) ⌊D.r * rowBudget D κ.1⌋₊.succ
  choose s s' using fun T (hT : ∀ l ∈ T, Nat.Prime l) ↦ show ∑ l ∈ T, rowBudget D l * log l ≤ D.B₀ ∧
      ∑ l ∈ T, 9 * crudeUnit l D * log l ≤ D.x ^ 999 by -- the budgets, summed over the primes
    clear * - hT
    have L {a} : ∑ l ∈ T, padicValNat l a * log l ≤ log⁺ a := by grw [log_of_nat_eq_posLog,
      log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ subset_union_right,
      ← T.subset_union_left] <;> simp_all [Nat.factorization_def]
    push_cast [rowBudget, _root_.loss, lambdaLoss, crudeUnit, add_mul, @mul_assoc ℝ,
      sum_add_distrib, ← mul_sum]
    grw [L, sum_le_sum fun _ _ ↦ by grw [mul_comm, log_le_self (by simp)], sum_le_hasSum _ (by simp)
      (hasSum_coe_mul_geometric_of_norm_lt_one (by bound)), L, (exists_length_shaOdd_le
      ..).choose_spec.2.1, classNumber_le, L, L, prod_le_prod' (by simp; tauto), prod_const,
      Nat.card_Ioc, tsub_tsub_le_tsub_add, add_tsub_cancel_left]
    push_cast [↓log_of_nat_eq_posLog, sub_half, Nat.cast_natAbs, abs_discr_eq_rootDiscr_pow,
      finrank_eq_two_mul_card_infinitePlace]
    any_goals exact neg_one_lt_zero.le.trans (Nat.cast_nonneg _)
    exacts [⟨add_halves D.B₀ ▸ add_le_add D.le_of_hasLogBound D.le_of_hasLogBound,
      D.le_of_hasLogBound⟩, D.nat_le_of_hasLogBound, D.algebraMap_mem_cycloField]
  use τ, fun κ ↦ (@coprime_q_of_isAuxiliary _ _ _ ⟨⟩ _ (H κ ⟨1, .refl,
    D.nat_le_of_hasLogBound⟩).1.1).1, fun j ↦ ⟨_, s, fun κ ↦
    have := ThePrime.mk; ⟨denominatorLe_rowBudget _ _ (H ..).1 (D.range_goodLift_le fun q y a c k
      m ↦ dite (y = 0) (by simp [·]) (subset_span ⟨⟨⟨y, a.1⟩, rfl⟩,
      ⟨c, m, isApt_auxPair D _ j k, D.range_tupleIdem_le k⟩, _, D.lifts_auxLift _ a.2, _, _,
      F ⟨j, q, by simpa using mt (D.goodForms_inf_eigenPart_eq_bot (D.hasRigidLabels_spaceW j)
      (D.hasRigidLabels_spaceW ⟨_, D.nat_le_of_hasLogBound, .refl⟩) · |>.le a) ·⟩, by simp [auxPair,
      liftChar, twist_one_spec], (H ..).2.1 (.inl _)⟩)), fun p h ↦ denominatorLe_rowBudget _ _
      (H ..).1 (span_mono (forall_eq.2 ⟨by simp, ⟨_, trivialLift_mem_range_tupleProj_rank_one _ h,
      isApt_rank_one _ h, le_rfl⟩, _, LValueData.auxPair_lifts_trivialLift _, _, _, F' ⟨(p, j),
      h⟩, by simp [twist_one_spec], (H ..).2.1 (.inr _)⟩))⟩⟩, (.of_le s' fun _ ↦ H _ · |>.2.2 · · ·)
