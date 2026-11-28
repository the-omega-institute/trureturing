/- GID: D5/S3/Zeros/GRH/New/Columns/LocalStatement
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/LocalStatement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.LocalStatement. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/LocalStatement.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Columns.SizeEstimates
import D5.S3.Zeros.GRH.New.Columns.MarkedPrimeType
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Scaled Hecke operators repair divisibility at inert primes pairing tops. Each lift may lose
divisibility at an inert prime p pairing two tops, but outside a sparse set of p the chain regains
the predicted power of p, up to about one lift's loss, on the image of scaled Hecke operators above
p applied once per lift, and this image has small index once enlarged by a p-power multiple of all
columns. Hecke operators passing through theta lifts, p-power scaling by weight and p-adapted lifts
at ordinary p are known. Related work: Rallis, Langlands' functoriality and the Weil representation,
1982; V. Lafforgue, Estimées pour les valuations p-adiques des valeurs propres des opérateurs de
Hecke, 2011; Z. Liu, Test Schwartz functions at p for theta lifts of Hida families, arXiv
2510.21644, 2025.

Divisibility of the chain of theta lifts at each prime. For each prime p and twist of conductor
prime to p, the chain is divisible by the predicted power of p, less an error, on a submodule of the
ramified columns whose index has mean exponent at most that error, and the errors times log p have a
small sum, which gives the divisibility side of the product formula. The p-integrality of single
theta lifts is known. Related work: X. Zhang, Non-vanishing mod p of theta lifts for
(O(2n+1),Mp(4n)), 2022; Berger, Arithmetic properties of similitude theta lifts, 2009; Prasanna,
Integrality of a ratio of Petersson norms, 2006.

Short columns span, and the size of all conjugates of the chain. Columns ramified at the level prime
N have nearly full dimension and are spanned by forms integral at all primes with all conjugates
small, and the untwisted chain of lifts enlarges squared norms of all conjugates by at most an
explicit factor, which gives the size side of the product formula. Algebraic modular forms as values
on lattice classes and short lattice bases are known. Related work: Gross, Algebraic modular forms,
1999; Greenberg–Voight, Lattice methods for algebraic modular forms on classical groups, 2014;
Minkowski, Mahler, short lattice bases (geometry of numbers).

This file: Scaled Hecke operator passes the chain; divisibility on its image at non-split primes.
Explicit bound for all conjugates of the untwisted chain of lifts. Chain of lifts is divisible by
predicted p-power on a submodule of small index. -/

open Polynomial Finset Gf Kernel Module Parameters Real Submodule

variable {P} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] {Λ} {ϑ : D.Twist} {Ψ}
  (H : Data.IsGoodDatum ϑ Ψ) (hQ : p.Coprime ϑ.levelNorm) {v} (hv : v ∈ Data.integralColumns) (hΛ :
  D.IsMarked Λ)

/-- For a set Λ of primes of E and an index j, the real number 𝔯·∑_σ `Data.lowColumns` j σ −
`Data.jetExponent` p j ev, the sum over the set ev of places inducing a prime in Λ. -/
noncomputable def Data.liftLoss Λ j := D.ceilLogM p * ∑ σ ∈ evenPlaces Λ,
  D.lowColumns j σ - D.jetExponent p j (evenPlaces Λ)

include H hQ

/-- Hecke transfer. For good Ψ, p prime to Q, l in a marked set, j < m, some c_i ∈ O_ι serve all
terms of Ψ: datum j is target-spherical at l, and ∑_{i≤𝔯} c_iT_{l,i}Cφ = p^δ·CT_{l,𝔯}φ for
l-spherical φ, C the chain of j+1 lifts, δ = `Data.deltaP` p. -/
lemma Data.IsGoodDatum.exists_hecke_transfer (hΛ : D.IsMarked Λ) l (hl : l ∈ Λ) (hw : _ ≠ l) j :
  ∃ c : ℕ → ℂ, (j < D.m → ∀ i, c i ∈ embValRing) ∧ ∀ x ∈
  Ψ.support, let C := chain (D.liftKernel ϑ) (translateDatum x) (j + 1); (∀ b ∈ maxCompactAt _ l,
    (D.liftKernel ϑ j).ω (1, b) (translateDatum x j) = D.translateDatum x j) ∧ ∀ φ ∈ levelSpace
    (smoothFormRep ..) (maxCompactAt _ l), ∑ i ≤ D.ceilLogM p, c i • heckeSplit (smoothFormRep ..)
    hw i (C φ) = (p : ℂ) ^ D.deltaP p • C (heckeSplit (smoothFormRep ..) hw (D.ceilLogM p) φ) := by
  obtain ⟨_, N, m, h, o⟩ := hp.1.pos, hΛ.not_dvd_gProd_mul_N, hΛ.p_mem hl,
    D.m_even.two_dvd.trans (hΛ.2 ⟨l, hl⟩).m_dvd_orderOf
  have q : l.q = (p ^ h) ^ 2 := by simp_all [q_eq_inert m (hΛ.2 ⟨l, hl⟩).1, pow_mul']
  have Q := l.2.notMem_of_isCoprime_of_mem hQ.cast m
  simp [← l.natCast_mem_iff_dvd m, ← piGBar_mul_star, l.2.mul_mem_iff_mem_or_mem] at N
  have hu {j k} : CharUnramifiedAt (rankTwist (D.chainChar ϑ j) (D.X k)).baseChange.finPart l := by
    apply D.hasWeight_liftChar.hasWeight_rankTwist.charUnramifiedAt <;> simp_all [liftTamePart, ω,
      IsChosen, TameChar.pow, ϑ.1.5, mt (D.levelNorm_mem_and_notMem_of_mem_Q ϑ ∘ .inl)]
  let y e i : ℂ := ((p ^ h) ^ D.n (j + 1) / (p ^ h) ^ D.n e) ^ i * l.q ^ i.choose 2
  have I e : ‖ιₚ ((D.chainChar ϑ e).baseChange.atUnif l)‖ ≤ 1 := by
    erw [D.hasWeight_liftChar.norm_padic_eq_prod _ _ (unitary _).one_mem.2, ← rpow_zero p,
      hΛ.sum_inducedPlace_sub_star_eq_zero e fun c w ↦
      ite (w = l) (-c) 0, rpow_sum_of_pos (by simpa)]; gcongr with τ
    have f σ : ‖adeleExtension σ (locIdele l (uniformizer l)).1‖ = ‖adeleExtension (F := ℂ_[p]) σ
      (ite (placeOfEmb σ = l) p 1)‖ := by split <;> subst_vars <;> simp [*,
      ↓norm_adeleExtension_eq_iff, ← hΛ.valuation_p hl, ← v_algebraMap_eq_valuation]
    erw [map_mul, adeleExtension_star, inducedPlace, ← placeOfEmb_comp_star]
    simp [f]; split_ifs <;> simp_all [norm_p_eq_inv, NeZero.ne]
  refine ⟨_, fun hj i ↦ ?_,
    fun x i ↦ have z {j} := D.projOn_translateDatum (j := j) (S := {l}) (D.mem_integralAfter
    (H.support_subset x i) (by simp_all [star_eq_iff_star_eq, IsChosen,
      l.2.mul_mem_iff_mem_or_mem])); ⟨by simp_all [Subtype.ext_iff, liftKernel_ω, -Prod.mk_one_one,
      pairWeil_eq_smul_of_projOn_eq {l}, hu.det_maxCompactAt_eq_one], fun φ u ↦ by
    have S e : let F := chain (D.liftKernel ϑ) (D.translateDatum x) e; F φ ∈ levelSpace
        (smoothFormRep ..) (maxCompactAt _ l) ∧ ∀ U X, X = -U * y e 1 →
        heckePolyOp (smoothFormRep ..) hw X (F φ) = (∏ a ∈ range e, ∏ k ∈ range (D.t + 1),
      (1 + .X * l.q ^ k • (p ^ h) ^ D.n j • C ⟨_, I a.succ⟩) : embValRing[X]).aeval U •
      F (heckePolyOp (smoothFormRep ..) hw (-U * y 0 1) φ) := by
      induction' e with e ih; simp [chain, compUpTo, u]
      refine (hecke_transfer_of_pairing (k := D.t + 1) (by clear * -; grind [card_X, n]) hu hu hw z
        _ _ (⟨_, rfl, lift_equivariant _ · · _ · |>.symm⟩) ih.1).imp_right fun E U _ o ↦ (E _).trans
        (.trans (congrArg _ (congrArg _ (ih.2 U _ ?_))) ?_) <;> simp [*, AutChar.frobValue, y, n,
        ↓spaceChar_rankTwist, ↓card_X, mul_smul, HeckeChar.atUnif, prod_range_succ_comm _ e]
      swap; congr! 3; all_goals field [NeZero.ne]
    simp [heckePolyOp, heckePolyEval, mul_smul, mul_pow, -map_prod] at S
    have S := congr((p ^ D.deltaP p / y 0 (D.ceilLogM p)) • $(sum_coeff_invOfUnit_smul_eq (r :=
      D.ceilLogM p) (by simp [coeff_zero_prod]) ?_ (S j.succ).2))
    simp [smul_sum, smul_smul, y, q, NeZero.ne, PowerSeries.coeff_mul_X_pow', apply_ite,
      ← sum_filter] at S ⊢
    convert S; all_goals clear * -; grind [n, (D.nat_le_of_hasLogBound : D.ceilLogM p ≤ D.k)]⟩⟩
  show ‖ιₚ _‖ ≤ 1; simp [norm_p_eq_inv]; grw [fun x : embValRing ↦
      @id (‖ιₚ x‖ ≤ 1) x.2,
    ← log_nonpos_iff (by bound)]
  simp (disch := positivity) [log_mul, log_div, (D.ceilLogM p).cast_choose_two ℝ, deltaP]
  grw [← D.n_mono hj, f, numInfPlaces, ← orderOf_le_card_univ, o,
    ← sub_nonneg]; simp; ring_nf; bound

/-- For good Ψ, p prime to the modulus of ϑ, marked Λ, x in the support of Ψ, and g_l in
`basicDoubleCoset` l i for some i ≤ 𝔯: ω(1, g) of the j-th datum multiplies gauges by at most
p^(∑_{l∈Λ} A_l + `Data.liftLoss` Λ j), A_l = `Data.markExponent` l. -/
lemma Data.IsGoodDatum.mem_raises {x} (h : x ∈ Ψ.support) j {g} (hc : ∀ l, ∃ i ≤ D.ceilLogM p,
  g l ∈ basicDoubleCoset _ _ i) : (D.liftKernel ϑ j).ω (1, atSplits hΛ.1 g) (translateDatum x j) ∈
  (D.liftKernel ϑ j).raises 1 1 (p ^ (∑ l ∈ Λ, markExponent l + liftLoss Λ j)) := by
  obtain ⟨N, p1 : 1 ≤ (p : ℝ)⟩ := hΛ.not_dvd_gProd_mul_N, mod_cast hp.1.pos; choose i hi hc using hc
  choose! J _ hJ using fun l h ↦ exists_subset_card_eq (le_card_of_mem_basicDoubleCoset (hc ⟨l, h⟩))
  choose a ha b hb e using fun l : Λ ↦ DoubleCoset.mem_doubleCoset.1
    ((basicDoubleCoset_eq (diagGL_mem_basicDoubleCoset (ϖ := .mk0 p NeZero.out)
    (by simp [← v_algebraMap_eq_valuation, ← hΛ.valuation_p l.2]) _).1).le (hJ _ l.2 ▸ hc l))
  simp [funext e, ← Pi.mul_def]
  refine Parameters.mem_raises_of_jet_bound (δ := 1) (H.translateDatum_mem_standardData hQ N.2.1 h j
    (.inr N.1)) (Kf_le_localLevel ?_) (Kf_le_localLevel ?_) (fun _ ↦ (?_ : ∀ w (f : _ →+* ℂ_[p]),
    (atPlace w _).1.map f = .diagonal fun i ↦ p ^ (ite (w ∈ Λ ∧ i ∈ J w) 1 0 - ite (⟨star w,
    i⟩ ∈ Λ.sigma J) 1 0 : ℤ)) _ _) ?_ <;> first | rwa [atSplits_mem_Kf] | clear * - hΛ p1 hJ hi
  intro w; by_cases w ∈ Λ <;> by_cases star w ∈ Λ <;> simp_all [apply_ite, hΛ.1,
    ← map_inv, atPlace_star (star_star w), atPlace_atSplits _ _ ⟨_, _⟩,
    mem_supportedOn.1 (atSplits_mem_supportedOn _ _)]
  intro _ hf _ _; obtain ⟨_, _, u, v, H⟩ := P.thetaProducts_normal_form _ hΛ.4.2
  grw [show ‖ιₚ (schurJet _ _ _ _)‖ ≤ p ^ (_ - D.jetExponent p j _) from norm_jetSeries_le hf _
    (.proj _ ∘ₗ .proj _ ∘ₗ schurJet _) (r := p ^ (_ : ℝ)) fun Θ h ↦ by
    erw [map_schurJet (isLiftWeight_kappa ..)]; simp_rw [jetExponent,
      ← card_X]; exact norm_schurJet_le (ev := evenPlaces Λ) (isLiftWeight_kappa ..).1 u v
      ((fun w h b ↦ ite (w ∈ Λ ∧ h = 1 ∧ b ∉ J w ∨ ⟨star w, b⟩ ∈ Λ.sigma J) 1 0) ∘ inducedPlace) (by
      grind [IsMarked, IsServed, chiK_cases, inducedPlace_neg_pow_mul_of_odd, star_star]) ((H _ (by
      simpa [P.norm_iota_periodFactor_eq_one _ (hΛ.4.2 ∘ P.chiK_eq_one_of_dvd Fact.out)] using
        norm_star_piG_le_one) _ h).1 _), ← zero_add (Λ.sum _),
    hΛ.sum_inducedPlace_sub_star_eq_zero (j + 1) fun c w ↦ #(J w) * ((D.n j / 2 : ℤ) - c)]
  simp (disch := positivity) only [norm_zpow, norm_p_eq_inv, inv_zpow', ← rpow_sum_of_pos, add_sub,
    markExponent, ← rpow_intCast, lastEntry, sum_filter, ← rpow_mul, placeOfEmb_comp_star,
    ← rpow_add, push_cast, ← inducedPlace.eq_1, liftLoss, lowColumns, mul_sum, card_filter,
    ← sum_ite_mem_eq D.tops, ← sum_add_distrib, Λ.sum_comm]
  clear hf H; gcongr _ ^ (∑ τ, ?_ - _)
  by_cases inducedPlace τ ∈ Λ <;> by_cases star (inducedPlace τ) ∈ Λ <;> simp_all [hΛ.1,
    add_assoc]; norm_cast
  rw [show ite .. = ∑ h ∈ range (D.n (j + 1)), ite (h = 1) (D.κ τ h) 0 by simp [κ, n]; grind]
  simp_rw [mul_sum, ← card_X, sum_range, ← sum_add_distrib]; gcongr
  split <;> simp [*, card_filter_add_card_filter_not]
  exact (sum_le_sum fun _ _ ↦ card_le_card_of_injOn _ (mem_filter_univ · |>.1)
    (tableau_col_injective ..).injOn).trans (by simp [*]; grw [hi]; lia)

/-- For L listing distinct primes of Λ, some linear t commutes on the j-th data with G_f × K_0; for
j < m, lifting by t·datum equals lifting after ∏_L Y_l, and Hecke translates off L raise as in
`Data.IsGoodDatum.mem_raises`, with ∑_L(δ_p − A_l) added to the exponent of p. -/
lemma Data.IsGoodDatum.exists_move_markOperator j {L : List Λ} (hn : L.Nodup) : ∃ t : End ℂ _,
  ∀ x ∈ Ψ.support, let Φ := t (translateDatum x
    j); let k := D.liftKernel ϑ j; let C := chain (D.liftKernel ϑ) (translateDatum x)
      (∀ a, ∀ b ∈ Kf .., k.ω (a, b) Φ = t (k.ω (a, b) (translateDatum x j))) ∧
        (∀ y, k.lift Φ (C j y.1) = C _ ((L.map hΛ.markOperator).prod y)) ∧ ∀ g, j < D.m →
        (∀ l, ite (l ∈ L) (g l = 1) (∃ i ≤ D.ceilLogM p, g l ∈ basicDoubleCoset _ l.1 i)) →
        k.ω (1, atSplits hΛ.1 g) Φ ∈ k.raises 1 1 (p ^ ((L.map fun l ↦ (D.deltaP p -
        markExponent l.1 : ℝ)).sum + ∑ l ∈ Λ, markExponent l + liftLoss Λ j)) := by
  induction' hn with l L hl _ ih
  use 1, fun x h ↦ ⟨by simp, by tauto, fun _ _ ↦ by simpa using H.mem_raises hQ hΛ h j⟩
  choose t e f ih using ih; have z := hΛ.star_ne l.2
  choose a ha u k using H.exists_hecke_transfer hQ hΛ _ l.2 z j
  let ρ := (D.liftKernel ϑ j).ω.comp (.inr ..); let s : ℂ := p ^ markExponent l.1 / p ^ D.deltaP p
  use (∑ i ≤ D.ceilLogM p, (a i * s) • heckeSplit ρ z i) * t; intro x r
  have h :
    t (D.translateDatum x j) ∈ levelSpace ρ (maxCompactAt _ l.1) := by simp +contextual [ρ, *]
  use fun a b c ↦ ?_, fun y ↦ ?_, fun g hj hc ↦ ?_
  simp [← e x r, c, ρ, by simpa [Kernel.ω_ω] using
    (map_heckeSplit z · ((D.liftKernel ϑ j).ω (a, 1)) (π' := ρ) (by simp [Kernel.ω_ω]) |>.symm.trans
    (congrArg _ (heckeSplit_comm_of_atPlace_mem z _ h (mem_Kf_iff.1 c l))))]
  refine .trans ?_ ((k x r _ (levelSpace_anti (hΛ.maxCompactAt_le_columnLevel l.2)
    (s • (L.map hΛ.markOperator).prod y).2)).trans ?_) <;>
    simp [← f x r, smul_smul, s, NeZero.ne, mul_div_cancel₀, IsMarked.markOperator]
  congr!; exact map_heckeSplit _ _ ((D.liftKernel ϑ j).lift.flip _) (by simp [ρ,
    ← lift_equivariant _ 1])
  simp [heckeSplit, heckeGL, heckeFun_sum, smul_sum]; refine sum_mem fun i c ↦ sum_mem fun k h ↦ ?_
  simp at h; simp [h, Kernel.ω_ω, ρ, ← map_mul,
    ← @id (atSplits hΛ.1 _ = _) (MonoidHom.noncommPiCoprod_mulSingle ..)]
  refine smul_mem_raises _ (ih x r _ hj ?_) ?_
  simp [Pi.mulSingle, Function.update]; clear * - hc h hl c; grind
  simp [s, rpow_add, rpow_sub, NeZero.pos, norm_p_eq_inv]
  grw [@id (‖ιₚ (a i)‖ ≤ 1) (ha hj i)]; simp [field]

/-- For good Ψ, p prime to the modulus of ϑ, marked Λ, Y the product of the
`Data.IsMarked.markOperator` l in a chosen order, and v an integral column, B_μ(Y^m v) has gauge at
most p^c everywhere, c = ∑_{j<m} (#Λ·δ_p + `Data.liftLoss` Λ j). -/
lemma Data.IsGoodDatum.gaugeLe_markOperator_pow {v} (hv : v ∈ integralColumns) :
  GaugeLe 1 (p ^ ∑ j ∈ range D.m, (#Λ * D.deltaP p + liftLoss Λ j))
  (Bμ ϑ Ψ (((Λ.attach.toList.map hΛ.markOperator).prod ^ D.m) v)) := by
  choose t A B C using (H.exists_move_markOperator hQ hΛ · Λ.attach.nodup_toList)
  have k x (h : x ∈ Ψ.support) j : chain (D.liftKernel ϑ) (fun j ↦ t j (D.translateDatum x j)) j v =
    chain (D.liftKernel ϑ) (D.translateDatum x) j (((Λ.attach.toList.map hΛ.markOperator).prod ^ j)
    v) := j.rec rfl fun j i ↦ by simp [pow_succ', ← B j x h, ← i]; rfl
  apply GaugeLe.restrictToY D hΛ.not_dvd_gProd_mul_N.2.1
  simpa +contextual [Finsupp.sum, k, -sum_add_distrib] using! H.gaugeLe_chain hQ t (by
    simp +contextual [A, (D.isLevel_columnLevel.1 ·)]) 1 (fun x h j ↦ by
    simpa [← Nat.cast_sum, sum_attach, -List.map_subtype] using C j x h 1) hv.2

omit H hQ

/-- Size bound. Let Ψ be good for the trivial twist, σ in Aut ℂ. If a column φ has ‖σφ‖² ≤ e^B
everywhere, then ‖σB_μφ‖² ≤ exp(B + h₀ + 2∑_p gain(p) log p + fa(log b)³) everywhere, p < x₁
non-split, h₀ = `Data.heightPerRow`. -/
lemma Data.weylNormSq_Bmu_le (H : IsGoodDatum 1 Ψ) {σ : ℂ ≃+* ℂ} {φ B} (hB : ∀ g,
  weylNormSq (σ ∘ φ.1.1 g) ≤ exp B) h : weylNormSq (σ ∘ (D.Bμ .one Ψ φ).1 h) ≤
  exp (B + D.heightPerRow + 2 * ∑ p ∈ D.nonsplitPrimes, D.gain p * log p + D.budget) :=
  (D.weylNormSq_restrictToY_le σ ..).trans ((exists_chain_eq_sum H.joint_invariant (fun _ _
  y ↦ √(weylNormSq (σ ∘ y))) (by bound) (fun _ _ _ _ _ _ ↦ (P.norm_jet_le_of_isAdmissibleComb
  (.single _ ⟨⟩) ..).2 D.a.succPNat (isLiftWeight_kappa ..)) (by bound) _).elim fun f e ↦ by
  erw [← sq_sqrt (weylNormSq_nonneg (σ ∘ _)), ← e.2]
  grw [← le_branchExp, sqrt_weylNormSq_sum_le, sqrt_weylNormSq_sum_le]; simp
  grw [e.1 _ _ ‹_›, ← sum_mul, Fin.sum_const, nsmul_eq_mul, (id (H.size_le rfl σ) : Ψ.1.sum _ ≤ _),
    Nat.cast_prod, prod_range, prod_range,
    D.card_stdClasses_le_exp (principalLevel_le_columnLevel ..) (by simp [↓card_X, n])]
  simp [-sum_add_distrib, ← exp_sum, ← exp_half, ← exp_add,
    ← exp_nsmul, ↓card_X, ↓norm_map_star_piG_sq,
    ← inv_div (P.bigOmega _), -inv_div, ← sub_eq_add_neg, ← add_sub, ← jetSize.eq_1, n]
  grw [nonsplitPrimes, ← filter_filter, sum_filter_of_ne fun _ _ ↦
    mt fun h ↦ by simp [gain, forcedPart, localAsk, h],
    ← tsub_le_iff_left, sum_le_sum fun (j : Fin D.m) _ ↦ have := D.hasLogUpper_of_le j.2.le; by
    grewrite [jetSize_le_add _ (D.diagramWeight_le_by_index j.2 ..),
      D.diagramWeight_le_by_index j.2, show ite .. + _ ≤ 2 * D.a by grind [κ,
      (D.nat_le_of_hasLogBound : D.b₁ + D.b₂ + D.h₂ + D.h₂ ^ 2 ≤ D.a)], (?_ : _ - _ ≤ ↑D.m)]
    simp [← mul_sum, ↓apply_ite D.jetSize, jetSize, sum_ite, filter_ne', ← Nat.Ico_zero_eq_range]
    grw [(?_ : _ * _ + _ ≤ D.b), (?_ : D.k + _ ≤ √D.b)]
    repeat use D.le_of_hasLogBound]
  simp [heightPerRow, dirCost, jetSize, (D.le_of_hasLogBound : D.nominalWeight _ ≤ D.a), gain,
    forcedPart, κ, apply_ite, ← mul_sum, sum_mul, add_mul, mul_assoc, (filter ..).sum_comm,
    D.primeSum_eq_sum_localAsk .refl, -tsub_le_iff_right]; ring; use D.le_of_hasLogBound)

seal Space.weightRep Space.embFin

/-- For marked Λ, Y = ∏_{l∈Λ} `Data.IsMarked.markOperator` l and M the integral columns: Y^m keeps
M, and [M : Y^m M + p^{j_p} M] divides p^c (`IndexDvd`) for some natural
c ≤ 3·loss(p)·dim(columns). -/
lemma Data.IsMarked.hasType_prod_markOperator_pow : HasType ↑p integralColumns (D.jetCeil p)
  ((Λ.attach.toList.map hΛ.markOperator).prod ^ D.m) (3 * D.loss p * finrank ℂ D.Column) := by
  obtain ⟨_, _, h⟩ := hp.1.pos, D.hasLogUpper_of_le_of_nonneg hΛ.4.1.le, HasType.prod
    (List.replicate D.m Λ.attach.toList).flatten fun l _ ↦ hΛ.hasType_markOperator (D.jetCeil p) l.2
  simp [← sum_mul, ← mul_assoc, ← mul_sum, ← Nat.cast_sum, sum_attach, -List.map_subtype] at h
  refine ⟨h.1, h.2.imp fun _ ↦ .imp_left (le_trans' ?_)⟩; erw [← mul_sum]
  grw [hΛ.card_le, sum_card_fiberwise_eq_card_filter, ← le_loss, jetCeil, Nat.ceil_lt_add_one]
  gcongr ?_ * _; field; use D.le_of_hasLogBound; bound

include H hQ hv

/-- Let Ψ be good for ϑ, and p a prime prime to the primes of ϑ, p ≠ N, p ≠ d. If the column v
is integral at ιₚ, so is B_μ v. -/
lemma Data.IsGoodDatum.gaugeLe_one (hN : p ≠ D.N) (hd : p ≠ P.d) : GaugeLe 1 1 (Bμ ϑ Ψ v) :=
  GaugeLe.restrictToY D hN
  (by simpa using H.gaugeLe_chain hQ 1 (by simp) 1 (r := 0) (fun _ a _ _ ↦ by
  simpa [((p.coprime_primes hp.1 P.4).2 hd).norm_natCast_eq_one] using! P.mem_raises_of_standardData
    (c := star D.piG) (by simp) (H.translateDatum_mem_standardData hQ hN a _ (.inl rfl))) hv.2)

/-- For Ψ good, p prime to the twist, Λ full (`Data.IsFullMark`), Y the product of the
`Data.IsMarked.markOperator` l, l ∈ Λ, and v an integral column, B_μ(Y^m v) has valuation at
least gain(p) − 2·loss(p). -/
lemma Data.IsGoodDatum.gaugeLe_Bmu_of_isMarked (hΛ : D.IsFullMark Λ) : GaugeLe 1 (p ^ (2 * D.loss
  p - D.gain p)) (Bμ ϑ Ψ (((Λ.attach.toList.map hΛ.markOperator).prod ^ D.m) v)) := fun g ↦ by
  grw [H.gaugeLe_markOperator_pow hQ hΛ.1 hv g]; simp_rw [liftLoss, add_sub]
  grw [hΛ.sum_lowColumns_le (by grind), ← le_jetExponent (by grind) hΛ.nonsplit,
    le_loss] <;> simp [hΛ.collisionSum_evenPlaces_eq_zero, field, hp.1.one_lt, hp.1.one_le,
    m_eq_two_mul_varrho_add_two, (hΛ.served (by grind [hΛ.2 1 (by simp [tops])])).1]; linarith

/-- Let Ψ be good for ϑ, p < x₁ non-split and prime to the primes of ϑ. For a column v integral
at ιₚ, B_μ v has valuation at least gain(p) − loss(p) − m·`Data.collisionSum` p ∅. -/
lemma Data.IsGoodDatum.gaugeLe_collisionSum (h : D.IsSmallNonsplit p) :
  GaugeLe 1 (p ^ (D.m * D.collisionSum p ∅ + D.loss p - D.gain p)) (Bμ ϑ Ψ v) := fun g ↦ .trans
  (by simpa [liftLoss] using H.gaugeLe_markOperator_pow hQ (Λ := ∅) (by grind [IsMarked]) hv g) (by
  grw [← le_jetExponent (by aesop) h, ← le_loss] <;> simp [hp.1.one_lt, hp.1.one_le, field,
    evenPlaces, m_eq_two_mul_varrho_add_two])

/-- Let Ψ be good for ϑ, p < x₁ non-split and prime to the primes of ϑ. For a column v integral
at ιₚ, B_μ(p^{j_p} v) has valuation at least gain(p) − loss(p), with j_p = `Data.jetCeil`. -/
lemma Data.IsGoodDatum.gaugeLe_pow_jetCeil_smul (h : D.IsSmallNonsplit p) :
    GaugeLe 1 (p ^ (D.loss p - D.gain p)) (Bμ ϑ Ψ ((p : ℂ) ^ D.jetCeil p • v)) := fun g ↦ by
  erw [map_smul, weylGauge_smul]; grw [jetCeil, H.gaugeLe_collisionSum hQ hv h g,
    collisionSum_le (·.1.1), Nat.le_ceil (D.m * _ : ℝ)]
    <;> simp [norm_p_eq_inv, add_sub_assoc, rpow_add, hp.1.pos, hp.1.one_le, NeZero.ne]

omit H hQ hv

/-- For an integer β < gain(p) − err(p) + 1 (err = `Data.allowedLoss`; gain omitted unless p < x₁ is
non-split), some O_ι-module S of columns has index (`IndexDvd`) dividing p^l, l ≤ err(p)·dim, in the
ι-integral columns, and v(B_μφ) ≥ β for ramified φ ∈ S, all twists with Q prime to p, all good Ψ.

Divisibility of the chain of theta lifts at each prime. -/
lemma Data.exists_indexDvd_Bmu_divisible {β : ℤ} (hc : β < ite (p ∈ D.nonsplitPrimes) (D.gain p) 0 -
  D.allowedLoss p + 1) : ∃ l : ℕ, l ≤ D.allowedLoss p * finrank ℂ D.Column ∧ ∃ S,
  IndexDvd integralColumns S (p ^ l) ∧ ∀ ϑ Ψ, IsGoodDatum ϑ Ψ → p.Coprime ϑ.levelNorm → ∀ φ
  ∈ S, φ ∈ D.ramifiedColumns → (p : ℂ) ^ (-β) • Bμ ϑ Ψ φ ∈ integralFormsAt ⊤ 1 := by
  have k {ϑ Ψ φ} {c : ℝ} (h : GaugeLe 1 (p ^ c) (D.Bμ ϑ Ψ φ)) (e : c ≤ -β := by linarith) :
      (p : ℂ) ^ (-β) • Bμ ϑ Ψ φ ∈ integralFormsAt ⊤ 1 := ⟨⟨⟩, fun g ↦ by
    erw [weylGauge_smul]; grw [h g, e] <;> simp [norm_p_eq_inv, rpow_neg, NeZero.one_le, NeZero.ne]⟩
  unfold allowedLoss at *; split_ifs at * with h hN <;> simp [Nat.lt_ceil, hp.1] at h; swap
  · subst hN; have : 1 ≤ D.m * D.f * D.b :=
      D.le_of_hasLogBound; peel D.exists_indexDvd_fourierOp_pow
    exact ⟨_, this.comap _ le_rfl fun _ _ ↦ mem_comap.2, fun _ _ G _ _ c r ↦
      k (D.gaugeLe_Bmu_at_N _ G r c)⟩
  have := D.hasLogUpper_of_le_of_nonneg h.1.le; have :=
    D.le_of_hasLogBound (F := 1).trans (D.le_loss p)
  obtain ⟨Λ, hΛ⟩ | s := (em _).imp (D.exists_isMarked h.1) (mul_collisionSum_le_loss h)
  · peel hΛ.hasType_prod_markOperator_pow.2; refine ⟨_, this, fun _ _ G Q _ e _ ↦ ?_⟩
    obtain ⟨_, ⟨u, U, rfl⟩, _, ⟨v, V, rfl⟩, rfl⟩ := mem_sup.1 e
    simpa using!
      add_mem (k (G.gaugeLe_Bmu_of_isMarked Q U hΛ)) (k (G.gaugeLe_pow_jetCeil_smul Q V h))
  all_goals use 0, mod_cast by bound, D.integralColumns, by simp, fun _ _ G Q φ c _ ↦ ?_
  exact k (G.gaugeLe_collisionSum Q c h)
  exact k (rpow_zero _ ▸ G.gaugeLe_one Q c hN
    (by rintro rfl; simpa [chiK] using h D.lt_of_hasLogBound)) (by norm_cast at *; lia)
