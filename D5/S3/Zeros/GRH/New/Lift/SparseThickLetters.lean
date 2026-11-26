/- GID: D5/S3/Zeros/GRH/New/Lift/SparseThickLetters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/SparseThickLetters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.SparseThickLetters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/SparseThickLetters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Lift.LongGap
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Rank-free exponents for crystalline classes at large weights. For crystalline lattices with
weights in short windows near 0 and near large weights (no small negative weight, two sizes, or
sparse large weights), an explicit power of p (ℓ in the Selmer bound),
independent of the rank, makes crystalline classes
cup to zero with those of congruent dual lattices, which bounds the loss above ℓ in the Selmer
bound. The question, the case of small weights and a rank-free factorial torsion bound by Sen
operators are known. Related work: Gao–Liu, Integral filtered Sen theory and applications, 2024;
Iovita–Marmora, Continuity of the finite Bloch–Kato cohomology, 2015; Y. Min, Congruences of first
syntomic cohomology groups, 2026.

Part of: Tame types: exponent independent of the ramification index (see New.Lift.ExponentTheorems).

This file: Polynomial in tame generator kills cokernel of Kisin modules independently of
ramification index. Kummer chart of a tame extension of Q_p with a generator of tame inertia.
Rank-free exponents killing cup products for two sizes and sparse thick letters. -/

namespace Lift

open KummerChart JumpLattice WittVector Submodule FrobGroup Module Finset Polynomial LinearMap
  PairingSide algebraMap
variable {p : outParam ℕ} [ThePrime p] (Γ : outParam (GroupOverGp p))

/-- A tame Kummer chart: Γ' is normal, p ∤ e, j(Γ') fixes some ϖ with ϖ^e = p, and some s in
inertia has s^k z = ξ^k z, ξ ∈ Λ of order e modulo p. -/
class TameChart extends KummerChart Γ where
  (zetaE : WittFq f) (tameGen : Γ) primitive : IsPrimitiveRoot (zetaE.coeff 0) e
  tameGen_pow_smul_z k : toGp (tameGen ^ k) • chart.z.1 = ↑(zetaE ^ k) * chart.z
  (isWeilPair_tameGen : IsWeilPair (toGp tameGen) 0) fixesLambda_tameGen_pow k :
    FixesLambda f (toGp (tameGen ^ k))
  (ϖ) apply_varpi (g : Γ') : toGp g.1 ϖ = ϖ
  (varpi_pow_eq : ϖ ^ e = p) (tame : ¬p ∣ e) [normal : Γ'.Normal]

namespace TameChart

variable [Γ] {d : TameChart Γ} {O} {L : d.JumpLattice O} {n m : ℕ} {q : ℤ_[p][X]} {S :
  PairingSide O} (hK : IsKilledBy S.ρ d.tameGen 0 (q.map (algebraMap _ O)))

/-- For a tame chart and q = ∑ a_k X^k in Z_p[X]: if q(β_{s,0}) = 0 on B ⊗ L (β = `linearFrob`,
s = `tameGen`), then ∑ a_k s^k
maps the Kisin module N into z·M, with M = `Lift.KummerChart.JumpLattice.kisinAinf`. -/
lemma exists_z_smul_eq_sum_tameGen (r : aeval (linearFrob L.ρ d.tameGen 0) q = 0) {x} (hx : x ∈ L.kisinModule) :
    ∃ y ∈ L.kisinAinf, d.z.1 • y = ∑ k ∈ range (q.natDegree + 1), q.coeff k • inr (d.tameGen ^ k) • x :=
    have n g := (d.normal.1 · · g)
    frame_theorem.1.2.2.2.elim fun u v ↦ v _ d.z_dvd_of_dvd_E_pow_mul _ (by
    simp [↓sum_mem, ↓smul_of_tower_mem, ↓smul_mem_kisinAinf (n _) hx.1]) fun μ ⟨hl, l, E⟩ ↦ by
  let Λ g := (DistribSMul.toLinearMap _ _ (toGp g)⁻¹ ∘ₗ l ∘ₗ overZp L.ρ g).liftBaseChange Bcris
  have A g g' y : Λ g' (tensorAction _ (toGp g) (L.ρ g) y) = toGp g • Λ (g' * g) y := by
    clear * -; induction y <;> simp_all [Λ, tensorAction, mul_smul]
  have S : ∑ k ∈ _, q.coeff k • Λ _ = 0 := ext_on L.inClass.isPotCrys fun y b ↦ by
    simpa [← linearFrob_pow L.inClass.isPotCrys d.isWeilPair_tameGen, fun k ↦ linearFrob_apply (m := 0) L.inClass.isPotCrys (d.isWeilPair_tameGen.pow k) b ▸
      (A _ 1 _).trans ((d.isWeilPair_tameGen.pow k).smul_eq_of_fixed_nearOne (.mp b (d.nearOne_le fun g b ↦ .trans (by
      rw [A]; congr 2 with _
      simpa [Λ, E, mul_smul, eq_inv_smul_iff, -map_pow] using (conjForm_mem_forms (n _) hl _ g).symm)
      (congrArg _ b)))), aeval_eq_sum_range] using congr(Λ 1 ($r y))
  simpa [smul_sub, smul_comm (q.coeff _), ← smul_sum, by
    simpa using apply_eq_of_mem_fracSpan (∑ k ∈ _, q.coeff k • conjForm μ (d.tameGen ^ k)) 0 (by ext; simpa [basisValues, Λ, E, smul]
                                   using congr(($S (1 ⊗ₜ _) : BdR))) (kisinAinf_le_fracSpan hx.1)] using! sum_mem (t := range
    q.natDegree.succ) fun k _ ↦ smul_of_tower_mem _ (q.coeff k) (pow_smul_gal_sub_mem_span_of_dvd (d.z_dvd_sub (d.fixesLambda_tameGen_pow k))
    (u _ ⟨conjForm_mem_forms (n (d.tameGen ^ k)) hl, (liftBaseChangeEquiv _).2 (Λ (d.tameGen ^ k)), by simp [Λ, E]⟩ _ hx))

include hK

/-- Tame chart. If the polynomial q over Z_p kills (s, 0) on Y, then q·(X − 1) evaluated at
β_{s,0} vanishes on B ⊗ Ỹ, for the extension Ỹ of the trivial lattice C by Y. -/
lemma aeval_linearFrob_extLattice_eq_zero :
  aeval (linearFrob S.extLattice.ρ d.tameGen 0) (q * (X - 1)) = 0 := LinearMap.ext fun y ↦ by
  obtain ⟨x, e⟩ := (lTensor_exact _ .inl_snd snd_surjective (_ - y)).1 (by
    simpa [IsCrystalline.linearFrob_eq_one, isAdmissible_of_cyclotomicGp_zpow 0,
      isWeilPair_tameGen] using! baseChange_linearFrob S.extLattice.inClass.isPotCrys
      d.isWeilPair_tameGen S.trivLattice.inClass.isPotCrys _ (by simp [extensionRep]) y)
  simpa [← e, eval₂_map, coefEnd, aeval_def, q.eval₂_eq_sum_range, End.pow_apply,
  Function.Semiconj.iterate_right
    (baseChange_linearFrob hK.1 d.isWeilPair_tameGen S.extLattice.inClass.isPotCrys (inl ..)
  (by simp [extensionRep])) _ _] using! congr((inl _ _ S.C).baseChange _ ($(hK.2) x))

/-- Tame chart; S a side with jumps ≤ n, and a monic q over Z_p kills (s, 0) on Y. If e ≤ p^m, m(deg
q + 1) ≤ κ and n + κ + 2 < p, then p^κ kills the cokernel
(`Lift.KummerChart.PairingSide.KillsCokernel`) at every letter. -/
lemma killsCokernel_of_isKilledBy (hn : ∀ i, ∀ u ∈ S.U i, u ≤ n) (hq : q.Monic) (hm : d.e ≤
  p ^ m) {κ i} (hp : n + κ + 2 < p) (hc : m * (q.natDegree + 1) ≤ κ) : S.KillsCokernel i κ 0 := by
  obtain ⟨⟨ν, h₀, hν⟩, M⟩ := exists_z_pow_mem_liftIdeal hn κ.succ, hq.mul (monic_X_sub_C 1)
  replace hν : ν < d.e := by nlinarith [NeZero.pos d.e]
  set Q := q * _
  replace h₀ := smul_mem _
    (p.cast ^ (m * #{k ∈ Ico ν.succ d.e | (aeval (d.zetaE ^ k) Q).coeff 0 = 0})) (h₀ i)
  induction' ν with n ih
  · apply liftIdeal_le_of_p_pow_mem <;> simpa using mem_liftIdeal_zero_of_mem_one _ _ le_rfl
      (p_pow_mul_z_pow_mem_liftIdeal_iff.2 h₀) (by grw [← card_image_iff.2
      (d.primitive.injOn_pow.mono (by grind)), card_le_degree_of_subset_roots (p := Q.map _)
      (forall_mem_image.2 (by
      simp [aeval_def, hom_eval₂, eval_map, ← WittVector.constantCoeff_apply, map_monic_ne_zero M]
      tauto)), natDegree_map_le, natDegree_mul_le, natDegree_X_sub_C, hc])
  apply ih hν.le
  rw [card_filter, sum_eq_sum_Ico_succ_bot hν] at *
  split
  · exact mem_liftIdeal_zero_of_mem_one _ _ (by lia) (p_pow_mul_z_pow_mem_liftIdeal_iff.2 h₀)
      (by grind [padicValNat_factorial_mul, padicValNat.mul,
      Nat.log_lt_of_lt_pow (by omega) (hν.trans_le hm), Nat.factorial, padicValNat_le_nat_log])
  obtain ⟨u, K⟩ := S.exists_lift_of_mem_liftIdeal (f := p ^ _ * d.z ^ _) h₀
  obtain ⟨w, t, rfl⟩ := d.exists_z_dvd_sub_const u
  refine (smul_mem_iff_of_isUnit _ ((isUnit_of_coeff_zero_ne_zero _ ‹_›).map (algebraMap ..))).1
    (mem_liftIdeal_iff.2 ⟨Q.sum fun k a ↦ a • toGp (d.tameGen ^ k) • t.1 * d.zetaE ^ k, fun c ↦
    (K _ (constantAt_mem_locLetterPart c)).rec fun x ⟨m, f⟩ ↦
    have ⟨X, v, b⟩ := exists_z_smul_eq_sum_tameGen (q := Q) (aeval_linearFrob_extLattice_eq_zero hK)
      ⟨frobKisinAinf_zero.le (mem_withExponents_stdExponent_iff.1 m.2).1, m.1.2⟩
    ⟨_, letterProj_mem_withExponents (frobKisinAinf_zero.ge v),
      (isUnit_WittCFlat_of_not_p_dvd d.not_p_dvd_z).smul_left_cancel.1 ?_⟩⟩)
  linear_combination (norm := simp [f, -map_pow, tameGen_pow_smul_z, fixesLambda_tameGen_pow, smul,
    smul_letterProj (m := inr _) (fixesLambda_tameGen_pow ..),
    aeval_eq_sum_range, mem_letterPart_iff_letterProj.1 letterProj_mem_letterPart, sum_over_range,
    smul_sub, smul_sum, sum_mul, sub_smul, constantAt, ← sum_sub_distrib, sub_add_eq_sub_sub_swap,
    ← sum_add_distrib, frobGroup_smul_smul, sum_smul]) congr(letterProj i (S.projTriv.wittMap $b) -
    $(Q.eval_eq_sum_range 1 ▸ eval_mul_X_sub_C _) • p ^ κ.succ • (w : Ainf) • S.constantAt i c)
  exact sum_eq_zero fun _ _ ↦ by module

end TameChart

end Lift

/-- If j: Γ → G_p is surjective, e divides p^f − 1 and p does not divide f, then there is a tame
Kummer chart `Lift.TameChart` for j with ramification index e. -/
lemma Lift.exists_tameChart {p e} [hp : ThePrime p] [Γ : GroupOverGp p] (hj : Function.Surjective
  Γ.overGp.toGp) (f : ℕ+) (hf : ¬p ∣ f) (he : e ∣ p ^ f.val - 1) : ∃ d : TameChart Γ, d.e = e := by
  obtain n := @not_dvd_pow_sub_one p _ f, NeZero.mk (ne_zero_of_dvd_ne_zero NeZero.out he)
  obtain ⟨⟨ϖ, hϖ⟩, a, Z⟩ := IsSepClosed.exists_pow_nat_eq (p : PadicAlgCl p) e,
    (HasEnoughRootsOfUnity.of_dvd (flatFq f) he).1
  obtain ⟨c, rfl, _, _, ⟨⟨⟩⟩⟩ := (@exists_chart_of_pow_mul_eq_neg p _ f ⟨ϖ, by
    simp [le_of_pow_le_pow_left₀ (NeZero.ne e), ← norm_pow, *, norm_p_lt_one.le]⟩ e (-1)
    (Subtype.ext (by simp [PadicComplex.coe_eq, ← map_pow, *]))).choose_spec.2 (-1) (by simp)
  set N := _ - 1
  obtain ⟨T, q, K⟩ := (hj.exists.1 <| exists_smul_teichmuller_eq _
    (isLocalGalois_padic.exists_inertia_smul_eq_of_pow_eq isUniformiser_ell) c.varpiFlat · c.e (by
    simp [PadicComplex.coe_eq, ← map_pow, *]) ·), (he.rec (by simp_all [pow_mul, div_pow,
    ← map_pow]) : ∀ g : Gp p, (g ϖ / ϖ) ^ N = 1), fun {g} ↦ by simpa using (@cycCharMod_eq_iff
    (Gp p) (PadicAlgCl p) _ _ _ N g _ _ _ 1), (fixes_roots_iff_fixesLambda · |>.1 <|
    apply_eq_self_of_mem_inertiaGroup n ·), ne_zero_pow NeZero.out (hϖ.trans_ne NeZero.out)
  let U : OpenSubgroup _ :=
    ⟨(cycCharMod _ N).ker, isOpen_ker_cycCharMod.1⟩ ⊓ ⟨_, isLocalGalois_padic.1.6 ϖ⟩
  have M {g} : g ∈ U ↔ c.FixesThetaZ g :=
    (K.trans (fixes_roots_iff_fixesLambda g)).and (by simp [*, c.z_eq_teichmuller, Subtype.ext_iff])
  have Pe {g} h : g ^ N ∈ U := ⟨pow_mem h _, by
    simp [*, @Function.Commute.iterate_eq_of_map_eq _ g (g ϖ / ϖ * ·) fun _ ↦ by aesop]⟩
  have : U.Normal := ⟨fun n c g ↦ by have := K.1 c.1 _ (q g⁻¹); simp_all [U, -K]⟩
  exact (T (a * c.varpiFlat) (by simp [mul_pow, ← map_pow, ← Subring.coe_pow, Z.1])).rec fun s i ↦
    ⟨@.mk _ _
    _ ⟨c, .comap toGp U, U.index_comap_of_surjective hj ▸ .of_dvd_left (IsPGroup.exists_card_dvd_pow
    (⟨1, ·.ind' fun g ↦ by simpa [← QuotientGroup.mk_pow, pow_mul] using Pe (K.2 fun
    _ e ↦ by simp [Function.Commute.iterate_eq_of_map_eq (map_pow g · _) _ (exists_apply_eq_pow n e
    g).choose_spec, pow_right_comm, pow_eq_pow_of_modEq ((Nat.modEq_sub NeZero.one_le).pow _)
    e])⟩)).choose_spec (.pow_left _ (hp.out.coprime_iff_not_dvd.2 (hp.out.not_dvd_mul hf n)).symm),
    by simp [M], hj.forall.2 (⟨⟨·, M.2 ·⟩, rfl⟩), by simpa using ⟨_, U.mem_nhds_one, .rfl⟩, fun l ↦
    by simpa using (T (epsTilt ^ l * c.varpiFlat) (by simp)).imp (by simp_all [↓← theta_smul,
    FixesLambda, c.z_eq_teichmuller, Chart.FixesThetaZ])⟩ _ s Z (by
    induction · <;> simp_all [pow_succ', mul_smul, c.z_eq_teichmuller]
    erw [WittVector.map_teichmuller]; ring!)
    (isWeilPair_zero_iff.2 i.1) (by simp [FixesLambda, *, pow_mem]) ϖ (·.2.2)
    hϖ (n ∘ (.trans · he)) (this.comap _), rfl⟩

namespace Lift.KummerChart.PairingSide

open Finset
variable {p} [j : ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {S S' :
  PairingSide O} (h : S.SidePairing S') {cut T : Letter → Prop} [DecidablePred T] {ε :
  Letter → ℤˣ} {s β : Letter → ℕ} {η V W X κ b n J s₀ G e K : ℕ} (hW : V + 4 * η ≤ W) (hU : ∀ i,
  IsInJumpWindow η (-ε i) (β i) V (S.U i) ∧ IsInJumpWindow η (ε i) (β i) V (S'.U i)) (hX :
  (J + 1 + k.differentExp + p.log (2 * b)) * n + k.differentExp * G ≤ X) (hκ : 12 * (J + 1)
  * X < κ) (hδ : k.e * (2 * b) ≤ p ^ (J + 1) * X) (h₈ : 8 * k.e ≤ p ^ (J + 1)) (hη : 1 ≤ η) (hs : W
  ≤ n ∧ W ≤ G ∧ ∀ i, β i + s i + W ≤ 2 * b) (hy : G ≤ (p - 1) * n) (hK : ∀ i, cut i → s i = 0 ∧ (∀ t
  ∈ Icc 1 J, β ((k.letterFrob ^ t) i) + W ≤ G) ∨ s i < β i ∧ IsUnramified ∧ 5 ≤ p ∧ s₀ ≤
  κ + s i) (hz : 5 ≤ p → ∀ i, β i + W ≤ (p - 3) * s₀) (hβ : β = fun i ↦ ite (T i) b G)
include hs hz hy hδ h₈ hX hκ hK

/-- Let the jump sets of S be bounded by β_i + W ≤ 2b − s_i. Under size inequalities, p^κE^{s_i}
kills (`Lift.KummerChart.PairingSide.KillsCokernel`) at each cut letter i, where either s_i = 0 and
β + W ≤ G at i^{p^t}, 1 ≤ t ≤ J, or the chart is unramified, p ≥ 5, s_i < β_i, s₀ ≤ κ + s_i. -/
lemma killsCokernel_at_cut (w : ∀ i n, β i + W ≤ n → ∀ u ∈ S.U i, u ≤ n) i (c : cut i) :
  S.KillsCokernel i κ (s i) := by
  obtain ⟨⟨e, t⟩ | ⟨_, hk, q, e⟩, ⟨a, H, f⟩, hp⟩ :=
    hK i c, exists_z_pow_mem_liftIdeal (w · (2 * b) (by grind)) κ.succ, j.out.one_lt
  have K x (l : p * a ≤ p ^ (J + 1) * x) :
      p ^ (J * X) * k.z.1 ^ (x + n) ∈ S.liftIdeal (p ^ κ.succ) 0 i := by
    clear hδ h₈ hκ hK c e; induction' J with s ih generalizing i x
    exact Ideal.mem_of_dvd _ (by simp_all [pow_dvd_pow, hp.pos, le_add_right]) (H i)
    apply p_pow_mul_z_pow_mem_liftIdeal_iff.1 (mem_liftIdeal_of_mul_E_pow
      (mul_E_pow_mem_liftIdeal_one (ih (by lia) _ (t ·.succ ∘ by simp) _ (by rwa [← mul_assoc]))
      (by tauto)) ⟨?_, ?_⟩) <;> nlinarith [(@sub_one_mul_padicValNat_factorial
      p _ G).trans_le tsub_le_self, p.sub_add_cancel hp.le]
  apply liftIdeal_le_of_p_pow_mem <;> simpa [e] using mem_liftIdeal_zero_of_mem_one _ κ (a := 0)
    bot_le (p_pow_mul_z_pow_mem_liftIdeal_iff.2 (K (2 * X + κ /
    4).succ (by nlinarith [κ.lt_div_mul_add four_pos]))) (by grw [padicValNat_factorial_mul,
    Nat.le_sub_one_of_lt (padicValNat_factorial_lt_of_ne_zero ..)] <;> lia)
  exact killsCokernel_of_isUnramified _ _ (w · _ (by grw [hz q, e])) hk q

include hW hη hU

variable (cut s b n J s₀ G) in
lemma SidePairing.scaledCupBounds_of_cut_windows (hd : ∀ i, s i + W ≤ p * n) (he : 51 * κ ≤ e) (hL :
  ∀ i : k.Letter, ∃ l ∈ Set.Ioc 0 (2 * J + 1), cut (i.stepBack l)) (H : ∀ i l, cut (i.stepBack l) →
  (∀ a ∈ Set.Ioo 0 l, ¬cut (i.stepBack a)) → ∃ t, (∀ a < l, ε (i.stepBack a) = ε (i.stepBack t) ∨
  β (i.stepBack a) + V ≤ η) ∨ k.IsUnramified ∧ 5 ≤ p ∧ s (i.stepBack l) = 0 ∧
  t + (J + 1) = l ∧ (s i = 0 ∨ t = 0) ∧ s₀ + G * ∑ a ∈ range (J + 1), p ^ a < β (i.stepBack t) ∧
  ∀ a < l, a ≠ t → (ε (i.stepBack a) ≠ ε (i.stepBack t) ∨ β (i.stepBack a) + V ≤ η) ∧
  (t < a → β (i.stepBack a) + W ≤ G)) c c' : h.ScaledCupBounds e c c' := by
  let A a := ite (a ≤ 2 * J) η 0
  choose l hl hn using (hL · |> Nat.findX |>.exists_of_subtype)
  choose t hc using (H · _ (hl _).2 (by grind))
  let R ρ i a u := ite (ε (.stepBack i (t i)) = ρ) (stdExponent (l i) a u) (-u - A a) ⊔ (-u - A a)
  have pt {T T' : PairingSide O} ρ {σ} (hU : ∀ i, IsInJumpWindow η (ε i / -ρ) (β i) V (T.U i) ∧
      IsInJumpWindow η (ε i / ρ) (β i) V (T'.U i)) {c i} (hi : cut i) : T.HasDeepPoint T' c i
    (25 * κ) cut (l i) (R ρ) (R σ) (raisedAtE <| -s ·) (ε (i.stepBack (t i)) = ρ) := by
    obtain ⟨⟨hL, hl⟩, hc, ht, h₀, q, z⟩ := hl i, hc i, hK i hi, (hK i hi).imp (·.1) (·.2.1.2.2),
      (show _ ≤ R σ · · · from le_sup_right), stepBack_zero i
    generalize R σ = w at *; unfold HasDeepPoint R; generalize l i = l, t i = t at *
    simp [IsInJumpWindow, div_eq_one, ← Int.units_ne_iff_eq_neg] at hU
    have kl := T.killsCokernel_at_cut hX hκ hδ h₈ hs hy hK hz ?_
    let o a u := raisedAtE (s i) a u + A (a / 2)
    obtain ⟨⟨_, hx⟩, ⟨hi, hk, hp, hy, rfl, ht, he, hc⟩ | ⟨hl, hc⟩⟩ :=
      pointsOver_nonempty_of_killsCokernel (kl i hi) c,
      (em (ε (i.stepBack t) = ρ ∧ ¬_)).imp (·.imp_right hc.resolve_left) (And.intro (z ▸ hi))
    have y a : (i.stepBack t).stepBack a = i.stepBack (t + a) := by simp [pow_add]
    have hx := phi_pow_smul_mem_pointsOver (pointsOver_nonempty_of_long_gap J.succ_pos hk (y _ ▸
      hy ▸ kl _ hl) (killsCokernel_of_isUnramified _ _ (by clear * - hU hz hp hW; grind) hk hp) rfl
      (y · ▸ by clear * - hU hc hs hW hi; grind) (he.trans_le ?_) (by lia) hδ c).some_mem
    let o a u := ite (a ≠ t) (stdExponent (t + J.succ) a u + 3 * A (a / 2)) (2 * b)
    all_goals try refine ⟨o, _,
      (pointsOver_nonempty_of_costs hx ((range (4 * J + 2)).sigma fun a ↦ twoWindows (ite (a = 0)
      (s i) 0 + W) (ite (ε (i.stepBack a) = ρ) 1 (-1) * β (i.stepBack a))) ?_ (by
      clear * - hd h₀ hs z hη hW hX hκ
      grw [← sum_sigma', sum_le_card_nsmul _ _ (72 * X), card_range]; lia
      refine fun a ha ↦ (sum_twoWindows_le n (2 * b) ?_ ?_).trans ?_ <;> grind [mul_le_mul' hs.1
        (add_le_add_left (mem_range_le ha) k.differentExp),
        le_of_mul_le_of_one_le_left (le_of_add_le_left hX) (by lia)])).imp fun _ ↦
      .imp_right (.imp_right (.imp_left (JumpLattice.mem_withExponents_of_le · ?_))), hl, ?_⟩
    all_goals
      try intro a; specialize hc a
      clear * - hU hc hi hL hs hW ht hη z hy he q; generalize i.stepBack = f at *
      (try simp [raisedAtE, -Nat.cast_sum]); grind (splits := 15)
  refine h.scaledCupBounds_of_points_at_cuts _ _ l (by grind [IsLeast, lowerBounds]) fun i e ↦
    ⟨pt 1 ?_ e, Int.units_ne_iff_eq_neg.eq ▸ pt (-1) ?_ e, pointsOver_nonempty_of_killsCokernel
    (killsCokernel_at_cut hX hκ hδ h₈ hs hy hK hz ?_ i e) 1, ?_⟩ <;>
    clear * - hU hW <;> simp [div_neg, Antitone] <;> grind

omit hs hz hy hX hκ hK
include hβ

/-- Sparse thick letters. Paired sides have jump sets in opposite windows [−η, η] ∪ ±[β_i, β_i + V],
β_i = b or G, G + V ≤ η, no three β = b at gaps in [1, J]; signs constant, or unramified with p ≥ 7.
Under size inequalities `Lift.Pairing.ScaledCupBounds` holds with exponent 10⁴X(J + 1).

Rank-free exponents for crystalline classes at large weights. -/
lemma SidePairing.scaledCupBounds_sparse_thick (hε : IsUnramified ∧ 7 ≤ p ∨ ∀ i i', ε i = ε i')
  (hG : G + V ≤ η) (hb : 11 * (p ^ J + 1) * W ≤ b) (hth : ∀ i, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J, T i →
  T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i)) (he : 4 * (J + 1 + k.differentExp +
  p.log (2 * b)) * W ≤ X) c c' : h.ScaledCupBounds (10 ^ 4 * (X * (J + 1))) c c' := by
  let C i := ∀ t ≥ 1, t ≤ J → ¬T ((k.letterFrob ^ t) i)
  replace hth i a (c : ¬C (.stepBack i a)) (t : T (i.stepBack a)) : C (i.stepBack (a + J.succ)) :=
    fun n _ hn tn ↦ c (by simp at t; simpa [t, pow_add, add_comm (_ - _), pow_sub _ hn.step] using
    (hth _ (J.succ - n) (by simp; lia) · · tn))
  apply h.scaledCupBounds_of_cut_windows _ (fun _ ↦ 0) b (2 * W) _ (3 * b / 5) (2 * W) hW hU _ .refl
    hδ h₈ hη _ _ _
    (by grw [← ·]; grind) _ _ (by_contra fun h ↦ h ⟨J + 1, by grind, fun n _ hn t ↦ h ⟨_, by grind,
    hth · (J + 1 - n) (h ⟨_, by simp; lia, ·⟩) (by simpa [pow_sub _ hn.step])⟩⟩) fun i n hl h ↦ ?_
  iterate 6 grind [mul_le_mul_left j.out.one_lt W, tsub_mul]
  replace hth a ha t := (eq_zero_or_pos a).imp_right fun a₀ ↦ (not_lt.1 fun e ↦ hl (n - a) (by lia)
    (by lia) (by simpa [← pow_mul_pow_sub _ ha.le])).eq_of_not_lt (h _ ⟨by lia, ·⟩
    (hth i a (h a ⟨a₀, ha⟩) t))
  exact (forall_or_exists_not _).elim (⟨0, .inl ·⟩) (.imp (by
    grw [sum_range_succ, @Nat.geomSum_lt _ J _ j.out.one_lt] <;> grind))

omit hδ h₈ in
lemma SidePairing.scaledCupBounds_two_sizes (hk : IsUnramified) (hp : 7 ≤ p) (h₀ : 5 * W ≤ G) (hG :
  G ≤ b) (hb : b < K * p ^ 2 ∧
  2 * G < K * p ∧ W ≤ K) c c' : h.ScaledCupBounds (10 ^ 4 * (K * (p.log (2 * b) + 1))) c c' := by
  obtain _ := pow_le_pow_left' hp 2, mul_le_mul_right hp (K - 1), mul_le_mul_right hp (b / p),
    b.div_mul_le_self p, @b.lt_div_mul_add p, @b.div_lt_of_lt_mul p (K * p)
  have z i : k.letterFrob (i.stepBack 2) = i.stepBack 1 ∧ k.letterFrob (i.stepBack 1) =
    i := by simp [sq]
  let s i := ite (T (k.letterFrob i)) (b / p - 7 * K) 0
  apply h.scaledCupBounds_of_cut_windows (fun i ↦
    s i < β i) s b K 1 (b / p + 12 * K) (G + W) hW hU .refl .refl <;> clear hU
  iterate 10 grind [tsub_mul, pow_one, hk.2]
  rintro i (_ | _ | _ | l) _ u <;> use 0 <;> try grind
  refine (em _).imp_right fun _ ↦ ⟨hk, ?_⟩; and_intros <;> try grind
  simp; nlinarith [(by grind : G + 7 * K ≤ b / p ∧ β i = b)]
