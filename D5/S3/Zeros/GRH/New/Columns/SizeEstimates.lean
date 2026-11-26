/- GID: D5/S3/Zeros/GRH/New/Columns/SizeEstimates
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/SizeEstimates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.SizeEstimates. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/SizeEstimates.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Core.ClassCountBound
import D5.S3.Zeros.GRH.New.Columns.ColumnDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

Part of: Divisibility of the chain of theta lifts at each prime (see New.Columns.LocalStatement).

This file: Size bookkeeping: row lengths, factorial sizes, class counts, sum of allowed losses. -/

open Nat ArithmeticFunction Finset NeZero NumberField Real Space Subgroup

namespace Data

attribute [-simp] posPart_of_nonneg posPart_of_nonpos

variable {P} (D : Data P) (σ : ℂ ≃+* ℂ) {n : Type} [Fintype n] {K : Subgroup (Gf D.E n)}

/-- The number m(∑_τ (st(a) − Ask(a, τ)) + kU) − |𝒯|·a·log N, τ over the set 𝒯 of tops; see
`Data.jetSize`, `Data.primeSum`, U = `Data.dirCost`. -/
noncomputable def heightPerRow := D.m * (∑ τ ∈ D.tops,
  (D.jetSize D.a - D.primeSum D.a τ) + D.k * D.dirCost) - #D.tops * D.a * .log D.N

/-- The set of primes p < x₁ with Legendre symbol (p|d) ≠ 1, the primes below x₁ that do not
split in K. -/
noncomputable abbrev nonsplitPrimes := {p ∈ range ⌈D.x₁⌉₊ | Nat.Prime p ∧ chiK P.d p ≠ 1}

/-- For y ≤ a, an infinite place σ and a natural number U ≥ ⌈x₁⌉, Ask(y, σ) = ∑ 2·ask_p(y,
σ)·log p over the primes p < U, with Ask = `Data.primeSum` and ask_p = `Data.localAsk` at p. -/
lemma primeSum_eq_sum_localAsk {U} (hU : ⌈D.x₁⌉₊ ≤ U) {y} σ (hy : y ≤ ↑D.a) :
    D.primeSum y σ = ∑ p ∈ range U with p.Prime, 2 * D.localAsk p y σ * .log p := by
  simp [primeSum, lambdaClass, Unique.eq_default, ← sum_subtype_eq_sum_filter]; set G := fun _ ↦ _
  have h0 : ∀ ν ∉ range ⌈D.x₁⌉₊, G ν = 0 := by simp [G]; grw [← (nominalWeight_mem_Icc ..).1]; bound
  convert tsum_eq_tsum_primes_of_support_subset_prime_powers (summable_of_ne_finset_zero h0) (by
    simp_all [G, vonMangoldt]) <;> rw [tsum_eq_sum]
  grind [(D.nat_le_of_hasLogBound : ⌈D.x₁⌉₊ ≤ D.a), vonMangoldt.map_zero]; congr with ⟨p, hp⟩
  erw [mul_right_comm, ← mul_assoc, ← tsum_mul_left, ← succ_injective.tsum_eq (by aesop)]
  obtain ⟨rfl, _⟩ | ⟨_, ⟨⟩⟩ := @chiK_cases P.d p ⟨hp⟩ _ <;> simp_all [G, neg_one_pow_eq_ite,
    vonMangoldt_apply_pow, vonMangoldt_apply_prime] <;> grind
  simp +contextual (disch := grind [le_self_pow₀, Primes]) [h0]

/-- For j < m, row i (from 0) of the weight on X_{j+1} at τ has length at most h₂² plus: κ_τ(1)
+ b₁ + b₂ if i = 0, w_0(τ) if 0 < i < k, and nothing otherwise. -/
lemma diagramWeight_le_by_index {j} (hj : j < D.m) τ i :
  diagramWeight (rankAt (D.X (j + 1))) D.κ (τ, i) ≤ ite (i = 0)
  (D.κ τ 1) (ite (i < D.k) (D.w 0 τ) 0) + (ite (i = 0) (D.b₁ + D.b₂) 0 + D.h₂ ^ 2) := by
  grw [diagramWeight_apply, rankAt, card_X, n_mono _ hj, (ite_self _).ge.trans (κ_le ..)]
  simp [tsub_mul]
  grind [(D.nat_le_of_hasLogBound : (D.n D.m + 2) * D.h ≤ D.h₂ ^ 2)]

lemma norm_map_star_piG_sq : ‖σ (star (D.piG : P.K).1)‖ ^ 2 = D.gProd := by
  simpa [-RingHom.coe_comp, gProd, sq] using! congr(‖σ.toRingHom.comp (star P.K.val.1) $D.norm_piG‖)

/-- For natural numbers l ≤ r + e, the Stirling term st = `Data.jetSize` satisfies st(l) ≤ st(r)
+ e·(log(r + e + 1) − log(Ω/g)), with Ω = `Parameters.bigOmega` and g = g₀g₁. -/
lemma jetSize_le_add {l r e : ℕ} (h : l ≤ r + e) :
    D.jetSize l ≤ D.jetSize r + (.log (↑(r + e) + 1) - (P.bigOmega D.s / D.gProd).log) * e := by
  grw [jetSize, jetSize, factorial_le h, ← factorial_mul_ascFactorial,
    (ascFactorial_le_pow_add ..).trans (by grw [le_succ (_ + _)])]
  simp (disch := positivity) [log_mul]; rify at h
  nlinarith [(P.bigOmega D.s / D.gProd).log_inv ▸ log_nonneg D.le_of_hasLogBound]

/-- Let G ≥ 1 be an integer and n an index set of size at most 2𝗇_m. If K contains the principal
level K(G), then I_n has at most exp(x^29(1 + log G)) classes at level K. -/
lemma card_stdClasses_le_exp_mul_log (G : ℕ) [NeZero G] (hn : Fintype.card n ≤ 2 * D.n D.m) (h :
  principalLevel n G ≤ K) : Nat.card (StdClasses K) ≤ exp (D.x ^ 29 * (1 + .log G)) := by
  have : Fact ((G : 𝓞 D.E) ≠ 0) := ⟨out⟩
  have := FiniteIndex.mk (relIndex_ne_zero_of_isLevel _ ∘ relIndex_eq_zero_of_le_left h)
  grw [card_le_card_of_surjective _ (surjective_doubleCoset_mk_mul _ (Kf ..) K), card_prod, ← index,
    ← relIndex, relIndex_le_of_le_left h, relIndex_principalLevel_le, Ideal.absNorm_span_natCast,
    RingOfIntegers.rank, finrank_eq_two_mul_card_infinitePlace,
    card_classes_le P.cycloConductor_mem_different, shortBasisConst, hn, hn, ← le_exp_of_log_le] <;>
    simp [-cast_add, NeZero.one_le, NeZero.pos, ne, log_mul, mul_add, ← mul_assoc]
  gcongr <;> use D.le_of_hasLogBound

lemma card_stdClasses_le_exp (h : principalLevel n (D.piGBar * D.π) ≤ K) (hn : Fintype.card n ≤
  D.n D.m := by simpa using D.nat_le_of_hasLogBound) : Nat.card (StdClasses K) ≤ exp (D.x ^ 30) :=
  (D.card_stdClasses_le_exp_mul_log (D.gProd * D.N) (by lia) (by
  grw [← h, principalLevel_le_of_dvd]; simp [← piGBar_mul_star, ← π_mul_star, mul_dvd_mul])).trans
  (by simpa using D.le_of_hasLogBound)

/-- The allowed loss err(p): 3·loss(p) for a non-split prime p < x₁ (`Data.loss`, with the
factor m if p is short), otherwise 4mfb for p = N, and 0 for every other p. -/
noncomputable def allowedLoss p :=
  ite (p ∈ D.nonsplitPrimes) (3 * D.loss p) (ite (p = D.N) (4 * D.m * D.f * D.b) 0)

/-- For every finite set U of natural numbers, ∑_{p∈U} err(p) log p ≤ fa(log b)³, with
err = `Data.allowedLoss` the allowed loss; the bound is `Data.budget`. -/
lemma sum_allowedLoss_mul_log_le U : ∑ p ∈ U, D.allowedLoss p * .log p ≤ D.budget := by
  obtain := (HasLogBound.pos D : 0 < D.logX₁).le, D.hasLogUpper_of_le_of_nonneg
    (log_exp _ ▸ harmonic_eq_sum_Icc ▸ harmonic_floor_le_one_add_log D.x₁ D.le_of_hasLogBound)
  grw [sum_le_sum fun p _ ↦ ?_, (Icc 1 ⌊D.x₁⌋₊ ×ˢ range 4).sum_fiberwise_eq_sum_filter _
    (fun (c, r) ↦ [D.N, D.m * c - 1, c, D.m * c + 1][r]!)
    (3 * D.f * D.a * D.logB ^ 2 * _ * 2 / ·.1), filter_subset]
  simp_all [sum_product, division_def, ← mul_sum]; use D.le_of_hasLogBound
  simp [allowedLoss, lt_ceil]; split_ifs with h h
  · obtain := h.2.1.two_le, le_floor h.1.le
    rsuffices ⟨u, a, b⟩ : ∃ u ∈ @filter .., @ite .. ≤ 2 * p / Prod.fst u
    grw [loss, b, ← single_le_sum (by bound) a, h.1, log_exp, cast_div_le]; simp [field]
    split; obtain ⟨c, _⟩ | ⟨c, _⟩ := ‹_› <;> [use (c, 3); use (c, 1)] <;>
      grind [c.div_lt_iff_lt_mul, mul_le_mul_left c D.le_m]
    use (p, 2); grind [mul_div_left]
  grw [h, ← single_le_sum (by bound) (a := (1, 0)) (by simpa)]
  exacts [D.le_of_hasLogBound (by grind [log_nonneg, scale]), by positivity]
