/- GID: D5/S3/Zeros/GRH/New/Columns/JetExponentBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/JetExponentBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.JetExponentBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/JetExponentBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.CrudeModularData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Scaled Hecke operators repair divisibility at inert primes pairing tops (see
New.Columns.LocalStatement).

Part of: Divisibility of the chain of theta lifts at each prime (see New.Columns.LocalStatement).

This file: Marked primes at inert p: orders of -p, parity, balance; scaled Hecke operator. Sum of
jet exponents along the chain is at least gain minus error. -/

open Nat Finset Parameters Real

variable {P} {D : Data P} {p : ℕ} (D' : Data P) {e : ℕ}

instance Data.instUbCastRealRrLogLx₁ [hq : Fact p.Prime] :
  D.HasLogUpper (D.ceilLogM p) (log D.logX₁) := D.hasLogUpper_of_le
  (A := D.s) (clog_le_of_le_pow (by grw [← hq.1.two_le]; use D.nat_le_of_hasLogBound))

/-- If the prime p is served, then m divides the order of the place named by −p in the group of
infinite places (ℤ/N₁)^×. -/
lemma Data.IsServed.m_dvd_orderOf [hq : Fact p.Prime] (h : D.IsServed p) :
  D.m ∣ orderOf (D.placeOfInt (-p)) := by
  obtain ⟨⟨⟩, i, _⟩ := D.m_pow, h
  have := @two_pow_dvd_or_of_pow_eq_one (-p) _ D.s (orderOf_pos (D.placeOfInt (-p)))
    (placeClass_placeOfInt (d := two_pow_dvd_N₁) (@isCoprime_N₀_of_not_dvd P 0 p _
    (by grind [chiK_eq_one_of_dvd, Fact])).neg_left ▸ mod_cast by simp [← map_pow])
  simp_all [IsShortPrime, ← Int.natAbs_dvd_natAbs, Int.natAbs_mul, padicValNat_dvd_iff]
  grind [padicValNat.mul]

lemma Data.le_loss p : D'.f * D'.logB ^ 2 * (D'.a / p) ≤ D'.loss p := by rw [loss]; bound [D'.le_m]

/-- For odd e and a top τ (`Data.tops`), the place (−p^e)τ is a top if and only if `Data.o₀` p
divides e. -/
lemma Data.placeOfInt_mul_mem_tops_iff (o : Odd e) : ∀ τ ∈ D'.tops,
  D'.placeOfInt (-p ^ e) * τ ∈ D'.tops ↔ D'.o₀ p ∣ e := by
  simp_all [o₀, tops, ← o.neg_pow, ← placeOfInt_pow, orderOf_dvd_iff_pow_eq_one]

variable {p : ℕ} [hq : Fact p.Prime] [PadicPlace p] {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E}

lemma Data.p_mem_inducedPlace σ : ↑p ∈ (D'.inducedPlace σ).1 := natCast_mem_placeOfEmb _

lemma Data.inducedPlace_mul σ τ : D'.inducedPlace (σ * τ) =
  τ • inducedPlace σ := by ext; simp [inducedPlace, phi_mul]

attribute [local grind] Data.IsMarked Data.IsServed Data.p_mem_inducedPlace
  Data.inducedPlace_mul Nat.Prime.dvd_mul
  Nat.prime_dvd_prime_iff_eq not_dvd_N₁_mul_d_of_inert smul_eq_star_iff_inert star_star

/-- If p is inert in K and e is odd, the place (−p^e)σ induces the conjugate of the prime that σ
induces. -/
lemma Data.inducedPlace_neg_pow_mul_of_odd (h : chiK P.d p = -1) (he : Odd e) σ :
    D'.inducedPlace (D'.placeOfInt (-p ^ e) * σ) =
  star (inducedPlace σ) := by grind [mul_comm, placeOfInt_pow, he.neg_pow (p : ℤ)]

/-- For a served prime p < x₁ there is a marked set Λ (`Data.IsMarked`) such that every top
induces a prime in Λ or the conjugate of one. -/
lemma Data.exists_isMarked (D : Data P) (hp : p < D.x₁) (h : D.IsServed p) : ∃ Λ,
  D.IsFullMark Λ := by
  cases exists_wellFoundedLT (FinPlace D.E)
  use {l ∈ D.tops.image inducedPlace | l < star l}, by grind, fun τ a ↦ by grind [h.m_dvd_orderOf, →
    Even.trans_dvd, D.inducedPlace_mul τ 1, orderOf_dvd_of_pow_eq_one,
    inducedPlace_neg_pow_mul_of_odd, (D.placeOfInt_mul_mem_tops_iff h.2.2.1 τ a).2 dvd_rfl]

/-- If p is inert in K, the place σ induces the prime induced by τ or its conjugate if and only
if σ = (−p)^i τ for some i. -/
lemma Data.inducedPlace_eq_or_star_iff (h : chiK P.d p = -1) σ τ : D.inducedPlace σ =
  inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ) ↔ ∃ i, σ =
  D.placeOfInt (-p) ^ i * τ := by grind [mul_div_cancel τ σ, mul_comm, smul_eq_iff_inert]

lemma Data.IsMarked.card_le (h : D.IsMarked Λ) : #Λ ≤ D.f :=
  card_le_card_of_surjOn inducedPlace fun _ ↦ by grind

lemma Data.IsMarked.not_dvd_gProd_mul_N (h : D.IsMarked Λ) : ¬p ∣ D.gProd ∧ p ≠ D.N ∧
  ¬p ∣ D.gProd * D.N := by grind [gProd, hq.1, g_prime, N_prime,
  (D.le_of_hasLogBound : D.x₁ ≤ D.N), !(D.le_of_hasLogBound : D.x₁ ≤ D.g _)]

/-- If Λ is marked and the prime induced at ι by the infinite place σ, or its conjugate, lies in
Λ, then σ is not in `Data.thick`. -/
lemma Data.IsMarked.notMem_thick (h : D.IsMarked Λ) σ (a : inducedPlace σ ∈ Λ ∨
  star (inducedPlace σ) ∈ Λ) : σ ∉ D.thick := fun _ ↦ P.pow_d_ne_neg_one 0 (by
  let ⟨i, t, _, _, o, _⟩ : ∃ i, D.placeOfInt (-p) ^ i * σ ∈ D.tops ∧
    D.IsServed p := by grind [inducedPlace_eq_or_star_iff]
  simp_all [tops, placeClass_of_thick]
  simpa [o₀, pow_right_comm _ i, ↓o.neg_pow] using congr((-$t ^ D.o₀ p).1))

/-- Let Λ be marked and G(c, l) a real function vanishing for l outside Λ. Then ∑_τ G(w_j(τ),
l(τ)) = ∑_τ G(w_j(τ), conj l(τ)), with l(τ) the prime induced by τ at ι. -/
lemma Data.IsMarked.sum_inducedPlace_sub_star_eq_zero (h : D.IsMarked Λ) j (G : ℕ → _ → ℝ) : 0 =
  ∑ τ, (ite (inducedPlace τ ∈ Λ) (G (D.w j τ) (inducedPlace τ)) 0 - ite (star (inducedPlace τ) ∈ Λ)
  (G (D.w j τ) (star (inducedPlace τ))) 0) := by
  rw [sum_sub_distrib, Fintype.sum_equiv (.mulLeft (D.placeOfInt (-p))), sub_self]
  simp; grind [notMem_thick, (D.inducedPlace_neg_pow_mul_of_odd · odd_one)]

lemma Data.IsMarked.p_mem (h : D.IsMarked Λ) (a : l ∈ Λ) : ↑p ∈ l.1 := by grind

lemma Data.IsMarked.valuation_p (h : D.IsMarked Λ) (a : l ∈ Λ) : l.valuation D.E p = .exp (-1) := by
  erw [l.valuation_of_algebraMap p, intValuation_p] <;> grind

lemma Data.IsMarked.star_ne (h : D.IsMarked Λ) (a : l ∈ Λ) : l.IsSplit := by grind

lemma Data.IsMarked.maxCompactAt_le_columnLevel (h : D.IsMarked Λ) (a : l ∈ Λ) :
    maxCompactAt _ l ≤ D.columnLevel 0 := (inf_supportedOn_le_principalLevel
  (by grind [not_dvd_gProd_mul_N, =_ l.natCast_mem_iff_dvd, piGBar_mul_star, π_mul_star,
  l.2.mul_mem_iff_mem_or_mem, mem_star_place, star_mul])).trans (principalLevel_le_columnLevel ..)

/-- For p < x₁ and a marked prime l, the O_ι-linear operator p^{A_l} T_{l,𝔯} on columns, with
A_l = `Data.markExponent` and 𝔯 least with m ≤ p^𝔯. -/
noncomputable def Data.IsMarked.markOperator (h : D.IsMarked Λ) (l : Λ) :
  Module.End embValRing D.Column := .restrictScalars _
  <| (p : ℂ) ^ markExponent l.1 • (heckeSplit _ (h.star_ne l.2) (D.ceilLogM p)).restrict fun _ a ↦
  heckeSplit_mem_levelSpace _ _ (levelSpace_anti (h.maxCompactAt_le_columnLevel l.2) a) IsLevel.le a

/-- The number (1/(p−1) − ρ_p)L − ((1 − (p/d))/2)·C − fn³(⌊log_p L⌋ + 1), L the boxes in columns
of height below n, C a sum of coupling counts `couplingCount`; compare `norm_schurJet_le`. -/
noncomputable def Data.jetExponent p j ev := let n := D.n (j + 1); let N := boxes D.κ n
    (1 / (p - 1) - nonsplitWeight P.d p) * N + (chiK P.d p - 1) / 2 * ∑ e ≤ p.log N with Odd e ∨ p =
      P.d,
      ∑ σ, couplingCount p D.κ n ev σ (D.placeOfInt (-p ^ e) * σ) e - D.f * n ^ 3 * (p.log N + 1)

/-- If (τ, e) is a collision at p outside ev, then p ≠ d, e is odd and o₀ divides e. -/
lemma Data.IsCollision.ne_and_odd_and_dvd {p ev τ} (h : D.IsCollision p ev τ e) : p ≠ P.d ∧ Odd e ∧
  D.o₀ p ∣ e := by grind [IsCollision, tops, ne_d_of_placeClass_eq, placeOfInt_mul_mem_tops_iff]

variable {p : ℕ} [q : Fact p.Prime] {j : ℕ}

/-- For p prime, if every collision (τ, e) outside ev has e ≥ o, then `Data.collisionSum` p ev is at
most 2fa/p^o. -/
lemma Data.collisionSum_le {S o} (h : ∀ {τ e}, D.IsCollision p S τ e → o ≤ e) :
    D.collisionSum p S ≤ 2 * D.f * D.a / p ^ o := by
  grw [collisionSum, ((add_right_injective o).tsum_eq fun e a ↦ le.dest (by
    grind [Function.mem_support])).ge, le_norm_self (tsum _), tsum_of_norm_bounded
    (hasSum_geometric_two' (D.a / p ^ o * 2))]; simp [field]
  intro; split <;> simp [pow_add, ← div_div] <;> bound [cast_le (α := ℝ).2 q.1.two_le]

/-- Let p < x₁ be a prime with χ_K(p) ≠ 1 that is not served. Then m times the sum of a/p^e over
all collisions (τ, e), no place being excluded (`Data.collisionSum` at the empty set), is at
most `Data.loss` at p. -/
lemma Data.mul_collisionSum_le_loss (H : D.IsSmallNonsplit p) (h : ¬D.IsServed p) :
  D.m * D.collisionSum p ∅ ≤ D.loss p := by
  grw [loss, ← (D.le_of_hasLogBound : 2 ≤ D.logB ^ 2)]; split; grw [collisionSum_le (·.1.1)]; grind
  grw [collisionSum_le (o := D.ceilLogM p + 1) (by grind [IsServed, IsCollision.ne_and_odd_and_dvd,
    IsCollision, chiK_cases, Odd.of_dvd_nat,
    → le_of_dvd]), le_pow_clog q.1.one_lt D.m, ← ceilLogM]
  have := q.1.ne_zero; simp [pow_succ, field]

/-- If Λ is full (`Data.IsFullMark`), the sum `Data.collisionSum` of a/p^e over the collisions (τ,
e) outside the even places of Λ is zero. -/
lemma Data.IsFullMark.collisionSum_evenPlaces_eq_zero [PadicPlace p] (h : IsFullMark Λ) :
  D.collisionSum p (evenPlaces Λ) = 0 := by
  simp (disch := grind [IsCollision.ne_and_odd_and_dvd, IsCollision,
    inducedPlace_neg_pow_mul_of_odd, IsMarked, IsServed, IsFullMark]) [collisionSum, ite_eq_right]

/-- For j < m and every infinite place σ, with w = `Data.nominalWeight` σ: kw ≤ `Data.lowBoxes` j σ
≤ kw + x^60, and `Data.lowColumns` j σ ≤ w + x^60. -/
lemma Data.lowColumns_lowBoxes_bounds (hj : j < D.m) σ : D.k * D.nominalWeight σ ≤ D.lowBoxes j σ ∧
  D.lowColumns j σ ≤ D.nominalWeight σ + D.x ^ 60 ∧
  D.lowBoxes j σ ≤ D.k * D.nominalWeight σ + D.x ^ 60 := by
  obtain ⟨k : D.k ∈ range (D.n (j + 1)), _⟩ := by simp [n], D.hasLogUpper_of_le (D.n_mono hj)
  use by grw [lowBoxes, ← single_le_sum (by simp) k,
    nominalWeight_le_w_sub _ 1]; rify; gcongr; norm_cast; grind [κ]
  grw [lowColumns, lowBoxes, κ_le, κ_le]; simp [k, mul_add, ← sum_mul, sum_range_id]
  grw [D.w_le_nominalWeight_add D.nat_le_of_hasLogBound, Nat.div_le_self, sub_le]; simpa [add_assoc,
    mul_add] using ⟨D.le_of_hasLogBound, D.le_of_hasLogBound⟩

/-- For a non-split prime p < x₁, j < m and any finite set ev of infinite places,
`Data.jetExponent` p j ev is at least gain(p)/m − coll + ½(1 − χ_K(p))·#(tops in ev)·a/x₁ −
f(log b)²a/(pm), with coll = `Data.collisionSum` p ev. -/
lemma Data.le_jetExponent (hj : j < D.m) (H : D.IsSmallNonsplit p) ev :
  D.gain p / D.m - D.collisionSum p ev + (1 - chiK P.d p) / 2 * #(D.tops ∩ ev) * (D.a / D.x₁) -
  D.f * D.logB ^ 2 * (D.a / p) / D.m ≤ D.jetExponent p j ev := by
  obtain ⟨o, _, hs⟩ := q.1.two_le, D.hasLogUpper_of_le (D.n_mono hj), lowColumns_lowBoxes_bounds hj
  rw [gain, mul_div_cancel_left₀ _ (mod_cast by lia), jetExponent, mul_div_assoc]; set N :=
    boxes D.κ _
  generalize v : (D.a / p / _ : ℝ) = u; have z : N = #D.tops * D.a + ∑ σ, (D.lowBoxes j σ : ℝ) := by
    simp [N, lowBoxes, sum_ite, filter_ne', (by grind [n] : 1 < D.n (j + 1))]; simp [κ]
  have ⟨h3, _⟩ : D.x ^ 60 ≤ u ∧ 0 ≤ u := by grw [← v, H.1]; use D.le_of_hasLogBound; bound
  grw [h3.trans' (D.le_of_hasLogBound (F := D.n _ ^ 3)), ← show 5 * p.log N + 5 ≤ D.logB ^ 2 by
    grw [N.le_succ, natLog_le_logb, logb, ← o, ← one_sub_inv_le_log_of_pos, cast_succ, z, (hs
    _).2.2.trans (D.le_of_hasLogBound (G := D.gProd)),
      card_le_univ] <;> norm_num; use D.le_of_hasLogBound]
  have := Fintype.sum_mono fun σ ↦ hasSum_le (fun e ↦ ?_) ((((hasSum_sum (s := Iic (p.log N)) fun e
    _ ↦ hasSum_ite_eq e (ite (Odd e ∨ p =
    P.d) (couplingCount p D.κ (D.n (j + 1)) ev σ (D.placeOfInt (-p ^ e) * σ)
    e) 0 - 4 * u)).add ((D.summable_localAsk H.2 D.a σ).hasSum.mul_left (ite (σ ∈ D.tops) 1 0))).add
    ((D.summable_localAsk H.2 (D.nominalWeight σ) σ).hasSum.mul_left ↑D.k)).add (hasSum_ite_eq 1
    (ite (σ ∈ D.tops ∩ ev) (D.a / D.x₁) 0))) ((hasSum_live_inv_pow H.2 (D.κ σ 1 + D.lowBoxes j
    σ)).add ((hasSum_live_inv_pow H.2 D.a).summable.indicator {e | D.IsCollision p ev σ e}).hasSum)
  have : 0 ≤ 4 * D.f * u * (p.log N + 1) + D.collisionSum p ev := by rw [collisionSum]; positivity
  obtain ⟨_, h⟩ | ⟨_, h | h⟩ := chiK_cases P.d p <;> simp +contextual [sum_filter, ← mul_sum,
    IsCollision, collisionSum, h, forcedPart, κ, z, @sum_comm ℕ, localAsk, ← sum_mul, -mem_inter,
    Set.indicator, IsSmallNonsplit] at * <;> linarith
  simp [couplingCount, ↓← lowColumns.eq_1, ↓← lowBoxes.eq_1, add_div, ite_div, ite_and,
    posPart_eq_ite, κ, IsCollision, Set.indicator]; wlog h : Odd e ∨ p = P.d; grind; set σ' :=
    _ * σ; cases' e with e
  simp at h; have h6 τ := (hs τ).2.1.trans (D.le_of_hasLogBound.trans (h ▸ v.le))
  have (τ) (_ : τ ∉ D.thick) :=
    (hs τ).2.2.trans (.trans (by simpa [nominalWeight, *] using D.le_of_hasLogBound) v.le)
  grind +splitImp [tops, placeClass_of_thick, @ne_d_of_placeClass_eq _ D p 0 σ]
  have : e = 0 → D.a / D.x₁ ≤ D.a / p ^ e.succ := by bound
  have d := monotone_div_right_of_nonneg (α := ℝ) (p ^ e.succ).cast_nonneg
  grind [d D.a.cast_nonneg, min_le_left, min_le_right, nominalWeight_nonneg, d (hs σ).1,
    D.nominalWeight_mem_Icc σ', d (D.lowBoxes j σ).cast_nonneg,
    (by bound : 0 ≤ D.k * D.nominalWeight σ'), show D.lowColumns _ σ /
    p ^ e.succ ≤ u by grw [← v, (hs σ).2.1, div_right_comm]; gcongr; use D.le_of_hasLogBound; bound]

/-- For marked Λ and j < m: #Λ·δ_p + 𝔯·∑_σ `Data.lowColumns` j σ ≤ loss(p)/m + #(even tops)·a/x₁,
the sum over the even places σ (those inducing a prime in Λ), with δ_p = `Data.deltaP` p. -/
lemma Data.IsMarked.sum_lowColumns_le (hj : j < D.m) [PadicPlace p] (H :
  IsMarked Λ) : #Λ * D.deltaP p + D.ceilLogM p * ∑ σ
  ∈ evenPlaces Λ, D.lowColumns j σ ≤ D.loss p / D.m + #(D.tops ∩ evenPlaces Λ) * (D.a / D.x₁) := by
  rcases D.hasLogUpper_of_le_of_nonneg H.4.1.le, q.1.pos
  grw [cast_sum, mul_sum, sum_le_sum (g := fun σ ↦ D.a / p / D.m + ite (σ ∈ D.tops)
    (D.a / D.x₁) 0) fun σ a ↦ ?_, ← le_loss, H.card_le, deltaP]
  simp [inter_comm, ← add_assoc, field]; use D.le_of_hasLogBound
  simp at a; grw [(lowColumns_lowBoxes_bounds hj σ).2.1, nominalWeight,
    ite_eq_right (H.notMem_thick σ (.inl a))]
  obtain ⟨⟨_, _, _, e⟩, c | c⟩ := H.2 ⟨_, a⟩, le_total p D.m
  grw [c]; split <;> simpa using D.le_of_hasLogBound
  rw [ceilLogM, clog_eq_one D.nat_le_of_hasLogBound c] at *; grw [ite_eq_left (by
    grind [inducedPlace_eq_or_star_iff, H.3, tops, one_pow, o₀, orderOf_eq_one_iff]),
    add_comm]; simpa using D.le_of_hasLogBound
