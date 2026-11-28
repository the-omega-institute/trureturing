/- GID: D5/S3/Zeros/GRH/New/Data/DataExist
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/DataExist
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.DataExist. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/DataExist.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Endgame.OneSidedCriterion
import D5.S3.Zeros.GRH.New.Seesaw.IndexTypes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Known result: Behrend's construction for several equations at once. Here all ratios up to a given
bound are avoided at once, in a coset of a cyclic group seen through a homomorphism, with the
explicit count of points on a sphere. Source: Shapira, Behrend-type constructions for sets of linear
equations, Acta Arith. 2006, Thm 1 (after Behrend, PNAS 32, 1946).

This file: Admissible data exist for large x; Behrend sets and class-group pigeonhole as inputs. -/


open Finset Behrend Real Filter NumberField ClassGroup NeZero QuadField

/-- Behrend: let φ : G → H map commutative groups, L > 0, (LM)ⁿ ≤ ord φ(g). Some finite T ⊆
{cgᵉ} has |T| ≥ Mⁿ/(nM²), and σ, σy, σz ∈ T, φ(y)ʲ = φ(z)ⁱ, 0 < i < j ≤ L force φ(y) = 1.

Known result: Behrend's construction for several equations at once. -/
lemma exists_three_term_free {G H} [CommGroup G] [CommGroup H] (φ : G →* H) c g (n M L : ℕ)
    (hL : 0 < L) (h : (L * M) ^ n ≤ orderOf (φ g)) : ∃ T, (∀ σ ∈ T, ∃ e, σ = c * g ^ e) ∧
    (M ^ n / (n * M ^ 2) : ℝ) ≤ #T ∧ ∀ i j, 0 < i → i < j → j ≤ L → ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T, φ
    (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1 := (exists_large_sphere n M).elim fun k _ ↦ by
  have := pow_injOn_Iio_orderOf.comp map_injOn fun _ k ↦ h.trans' (finFunctionFinEquiv (⟨_, k ·⟩)).2
  use image (c * g ^ map (L * M) ·) (sphere n M k)
  rw [card_image_iff.2 fun _ a _ b _ ↦ this.mono (fun v k ↦ show ∀ i, _ from fun i ↦ ?_)
    a b ?_] <;> simp_all
    [← map_pow, sphere, Behrend.box, -map_apply, ↓forall_mem_image] <;> try nlinarith [k.1 i]
  intro i j _ o _ u hu _ v hv _ w hw _ H
  obtain ⟨a, ha, rfl⟩ := lt_iff_exists_add.1 o
  have e := @this ((i + a) • v) (by simp; nlinarith [hv ·]) (i • w + a • u)
    (by simp; nlinarith [hu ·, hw ‹_›]) (by simpa [pow_add, pow_mul', ↓div_pow,
    div_eq_iff_eq_mul, ← mul_assoc, -map_apply, -nsmul_eq_mul] using H)
  simp [by simpa [← mul_sum, *, ← add_mul, ha.ne', mul_left_comm i] using show
    ∑ l, (i + a) * (a * Int.natAbs (u l - v l) ^ 2 + i * v l ^ 2) =
    ∑ l, i * (i * w l ^ 2 + a * u l ^ 2) by simp [funext_iff] at e; zify at *; grind]

/-- Pigeonhole in the class group: among h + 1 pairs of prime ideals (I_i, J_i) of a number
field of class number h, with every I_i J_i principal, there are i ≠ j with I_i J_j
principal. -/
lemma exists_mul_principal {K} [Field K] [NumberField K] {I J : Fin (classNumber K + 1) → FinPlace
  K} (H : ∀ i, ((I i).1 * (J i).1).IsPrincipal) : ∃ i j, i ≠ j ∧ ((I i).1 * (J j).1).IsPrincipal :=
  let c (v : FinPlace K) := mk0 ⟨_, mem_nonZeroDivisors_of_ne_zero v.3⟩
  have e v w : _ ↔ c v * c w = 1 := by rw [← map_mul, mk0_eq_one_iff]
  by simp_all; grind [Fintype.exists_ne_map_eq_of_card_lt (c ∘ I) (card_fin _).ge]

/-- Let 0 < ε < 1/100. For all large x there are admissible data with scale x, log x₁ = x^{ε/6}
≥ (10⁶ log x)², log log b = ε log x, and at least 3^c 2^s / log b thick places. -/
lemma exists_data P {ε : ℝ} (e0 : 0 < ε / 6) (e1 : ε < 1 / 100) : ∀ᶠ x in atTop, ∃ D : Data P,
    D.x = x ∧ log D.x₁ = x ^ (ε / 6) ∧ (1e6 * log x) ^ 2 ≤ log D.x₁ ∧
    log (log D.b) = ε * log x ∧ towerDeg D.s / log D.b ≤ #D.thick := by
  have ⟨n, h⟩ := exists_nat_gt (99 * P.N₀ * P.d / (ε / 6) ⊔ 6)
  have E (k : ℕ) := tendsto_exp_mul_div_rpow_atTop k _ e0
  have ev k c := E k (mem_atTop c)
  rw [← map_exp_atTop, eventually_map]
  filter_upwards [E 0 (exists_prime_modEq_one_log_mem (P.N₀ * P.d) n (by grind [Parameters])),
    ev 2 1e12, ev (n + 1)
    ((P.N₀ * 8019 + 2) * 10368 ^ n), mem_atTop 1, ev 0 (2 * classNumber P.K + 1e6), Ioi_mem_atTop 0,
    mem_atTop 2, ev 0 (1e12 * P.c).exp, ev 1 (8019 * 2 ^ n * n)] with x hg h3 hL lx h5 x0 _ hf hC
  simp_all [↓rpow_natCast, le_div_iff₀, div_lt_iff₀, ← exp_mul, mul_comm x]
  have N (x y : ℝ) (e : 1 ≤ x := by simp; bound) (h : 1 < y := by simp) := exists_nat_pow_near e h
  obtain ⟨⟨h, n0⟩, ⟨o, m1, m2⟩, e, r1, r2⟩ := h, N (x / 2).exp 2, N (5 * x).exp 3
  let s := (o + 1) * 22
  have s8 : s ≤ 32 * x := by simp [s, pow_le_iff_le_log, exp_pos] at *; nlinarith [log_two_gt_d9]
  have W0 := exp_pos (ε / 6 * x)
  have ⟨k, k1, k2⟩ := N (2 ^ s / _) (2 ^ n) ((one_le_div W0).2 (by
    grw [pow_mul, ← le_self_pow₀, ← m2, e1] <;> bound)) (mod_cast by grind)
  set W := exp (_ * x)
  have Y i j (h : i ≤ j := by lia) : W ^ i ≤ W ^ j := by bound
  have s6 := @pow_le_of_le_log ((P.N₀ * P.d) ^ ((s + 6) * 2)) W n W0 (by
    grw [log_pow, log_exp, ← mul_assoc, ← h, log_le_self] <;> simp [field]; grind)
  have s5 : 2 ^ s ≤ W ^ n := s6.trans' (mod_cast by gcongr <;> nlinarith only [P.lt_d, pos P.N₀])
  obtain ⟨hg, w2⟩ := hg _ (by lia) s6, Y 2 6
  simp [pow_mul, field] at hg k2
  choose i1 p hp hm l u using fun i : Fin (classNumber P.K + 1) ↦ have : 0 ≤ i * W ∧ (i + 1) * W * 2
    ≤ W ^ 2 := ⟨by bound, by grw [i.is_le]; nlinarith only [h5]⟩; And.intro this (hg (10 * W ^ 6
    + 2 * i * W) (by bound) (by nlinarith only [this, Y 7 n, w2, h5]))
  have hN i := (hm i).of_dvd (P.N₁_mul_d_dvd_M_omega.pow out)
  choose I J nI nJ eJ using fun i ↦ have := Fact.mk (hp i); (FinPlace.exists_natCast_mem P.K
      (p i)).imp fun w h ↦ (prime_inert_or_eq_mul w h).imp fun _ ↦
      (·.2.resolve_left (by simp [(q_eq_iff_legendreSym_ne_neg_one w h).2, sq,
      P.chiK_eq_one_of_modEq_one (hN i), (hp i).ne_one]))
  have ⟨i, j, ne, α, hα⟩ := exists_mul_principal (⟨_, eJ · |>.symm⟩)
  let M := P.N₀ * 3 ^ (Nat.log 3 s + 5)
  have := @Parameters.placeClass_placeOfInt P s (M + 1) (mod_cast by simp [M])
  have ⟨T, t1, t2, t⟩ := exists_three_term_free (P.placeClass P.two_pow_dvd_N₁) (P.placeOfInt s
    (-1)) (P.placeOfInt s (M + 1)) n (2 ^ k) (324 * s) (by lia) (le_of_mul_le_mul_left (.trans (by
    unfold M; norm_cast; grw [pow_add, Nat.pow_log_le_add_one]; rify
    grw [← (le_div_iff₀ W0).1 k1, lx, ← hL, s8, s8]; ring; rfl)
    (@two_pow_le_of_pow_eq_one (M + 1) (mod_cast by
    simp) _ s (orderOf_pos _) (this ▸ Units.ext_iff.1 (pow_orderOf_eq_one _)))) (pos _))
  refine ⟨⟨_, W ^ 6, W, s, _, _, s8, T, p ∘ ![i, j], α, ?_, ?_, ?_, ⟨o, rfl, rfl⟩, ⟨e, rfl⟩,
    fun _ k ↦ (by cases t1 · ·; simp [*, P.placeClass_placeOfInt isCoprime_one_left.neg_left,
    Units.ext_iff, (ZMod.natCast_eq_zero_iff M _).2 k]), t, ?_, ?_, fun _ ↦ (hm _).symm.dvd',
    (Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    rify; grw [← log_lt_log_iff, u, ← l] <;> simp [(hp _).pos]; bound).injective.comp
    (by simpa), by
    simp [pow_le_iff_le_log, le_pow_iff_log_le, (hp _).pos, exp_pos]; grind, ?_, ?_⟩, ?_⟩ <;>
    simp [m2.le, r2.le, ← absNorm_span_eq_mul_star, ← hα, nI, nJ, hp, hN]
  simp [W]; and_intros <;> nlinarith only [e0, e1, w2, lx, h3, hf, h5]
  iterate 2 simpa [pow_succ']
  grw [← le_sqrt_of_sq_le w2]; intros
  apply hg <;> grind
  use by bound, by simp [W, field]
  grw [← t2, towerDeg, pow_add, Nat.pow_log_le_add_one]; simp; grw [k2, s8, pow_succ,
    pow_right_comm]
  field; grw [(lt_of_pow_lt_pow_left₀ n W0.le (by grw [← s5, pow_right_comm, k1]; bound) :), lx]
  nlinarith only [hC, Y 3 5]
