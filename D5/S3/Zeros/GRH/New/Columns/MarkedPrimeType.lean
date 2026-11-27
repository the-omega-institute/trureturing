/- GID: D5/S3/Zeros/GRH/New/Columns/MarkedPrimeType
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/MarkedPrimeType
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.MarkedPrimeType. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/MarkedPrimeType.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Columns.TwistedHeckeType
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Scaled Hecke operators repair divisibility at inert primes pairing tops (see
New.Columns.LocalStatement).

This file: Scaled Hecke operator at a marked prime has image of small index on columns. -/

namespace Data

open Finset ZMod Nat Columns Parameters RingHom Module Real IsLocalization AtPrime

/-- For Λ marked at p, l in Λ and any s, the operator p^{A_l}T_{l,𝔯} (`Data.IsMarked.markOperator`)
keeps the integral columns and is onto modulo p^s up to an index of exponent at most (128A_l log
b/(mp) + s/x^14 + x^40)·dim(columns) (`HasType`). -/
theorem IsMarked.hasType_markOperator {P p} {D : Data P} [h₀ : Fact p.Prime] [PadicPlace p] {Λ}
    (hΛ : D.IsMarked Λ) s {l} (hl : l ∈ Λ) :
  HasType ↑p D.integralColumns s (hΛ.markOperator ⟨l, hl⟩) ((128 * D.markExponent l *
  (D.logB / (D.m * p)) + 1 / D.x ^ 14 * s + D.x ^ 40) * finrank ℂ D.Column) := by
  obtain ⟨hL, -, hd, hx⟩ := hΛ.2 ⟨l, hl⟩; set d := D.o₀ p; let c := D.placeOfInt (-p) ^ d
  obtain ⟨hs, ⟨τ, _, e⟩, ⟨z, hz⟩, hm, h', _, _, _, _, hN, hu : ¬IsUnit (p : embValRing), hW, r0⟩ :=
    (hΛ.2 ⟨l, hl⟩).m_dvd_orderOf, hΛ.3 l hl, (Complex.isSquare p).exists_sq, hΛ.p_mem hl,
    hΛ.star_ne hl, P.thirteen_le_of_chiK_ne_one h₀.1 (by lia), NeZero.of_pos (orderOf_pos c),
    D.hasLogUpper_of_le hx, D.hasLogUpper_of_le (orderOf_le_card_univ
    (x := c)), (by grind [o₀, orderOf_map_dvd, orderOf_pow_of_dvd, Nat.mul_div_cancel'] : orderOf
    (D.placeOfInt (-p)) = d * orderOf c), (Valuation.mem_maximalIdeal_iff ..).2 (by simpa using!
    norm_p_lt_one), l.valuationSubringAtPrime_eq_valuationSubring (K := D.E), hd.pos.trans_le hx
  let t (s : ZMod (orderOf c)) := c ^ s.val * τ; have ht s : t (s + 1) =
    D.placeOfInt (-p ^ d) * t s := by simp [t, ← hd.neg_pow, ← placeOfInt_pow, c, _root_.pow_succ',
    val_add, val_one_eq_one_mod, mul_assoc]
  have hi : t.Injective := fun _ _ ↦ by simp [t, pow_inj_mod, ← natCast_eq_natCast_iff']
  have hS σ : σ ∈ Set.range t ↔ σ ∈ D.tops ∧ (inducedPlace σ = l ∨ inducedPlace σ = star l) := by
    simp [t, natCast_zmod_surjective.exists, ← e, inducedPlace_eq_or_star_iff, hL]; simp [c,
      ← pow_mul]
    grind [o₀, tops, =_ orderOf_dvd_iff_pow_eq_one, dvd_def]
  have := CharP.quotient _ p hu; let v s := inducedPlace (t s) == l; have w s :=
    ((hS _).1 ⟨s, rfl⟩).2
  let g s : l.valuationSubringAtPrime D.E →+* embValRing := .restrict (ite (v s) (Φ (t s)) (comp (Φ
    (t s)) (starRingEnd _))) _ _ fun x h ↦ (isEquiv_placeOfEmb (ιₚ.comp _)).le_one_iff_le_one.2
    <| by cases w s <;> simp_all [v, ← comp_assoc, placeOfEmb_comp_star, inducedPlace]
  let ψ s := comp (Ideal.Quotient.mk (.span {↑p})) (g s)
  let T : TwistingData .. :=
    ⟨p, d, g, v, ⟨z, by simpa [hz, pow_le_one_iff] using (p : embValRing).2⟩, h₀.1, by
    grind [le_pow], Subtype.ext hz.symm, fun s x ↦ Ideal.mk_span_eq_iff_dvd_sub.1
    (RingHom.congr_fun (ringHom_ext l.1.primeCompl (ext (star_involutive.surjective.forall.2 fun a ↦
    .trans (congrArg (Quot.mk _) (Subtype.ext (show (_ : D.E →+* ℂ) (star a) = (_ : D.E →+* ℂ)
    (galOfPlaceInt _ a) by cases w s <;> simp [v, *, ← phi_mul, @starRingEnd_apply D.E, mul_comm (t
    s), inducedPlace_neg_pow_mul_of_odd]))) ((frob_ext (by grind [chiK_eq_one_of_dvd, Fact])
    (comp (ψ s) (algebraMap ..)) d (.inr ⟨rfl, rfl⟩)).2 ⟨rfl, by simp [*]⟩ a))) : ψ _ =
    comp (iterateFrobenius ..) (ψ _)) x), by grind [star_star, inducedPlace_neg_pow_mul_of_odd],
    (card_congr (equivQuotMaximalIdeal ..).1).symm.trans ((q_eq_inert hm
    hL).trans (by rw [lcm_eq_left (D.m_even.two_dvd.trans hs), hN, pow_mul]))⟩
  have A : markExponent l =
    D.a * #{s | T.isEven s} := by rw [markExponent, ← card_image_of_injective _ hi]; congr; grind
  have e := card_add_card_compl {s | T.isEven s}
  rw [@card_equiv _ _ _ᶜ {s | T.isEven s} (.addRight 1) (by simp [T.isEven_succ]), ZMod.card] at e
  apply Columns.hasType_markOperator hΛ hl hW T hu rfl (.ofInjective t hi) hS (by tauto) A (⟨r0,
    D.nat_le_of_hasLogBound, D.le_of_hasLogBound, D.le_of_hasLogBound, e, ?_, D.le_of_hasLogBound,
    D.le_of_hasLogBound, ?_, mul_le_mul (mod_cast by nlinarith) ?_ ?_ ?_⟩ : HeckeSizes (p ^ d) ..)
  grw [← (by lia : 3 * 3 ≤ p), mul_pow, mul_pow, ← pow_add, e, ← pow_mul, le_self_add.trans_eq e]
  rify; grw [← exp_one_lt_three.le, exp_one_pow, ← hN, ← le_of_dvd (orderOf_pos _) hs,
    ← (D.le_of_hasLogBound : D.logB * 2 ≤ D.m)]; use D.lt_of_hasLogBound
  grw [p.cast_pow, hΛ.4.1,
    @le_exp_of_log_le ((_ ^ d) ^ _) (D.logB / 2) (by simpa using D.le_of_hasLogBound)]
  use D.le_of_hasLogBound
  grw (transparency := default) [← le_pow hd.pos, ← (lt_two_mul_self r0).nat_succ_le, pow_succ,
    ← p.cast_pow, ← le_pow_clog h₀.1.one_lt]
  field_simp; use D.le_of_hasLogBound; all_goals bound [D.le_m, h₀.1.pos]
