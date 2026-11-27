/- GID: D5/S3/Zeros/GRH/New/Selmer/ThickSpacing
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/ThickSpacing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.ThickSpacing. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/ThickSpacing.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.DeterminantBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Spacing lemma: no three thick places (`Data.thick`) in a short Frobenius arc;
thick embeddings have the same sign if ℓ divides `Data.cycloConductor`. -/


open Fact Int ZMod IsCyclotomicExtension Parameters IsAlgClosed
variable {P} {D : Data P} {ℓ} [hp : Fact ℓ.Prime] {e : D.E →+* PadicAlgCl ℓ} {g g' g₁ : Gp ℓ}

lemma fixes_emb_of_fixes_rootsOfUnity (H : ∀ ζ, ζ ^ D.cycloConductor = 1 → g ζ = ζ) x : g (e x) =
  e x := have := (@toCycloField P D.s).toAlgebra
  (surjective_domRestrict_of_isAlgebraic e.toRatAlgHom).elim fun ψ E ↦ congr($E x) ▸ congr($(((
  zeta_spec D.cycloConductor ℚ (cycloField D.cycloConductor)).powerBasis _).algHom_ext
  (f := .comp (g.restrictScalars ℚ) ψ) (by simp [H, ← map_pow, zeta_pow])) _)

lemma cmSign_spec (σ : D.E →+* _) : σ (P.sqrtNegDInE D.s) = cmSign σ * QuadField.sqrtNegD P.d ∧
  Φ (.mk σ) (P.ζ _) = σ (P.ζ _) ^ (cmSign σ).1 := by cases Φ_eq_or σ with exact ‹_› ▸ (by
       simp [cmSign, ← RCLike.star_def, ← map_star_complex])

variable [PadicIso ℓ] {a i n} (t : .mk (complexEmbOf e g) ∈ D.thick) (t' : .mk (complexEmbOf e g') ∈
  D.thick) (h : (g' * g⁻¹) (e (P.ζ _) ^ ℓ ^ a) = (e (P.ζ D.s) ^ ℓ ^ a) ^ ℓ ^ n)
include h

variable (e g g' a n) in
/-- Let g'g⁻¹ raise e(ζ)^{ℓ^a} to the power ℓ^n, and y be the ratio of the infinite places of
the embeddings read by g and g'. Modulo any m ∣ N₁ prime to ℓ^a, y ≡ ±ℓ^n, the sign being
the product of their signs. -/
lemma placeClass_ratio {y} m d (c : (ℓ ^ a).Coprime m) (hy : .mk (complexEmbOf e g') * y =
  .mk (complexEmbOf e g) := by apply mul_div_cancel) : (@placeClass P _ m d y).1 =
  (cmSign (complexEmbOf e g) * cmSign (complexEmbOf e g') : ℤ) * ℓ ^ n := by
  have E := congr((g' (ιℓ $(hy ▸ phi_mul _ _ (ζ ..))) ^ (cmSign (complexEmbOf e g')).1) ^ ℓ ^ a)
  simp [galOfPlace_zeta, cmSign_spec, complexEmbOf, ← zpow_natCast, ← zpow_mul] at *
  rw [zpow_mul', h, ← zpow_mul, mul_rotate, ← div_eq_one_iff_eq, ← zpow_sub₀, ← sub_mul,
    (isPrimitiveRoot_zeta.map_of_injective e.injective).zpow_eq_one_iff_dvd] at E
  simpa [placeClass, unitsMap, mul_comm, ↓← mul_assoc, ← intCast_eq_intCast_iff_dvd_sub] using
    c.symm.cast.dvd_of_dvd_mul_right (d.natCast.trans E)
  repeat simp [isPrimitiveRoot_zeta.ne_zero, NeZero.ne, zpow_ne_zero]

include t t'

/-- Spacing: let ℓ ≤ kt, 0 < i < n ≤ 27s, and g'g⁻¹, g'g₁⁻¹ raise e(ζ)^{ℓ^a} to the powers ℓ^n,
ℓ^i. If the embeddings read by g and g' are thick, that read by g₁ is not. -/
lemma not_thick_of_short_arc (h₁ : (g' * g₁⁻¹) (e (P.ζ _) ^ ℓ ^ a) =
  (e (P.ζ _) ^ ℓ ^ a) ^ ℓ ^ i) (hk : ℓ ≤ D.k * D.t) (hi : 0 < i) (hn : i < n) (hL : n ≤ 27 * D.s) :
  .mk (complexEmbOf e g₁) ∉ D.thick := fun u ↦ by
  have A {g n m} h d c := congr($(placeClass_ratio e g g' a n h m d c) ^ 2)
  simp [mul_pow, ← Int.cast_pow, isUnit_sq, -map_pow] at A
  obtain rfl | o := hp.1.eq_two_or_odd'
  · grind [@orderOf_one_add_prime 3 out nofun _ ▸ orderOf_le_of_pow_eq_one hi (.trans (by norm_num
      [← mul_pow, sq]) ((A h₁ ⟨_, mul_left_comm ..⟩ (.pow _ _ rfl)).symm.trans
      (by simp [D.thick_eq_neg_one_mod, *]))), @Nat.lt_pow_succ_log_self 3 out D.s]
  exact (@two_pow_le_of_pow_eq_one ℓ hp.1.one_lt (i * 2) _ (by lia) (by rw [Int.cast_natCast,
    pow_mul, ← A h₁ two_pow_dvd_N₁, ← map_div, D.three_term (2 * i) (2 * n) _ _ _ _ t'
    _ u _ t] <;> first | lia | simp [Units.ext_iff, pow_mul, A h, A h₁, o.pow] <;> ring)).not_gt
    (by grw [natAbs_natCast, hk, hn, hL]; use D.nat_le_of_hasLogBound)

omit h

/-- Let the prime ℓ divide N₁d and e embed E in Q̄_ℓ. If the complex embeddings `complexEmbOf e g`
and `complexEmbOf e g'` (g, g' in G_ℓ) both define thick places, then both or neither belong to the
CM type. -/
lemma cmSign_eq_of_thick (c : ℓ ∣ D.cycloConductor) : cmSign (complexEmbOf e g) =
  cmSign (complexEmbOf e g') := units_ne_iff_eq_neg.not_right.2 fun _ ↦ if b : ℓ ∣ D.N₁ then by
    let x := e (P.c₀InE D.s)
    rcases congr(g (ιℓ ($((cmSign_spec (complexEmbOf e g)).1) + $((cmSign_spec
      (complexEmbOf e g')).1)))), P.dvd_norm_c₀ out b, congr(‖e $(P.c₀InE_mul_one_sub D.s)‖),
      IsUltrametricDist.norm_add_le_max x (1 - x), dist_smul (g * g'⁻¹) x 0
    simp_all [sqrtNegDInE, map_ofNat, complexEmbOf, ← Padic.norm_natCast_lt_one_iff,
      ← PadicAlgCl.norm_extends]
    grind [sq_nonneg (‖x‖ - 1), sq] else (exists_apply_eq_pow b (by simp [← map_pow,
  isPrimitiveRoot_zeta.1]) _).elim fun n ↦ mt (placeClass_ratio e g g' 0 n · _ ⟨_, rfl⟩ (by simp))
  (by simp_all [D.placeClass_of_thick, hp.1.dvd_mul, Nat.prime_dvd_prime_iff_eq, out]; grind
  [pow_d_ne_neg_one])
