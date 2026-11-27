/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Green/GreenTau
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Green/GreenTau
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Green.GreenTau. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Green/GreenTau.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Green.CuspidalInnerProduct
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Cuspidality, independence of choices and orthogonality of the characters of irreducible
polynomials. -/


open Polynomial Hall IsAlgClosed Classical FiniteField LinearMap Finset minpoly Multiset Module
  UniqueFactorizationMonoid ComplexConjugate AdjoinRoot
variable {k K : Type _} [Field k] [Finite k] [Field K] [Algebra k K] {T : MulChar K ℂ}
  {P : k[X]} (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0) {x : K}
  (hx : P.aeval x = 0)

@[simp] lemma labelChar_eq_greenTau (T : MulChar K ℂ) (hP : Irreducible P) (hm : P.Monic) :
  labelChar T P = greenTau T P
  := by simp [labelChar, normalizedFactors_irreducible hP, hm.normalize_eq_self, hP.ne_zero]

attribute [local simp] greenTau rankInner Hall.ext_iff charpoly_natDegree thetaChar_charName
  blockAverage Finite.one_lt_card aeval_algHom_apply coe_frobeniusAlgHom

/-- For every polynomial P and multiplicative character T of K, τ_P is cuspidal: its mean over block
triangular matrices with given diagonal blocks vanishes whenever both blocks have nonzero
dimension. -/
lemma isCuspidal_greenTau : (greenTau T P).IsCuspidal := fun _ ↦ by
  simp_intro ..; split <;> simp; apply_rules [isCuspidal_greenCuspidal]

lemma greenTau_eq_zero_of_dim_ne c : c.dim ≠ P.natDegree → greenTau T P c = 0 := by aesop

variable [IsFaithfulMulChar K T]

/-- If the endomorphism σ of L is y ↦ y^(q^i) with q = |k|, then the roots of σP in the
algebraically closed field K are the q^i-th powers of the roots of P, with multiplicity. -/
lemma aroots_map_frobenius_pow [IsAlgClosed K] {L} [Field L] [Algebra L K] {i} (σ : L →+* L)
    (h : ∀ y, σ y = y ^ .card k ^ i) (P : L[X]) :
    (P.map σ).aroots K = (P.aroots K).map (· ^ .card k ^ i) := by
  open Fint in convert (splits _).roots_map (frobeniusAlgHom k K ^ i).1 <;> aesop

include hP h0 hx

lemma root_pow_card_pow_pred_eq_one : x ^ (.card k ^ P.natDegree - 1) = 1 ∧ 2 ≤
  .card k ^ P.natDegree := by aesop (add simp [(root_pow_card_pow_eq_self_iff hP), Nat.succ_le_iff,
  hP.natDegree_pos.ne', aeval_def])

omit [IsFaithfulMulChar K T] in
lemma rankPart_greenCuspidal_pow {a} [NeZero a] : let d := P.natDegree; (greenCuspidal k
    (thetaChar T (.card k ^ d) (x ^ a))).rankPart d = (greenCuspidal k (thetaChar T (.card k ^ d)
    x <| · ^ a)).rankPart d := by
  simp [Hall.ext_iff]; intros; split_ifs <;> [subst_vars; rfl]
  rw [greenCuspidal_congr, one_mul]; intro z; by_cases z =
  0 <;> simp_all [thetaChar_eq_apply_norm_pow T _ _ _ (pow_one _).symm rfl,
  root_pow_card_pow_pred_eq_one hP h0 hx, MulChar.map_zero, NeZero.ne]

/-- For T injective, P irreducible of degree d over the finite field k with P(0) ≠ 0, and any
root x of P in the algebraically closed field K: τ_P = (−1)^d times the rank d part of
C_{θ_x}, θ_x taken for Q = |k|^d. -/
lemma greenTau_eq : let d := P.natDegree
  greenTau T P = (-1 : ℂ) ^ d • (greenCuspidal k (thetaChar T (.card k ^ d) x)).rankPart d := by
  rw [greenTau, ← (exists_pow_card_pow_eq_of_root hP hx (@epsilon_spec _ (P.aeval · = 0) ⟨x,
    hx⟩)).choose_spec.2, rankPart_greenCuspidal_pow hP h0 hx]
  delta greenCuspidal brauerLift; congr! 6
  open Fint in erw [← Multiset.map_map, ← aroots_map_frobenius_pow (.id k)] <;> simp [pow_card_pow]

omit hx
seal rankInner finrank

/-- Let T be injective, P monic irreducible, P(0) ≠ 0. On GL_{deg P}(k), ⟨τ_P,τ_S⟩ is 1 if P =
S, else 0, for S monic irreducible with S(0) ≠ 0; if P(1) ≠ 0, `Hall.skew` of τ_P in
degree deg P kills the constant function 1. -/
lemma rankInner_greenTau (hm : P.Monic) : (∀ S, Irreducible S → S.Monic → S.coeff 0 ≠ 0 →
  rankInner P.natDegree (greenTau T P) (greenTau T S) = ite (P = S) 1 0) ∧
  (P.eval 1 ≠ 0 → skew P.natDegree (greenTau T P) constOne = 0) := by
  have := NeZero.of_pos hP.natDegree_pos; let L := Extension k _ P.natDegree
  let := (lift : L →ₐ[k] K).toAlgebra; have r : _ = finrank k L := (finrank_extension ..).symm
  let j χ := algebraMap L K (charName T χ).1
  have R {S : k[X]} (i : Fact (Irreducible S)) (z : S.coeff 0 ≠ 0) h : ∃ χ, S.aeval (j χ) = 0 :=
    ⟨(charName T).symm (.map (algEquivExtension k _ _ _ (finrank_quotient_span_eq_natDegree.trans
    h)).toMonoidHom (.mk0 (root S) (z <| by simpa [·] using eval₂_root S))), by simp [j]⟩
  have ⟨χ, a⟩ := R ⟨hP⟩ h0 rfl
  have o ξ : @finMean Lˣ (fun z ↦ conj (χ z) * ξ z) = ite (j χ = j ξ) 1 0 := by
    open Fint in simpa [finMean, field, ← χ.star_apply', ← @inv_mul_eq_one _ _ χ, j, Units.val_inj,
      MulChar.ext_iff, MonoidHom.ext_iff] using sum_hom_units ((χ⁻¹ * ξ).comp (Units.coeHom L))
  have p B := rankInner_greenCuspidal_mulMu (thetaChar T (.card L) (j χ)) (IsScalarTower.toAlgHom k
    L _) B ▸ rankInner_mul_of_isCuspidal
    (H := constOne) (isCuspidal_greenCuspidal _) finrank_pos.ne'
  rw [greenTau_eq hP h0 a, r, ← natCard_eq_pow_finrank]
  use fun S i m z ↦ byCases (R ⟨i⟩ z · |>.rec fun ξ b ↦ by
    rw [show ite .. = ↑(count (j χ) (S.aroots K)) by simp [eq_comm, i.ne_zero, ↓mem_aroots, *,
      ↓count_eq_of_nodup (nodup_roots (PerfectField.ofFinite.1 i).map),
      eq_iff_aeval_eq_zero, eq_of_irreducible_of_monic hP a hm], greenTau_eq i z b]
    simpa [fun (u : L) i ↦ charpoly_eq_pow_of_isNilpotent (g := mulLeft k u) (irreducible (x :=
      u) i) (monic i) (aeval_algHom k (Algebra.lmul k L) u ▸ .zero) ▸ aroots_pow_eq_frobenius_orbit
      (irreducible i) (x := algebraMap L K u) (by simp), IsIntegral.of_finite,
      aroots_eq_frobenius_orbit i b, *, mulMu, j, mul_sum, eq_one_of_monic_natDegree_zero,
      ← range_val, finMean_sum, ← mul_pow, ← ξ.pow_apply_coe, count_map,
      mul_mul_mul_comm _ (conj _), ← natCard_eq_pow_finrank, charpoly_monic] using! p (brauerLift k
      (thetaChar T (.card L) (j ξ)))) (by aesop), fun h ↦ by simpa [by simpa using (o 1).trans (by
       aesop (add simp aeval_def)), mulMu.eq_unfold, mu_mul_constOne, skew, j,
    finrank_pos.ne'] using (p constOne).symm
