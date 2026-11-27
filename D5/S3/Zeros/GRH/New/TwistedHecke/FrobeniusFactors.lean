/- GID: D5/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.TwistedHecke.FrobeniusFactors. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/TwistedHecke/FrobeniusFactors.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.TwistedHecke.RootLemma
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: An approximate projector from averages over generic matrices (see
New.TwistedHecke.ElementaryDivisors).

This file: Frobenius-power products of generic matrices: monomial weights track the excess up to
error. -/

noncomputable section

namespace TwistingData

open MvPolynomial Matrix Finsupp SetLike IsRealFiltration Ideal.Quotient Fintype Function List Nat
variable {N k W O R} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O] [CommRing R]
  (T : TwistingData N W O) (h : GL (Fin k) W) (s : ZMod N) (r ℓ n d : ℕ) (a a' : Fin k)
  (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R)

/-- The k × k matrix of polynomials over O whose (b,c) entry is the P^d-th power of the variable
labelled (s − d, b, c). -/
abbrev frobGenericMatrix := of fun b c : Fin k ↦ @X O _ _ (s - d, b, c) ^ T.P ^ d

/-- The Kronecker product over s of the n-th symmetric powers of the matrix whose row b is that
of ψ(s,m−1)⋯ψ(s,0) (s even) or its transposed adjugate (s odd), m = ℓ + `TwistingData.deepIndicator`
r (b,s). -/
def frobOperator := kroneckerPi fun s ↦ symPowMatrix n (of fun b c ↦ ite (T.isEven s) id
  (·.adjugateᵀ) ((range (ℓ + T.deepIndicator r (b, s))).map (ψ s)).reverse.prod b c)

/-- For h in GL_k(W) and a letter s, the monoid endomorphism A ↦ ι_s(h)·A·ι_s(h⁻¹) of the k × k
matrices over O, that is, conjugation by ι_s(h). -/
def letterConj := MonoidHom.mk ⟨(h.1.map (T.ι s) * · * h⁻¹.1.map (T.ι s)), by simp⟩
  (by simp [mul_assoc, ← (h.1⁻¹.map _).mul_assoc])

/-- For ℓ and indices a,a', the real function of index b equal to (indicator of b=a' minus
indicator of b=a) divided by P^ℓ. -/
def indexWeight b := (ite (b = a') 1 0 - ite (b = a) 1 0) / (T.P ^ ℓ : ℝ)

variable {r ℓ n d s a a' h ψ β γ ν}
attribute [local simp] weight_eq_sum sum_prod_type_right indexWeight letterConj mul_sub map
  Matrix.mul_apply letterMatrix deepIndicator

/-- For a ring map χ: R → O, matrices ψ(s,d) over R and block diagonal h in GL_k(W) (blocks b <
r, b ≥ r): χ applied to `TwistingData.frobOperator` of ψ equals ρ(h⁻¹)·Q·ρ(h), where Q is
`TwistingData.frobOperator` of the matrices ι_s(h)·χ(ψ(s,d))·ι_s(h⁻¹). -/
lemma frobOperator_map (χ : R →+* O) (hh : h ∈ levi W (twoBlock k r)) :
  (T.frobOperator r ℓ n ψ).map χ = T.letterRep n h⁻¹ * T.frobOperator r ℓ n (fun s d ↦
  T.letterConj h s ((ψ s d).map χ)) * T.letterRep n h := by
  simp_rw [letterRep_apply, frobOperator, ← kroneckerPi_mul, ← map_mul, ← kroneckerPi_map,
    ← symPowMatrix_map]
  congr!
  have e {M s} : .map (ite (T.isEven s) id (·.adjugateᵀ) M) χ = T.letterMatrix s h⁻¹ * ite (T.isEven
    s) id (·.adjugateᵀ) (T.letterConj h s (χ.mapMatrix M)) * T.letterMatrix s h := by
    split <;> simp [*, ← transpose_mul, adjugate_mul_distrib, mul_assoc, adjugate_mul, mul_adjugate,
      smul_smul, transpose_map, ← det_mul, ← (h.1⁻¹.map _).mul_assoc]; exact χ.map_adjugate _
  ext; erw [congrFun₂ e]
  simp [-coe_units_inv, map_list_prod, comp_def]; congr! 3
  grind [transpose_apply, twoBlock, hh _, inv_mem hh _]

/-- Let G be a decreasing multiplicative filtration, |α_{s,0}(b)| ≤ u, ∑_b α_{s,d}(b) = 0, and
ψ(s,d)_{bc} ∈ G(α_{s,d+1}(b) − α_{s,d}(c) − u) for d ≤ ℓ. Then row β of `TwistingData.frobOperator`
lies in G(x·β − Nnk(ℓ+2)u), where x(b,s) = ±α_{s,ℓ+ε}(b), + for even s, ε =
`TwistingData.deepIndicator` r (b,s). -/
lemma frobOperator_mem G [IsRealFiltration G] (α : _ → _ → Fin k → ℝ) x u (e :
  (∀ s b, |α s 0 b| ≤ u) ∧ ∀ s d, ∑ b, α s d b = 0) (hx : ∀ b s, x (b, s) =
  ite (T.isEven s) 1 (-1) * α s (ℓ + T.deepIndicator r (b, s)) b) (H : ∀ s, ∀ d ≤
  ℓ, ∀ b c, ψ s d b c ∈ G (α s (d + 1) b - α s d c - u)) (o : 0 ≤ u := by positivity) :
  T.frobOperator r ℓ n ψ β γ ∈ G (weight x (exponentOf β) - N * (n * (k * ((ℓ + 2) * u)))) :=
  antitone (by simp [← Finset.sum_mul, ← cast_sum, Monomials.degree_eq, ← degree_eq_sum,
  exponentOf]) (prod_mem_graded _ _ _ fun s _ ↦ (show _ ∈ gaussFiltration G (k * ((ℓ + 2) * u) - x
  ⟨·, s⟩) 0 by simpa [linSubst, bind₁_monomial, X, smul_monomial] using
  prod_pow_mem_graded _ 0 _ _ fun c _ ↦ sum_mem fun b _ ↦ monomial_mem_gaussFiltration (by
  simp [↓weight_single, *]
  generalize l : ℓ + _ = m
  replace l : m ≤ ℓ + 1 := by lia
  have h {b c} : ((range m).map (ψ s)).reverse.prod b c ∈ G (α s m b - (m + 1) * u) := by
    induction' m with m I generalizing b <;> simp [range_succ]
    grind [zero_mem, antitone _ (one_mem_graded G)]
    exact sum_mem fun x ↦ by grind [mul_mem_graded (H s m _ b x) (@I _ x)]
  split <;> simp [adjugate, cramer_apply, det_apply]
  exact antitone (by grw [← b.pos.nat_succ_le, l]; grind) h
  exact sum_mem fun π _ ↦ zsmul_mem
    (antitone (by simp [Finset.sum_update_of_mem]; grw [l, card_finset_fin_le]; grind)
    (prod_mem_graded G (update (α s m · - (m + 1) * u) b 0) _
    (by grind [zero_mem, updateCol_apply, transpose_apply, one_mem_graded G]))) _)) _)

lemma X_mem_gaussFiltration {σ w ω v} : @X O σ _ v ∈ gaussFiltration (adicFiltration w) ω (ω v) :=
  monomial_mem_gaussFiltration (by simp [weight_single])

omit [NeZero N] in
lemma p_dvd_cj_frobenius_sub {Y b c} : ↑T.p ∣ T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map
  (· ^ T.P ^ d)) b c - Y b c ^ T.P ^ d := let π := Ideal.Quotient.mk (.span {(_ : O)})
  let f := RingHom.mk' (π.1.comp (powMonoidHom _)) (by
    simp [← pow_mul, add_pow_prime_pow_eq T.prime, π, -map_natCast])
  (eq_zero_iff_dvd ..).1 (sub_eq_zero.2 (congrFun₂ ((by simp [← RingHom.coe_comp, ← mul_assoc,
    mul_assoc (Y.map _), show π ∘ (· ^ _) = f by rfl, show π.comp _ = f.comp
    _ by ext; simpa [← eq_zero_iff_dvd] using! T.frobenius_pow_congr d (s - d) _]) : .map _ π =
    Y.map f) ..))

/-- Let a' = a+1, Nnk(ℓ+2) ≤ P^ℓ, ℓ ≤ N, and, for j = s − d and e = P^d, ψ(s,d) =
ι_s(h)(ι_j(h)⁻¹g_jι_j(h))^{(e)}ι_s(h)⁻¹ (entrywise powers). In row β of `TwistingData.frobOperator`,
w^c divides the coefficient of ν if ν_j has equal row and column `TwistingData.indexWeight`-weights
for j ≠ i and |excess of β at i+ℓ − row weight of ν_i| > 2c+1. -/
lemma pow_dvd_coeff_conj_frobOperator (ha : a + 1 = a'.1) i (hn : N * n * k * (ℓ + 2) ≤
  T.P ^ ℓ) (hl : ℓ ≤ N) h {ψ} (hψ : ψ = fun s (d : ℕ) ↦ (map C T).letterConj h s
  (((map C T).letterConj h⁻¹ (s - d) (of fun b c ↦ X (s - d, b, c))).map (· ^ T.P ^ d))) {c : ℕ}
  (e : ∀ j ≠ i, weight (T.indexWeight ℓ a a' ·.1) (ν.curry j) = weight (T.indexWeight ℓ a a' ·.2)
  (ν.curry j)) (g : 2 * c + 1 < |weight (T.excessWeight (i + ℓ) a a') (exponentOf β) - weight
  (T.indexWeight ℓ a a' ·.1) (ν.curry i)|) : T.w ^ c ∣ (T.frobOperator a' ℓ n ψ β γ).coeff ν := by
  obtain ⟨rfl, _, _, ε, hε, g⟩ := hψ, T.prime.ne_zero, T.one_lt_P.le,
    (RCLike.exists_norm_eq_mul_self _).imp fun _ ↦ And.imp_right g.trans_eq
  let A m b := T.indexWeight ℓ a a' b * (ε / 2 * T.P ^ m / T.q)
  let ω | (j, b, c) => ite (j = i) (A N b) (A (j - i).val b - A (j - i).val c)
  have hA {m} (e : m ≤ N) b : ‖A m b‖ ≤ 2⁻¹ / T.P ^ ℓ := by
    simp [A, *, field]; split_ifs <;> simp <;> gcongr <;> lia
  refine .trans (pow_dvd_pow _ (lt_ceil.2 ?_).le) (T.frobOperator_mem (gaussFiltration
    (adicFiltration _) ω) (fun s d ↦ A (d + (s - d - i).val)) (T.excessWeight (i + ℓ) a a' · *
    (ε / 2)) _ ⟨fun _ ↦ hA (by grind), by simp [A, sub_mul, div_eq_mul_inv]⟩ (fun _ _ ↦ by
    dsimp; split_ifs <;> simp [excessWeight, rootVar, field, -one_add_val_sub_one_sub] <;> ring_nf
      <;> grind only) (fun s d hd b c ↦ have hω {v} := abs_le.1 (show |ω v| ≤ 1 / T.P ^ d by
    grw [hd]; clear_value A; grind [Real.norm_eq_abs]); have := abs_le.1 (hA (hd.trans hl) c)
      antitone (by simp [ω, ← sub_sub, add_assoc]; split <;> simp_all [A, pow_add, ← mul_div] <;>
        linarith) fun μ ↦ if q :
        _ then .trans (.pow (dvd_zero _) q) ((show _ ∈ gaussFiltration (adicFiltration _) ω _ by
    simp [← monomial_zero']
    solve_by_elim (transparency := .instances) (maxDepth := 50) [mul_mem_graded, pow_mem_graded,
      antitone hω.1 X_mem_gaussFiltration, monomial_mem_gaussFiltration,
      mem_adicFiltration_of_nonpos, (sub_self _).le, sum_mem]) μ) else
    (dvd_sub_left (pow_mem_graded _ X_mem_gaussFiltration μ)).1 (.trans (pow_dvd_pow _ (by
    clear_value ω; simp [field] at *; grind)) (T.w_sq ▸ (C_dvd_iff_dvd_coeff ..).1
    (T.map C).p_dvd_cj_frobenius_sub μ))) ..)
  grw [show (N : ℝ) * _ ≤ 2⁻¹ by field; norm_cast]
  simp_all [↓sum_prod_type, ω, A, ← mul_assoc, ← Finset.sum_mul]; bound

lemma degree_le_of_coeff_frobOperator (e : (T.frobOperator (k := k) r ℓ n
  T.frobGenericMatrix β γ).coeff ν ≠ 0) j : degree (ν.curry j) ≤ N *
    (n * (k * ((ℓ + 2) * T.P ^ ℓ))) := by
  rify; simpa [degree_eq_sum] using (mt zero_pow (ne_zero_of_dvd_ne_zero e (T.frobOperator_mem
    (gaussFiltration _ (if ·.1 = j then -1 else 0)) 0 0 _ (by simp) (by simp) (fun s d h _ _ ↦
    antitone (by grw [← h] <;> bound [T.prime.pos]) (pow_mem_graded _ X_mem_gaussFiltration)) ..)))
