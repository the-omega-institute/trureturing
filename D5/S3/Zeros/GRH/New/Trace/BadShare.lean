/- GID: D5/S3/Zeros/GRH/New/Trace/BadShare
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Trace/BadShare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Trace.BadShare. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Trace/BadShare.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.CentralConvolution
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Bad types have small share in the regular representation. For a product of groups GL_r(F_q),
types that are not good have share at most a multiple of 1/q per factor plus a term decaying
exponentially in the number of factors. This is a standard computation of Plancherel shares from
Green's degree formula and counts of squarefree and primitive polynomials over F_q, followed by a
union bound over the factors. Related work: Green, The characters of the finite general linear
groups, 1955; Dudko, Plancherel measures for GL(n,q), arXiv 0806.1345, 2008; Lidl–Niederreiter,
Finite Fields, ch. 3, 1983.

Good types and cubic twists of cuspidal characters. For r = 3, 9, 27, … and q ≡ 1 mod 9, a cuspidal
character of GL_r(F_q) from a faithful character of F_{q^r}^× has a cubic twist of the same kind
that avoids two given ones and agrees with it off irreducible characteristic polynomials. The twist
claim holds because cuspidal characters vanish off powers of irreducible polynomials by Green's
character table and the determinant is a cube for proper powers, and the rest is finite-field
counting. Related work: Green, The characters of the finite general linear groups, 1955;
Lidl–Niederreiter, Finite Fields, ch. 2–3, 1983.

This file: The bound `bad_share_le` for the share of bad types. Primitive labels: stable under
scaling of roots; norm of a generator generates. A
primitive cuspidal character has a cubic twist agreeing off irreducible characteristic
polynomials. -/

open Polynomial Finset Nat Fint Fintype Real minpoly ComplexOrder AlgebraicClosure
variable {k} [Field k] [Finite k] {c : k[X]} (a : kˣ) {r}

/-- c is a primitive label of degree r: an irreducible label of degree r (`IsLabel`) with a
root of multiplicative order q^r − 1 in the algebraic closure, q = |k|. -/
def IsPrimitiveLabel r (c : k[X]) := IsLabel r c ∧ Irreducible c ∧
  ∃ ξ : AlgebraicClosure k, c.aeval ξ = 0 ∧ IsPrimitiveRoot ξ (.card k ^ r - 1)

/-- Let a ∈ k^× with a^M = 1, M ≥ 1 and M² dividing |k| − 1. If c is primitive for r
(irreducible, with a root of order |k|^r − 1), so is the polynomial whose roots are a times
those of c. -/
lemma IsPrimitiveLabel.scaleRoots {M} (ha : a.1 ^ M = 1) (hM : M ^ 2 ∣ .card k - 1) :
  IsPrimitiveLabel r c → IsPrimitiveLabel r (c.scaleRoots a) := fun ⟨L@⟨_, _, rfl, z⟩, I, ξ, w, h⟩ ↦
  ⟨L.scaleRoots a, I.map
  (scaleRootsEquiv a), _, scaleRoots_aeval_eq_zero w, h.eq_orderOf ▸ .iff_orderOf.2 ((Commute.all
  ..).orderOf_mul_eq_right_of_forall_prime_mul_dvd (h.isOfFinOrder (sub_ne_zero_of_lt
  (root_pow_card_pow_pred_eq_one I z w).2)) fun _ _ d ↦ by grw [d, ← sq, orderOf_dvd_of_pow_eq_one
  (by rw [← map_pow, ha, map_one]), hM, ← h.eq_orderOf, sub_one_dvd_pow_sub_one])⟩

/-- The norm of a generator is a generator: for a primitive label c of degree r, the product of
its roots has order |k| − 1, and for one exponent e it equals ξ^e for every root ξ. -/
lemma IsPrimitiveLabel.isPrimitiveRoot_prod_roots (hc : IsPrimitiveLabel r c) :
    IsPrimitiveRoot (c.aroots (AlgebraicClosure k)).prod (.card k - 1) ∧ ∃ e, ∀ ξ ∈ c.aroots
  (AlgebraicClosure k), ξ ^ e = (c.aroots _).prod := have ⟨⟨_, _, rfl, z⟩, I, _, w, h⟩ := hc
  have e {ξ} (o : c.aeval ξ = 0) : ξ ^ _ = (c.aroots _).prod := by
    simp [aroots_eq_frobenius_orbit I o, prod_pow_eq_pow_sum, ← range_val]
  ⟨e w ▸ h.pow (by grind [root_pow_card_pow_pred_eq_one I z w])
    (geom_sum_mul_of_one_le Fin.pos' _).symm, by aesop⟩

/-- The set of tuples (c_w) of polynomials over the finite fields k_w, each an allowed label of
degree r (no root x with x^M = 1), with at least one c_w irreducible with a primitive root. -/
noncomputable def goodTuples {ι} [Fintype ι] {k : ι → _} [∀ w, Field (k w)] [∀ w, Finite (k w)]
    M r := {c ∈ Fintype.piFinset fun w ↦ monicsOfDegree (k w) r |
  (∀ w, IsLabel r (c w) ∧ ∀ x, x ^ M = 1 → ¬(c w).IsRoot x) ∧ ∃ w, IsPrimitiveLabel r (c w)}

/-- Let |k| ≡ 1 mod 9, r = |n| = 3^{a+1}, and S, T have at most one element each. Some P has
e_P(g) = e_c(g) for all g with reducible characteristic polynomial and, if c is a primitive label of
degree r, is one outside S ∪ T.

Good types and cubic twists of cuspidal characters. -/
lemma exists_labelIdem_eq_off_irreducible {k n a} [Field k] [Finite k] [Fintype n] (hr :
  Fintype.card n = 3 ^ (a + 1)) (hq : 9 ∣ .card k - 1) c {S T : Set k[X]} (hS : S.Subsingleton)
  (hT : T.Subsingleton) : ∃ P, (IsPrimitiveLabel (Fintype.card n) c →
  IsPrimitiveLabel (Fintype.card n) P ∧ P ∉ S ∪ T) ∧ ∀ g, ¬Irreducible g.1.charpoly →
  (labelIdem n c).coeff g = (labelIdem n P).coeff g := by_cases (fun ⟨hc, hi, ξ, hξ,
  h⟩ ↦ have ⟨χ, m, hx⟩ := (reindex_equiv (charName (faithfulChar k))).2.1.1 (by_contra fun _ ↦
    (@Nat.card_le_card_of_injective (rootsOfUnity 3 k) _ _ (c.scaleRoots ·.1 ∈ S) fun x y _ ↦ by
    choose l hl e using exists_pow_card_pow_eq_of_root (hi.map (scaleRootsEquiv _))
      (scaleRoots_aeval_eq_zero hξ) ((by grind
      [Set.Subsingleton] : c.scaleRoots x.1 = c.scaleRoots y.1) ▸ scaleRoots_aeval_eq_zero hξ)
    cases frobenius_conj_pow_injOn 1 hq (hr ▸ h) prime_three (by simpa [scaleRootsEquiv, hc.2,
      hr] using hl) Fin.pos'
      (by simpa [mul_pow, ← map_pow, (mem_rootsOfUnity' ..).1] using (e ▸ pow_right_comm _ 3 _ :))
    aesop (add simp [IsLabel, aeval_def])).not_gt (by
    erw [IsCyclic.card_powMonoidHom_ker, Nat.card_units, gcd_eq_right (by lia)]; simp) :
    ∃ x ∈ rootsOfUnity 3 k, c.scaleRoots x ∉ _)
  ⟨_, (⟨·.scaleRoots _ congr($m) hq, hx⟩), fun g _ ↦ .symm (by_contra fun z ↦ by
  simp_all [MulEquiv.map_eq_one_iff, ← map_pow, ← labelChar_mul_det hc, mul_right_eq_self₀,
    labelIdem, IsLabel.scaleRoots, hc.1]
  choose P j i p using isCuspidal_greenTau.exists_charpoly_eq_pow z.1.2
  obtain ⟨⟨_ | _⟩⟩ := (dvd_prime_pow prime_three).1 ⟨_, by simpa [hr] using congr(natDegree $p)⟩,
    g.det_ne_zero <;> simp_all [Matrix.det_eq_sign_charpoly_coeff, pow_add, pow_mul',
    coeff_zero_eq_eval_zero, ← χ.pow_apply', MulChar.one_apply])⟩) (⟨c, ·.elim, by simp⟩)

/-- Bad share: take f fields of order q, 1 < r = |n| < q, M ≥ 1, (1+M+2r)/q ≤ ε ≤ 1, 2r(2r log
q + 1)L ≤ f. For e the sum of `tupleIdem` over `goodTuples` M r, Re (1 − e)(1) ≤ fε + exp(−L).

Bad types have small share in the regular representation. -/
lemma bad_share_le {n ι} [Fintype n] [Fintype ι] {k : ι → _}
    [∀ w, Field (k w)] [∀ w, Finite (k w)] {q M r f : ℕ} [NeZero M] (ε L : ℝ) (hq : ∀ w, .card (k w)
    = q) (hr : card n = r) (hf : card ι = f) (hn : 1 < r) (h2 : r < q) (hε : ε ≤ 1)
    (hs : (1 + M + 2 * r) / q ≤ ε) (hL : 2 * r * (2 * (r * .log q) + 1) * L ≤ f) :
    ((1 - ∑ c ∈ goodTuples M r, tupleIdem (k := k) n c).coeff 1).re ≤ f * ε + exp (-L) := by
  rw [← le_div_iff₀' (by positivity)] at hL; let m : ℝ := (1 - r / q) / q ^ r
  have h1 := hn.trans h2
  obtain ⟨_ : 0 ≤ m, _⟩ := by simp [field, h2.le], one_lt_pow hn.ne_bot h1
  have B w : #{c ∈ monicsOfDegree (k w) r | ¬IsPrimitiveLabel r c} • m ≤ 1 - L / f := by
    grw [hL, div_right_comm, div_self_le_one, (by simp [field] : m ≤ 1 / ↑(q ^ r)), nsmul_eq_mul,
      filter_not, cast_card_sdiff (by simp), sub_mul]
    gcongr; simp_all [monicsOfDegree, ofEquiv_card, field]; field
    grw [(by lia : q ^ r ≤ (q ^ r - 1) * 2), cast_mul, le_totient_mul_log, ←
      (@hasEnoughRootsOfUnity (k w) _ _ ⟨by simp [Ne.pos, hn.ne_zero, ← hq
      w]⟩).1.choose_spec.card_primitiveRoots, sub_le] <;> simp [field, ← cast_mul, *]
    apply card_le_mul_card_image_of_maps_to (f := minpoly _) <;>
      simp_intro ξ g [monicsOfDegree, IsPrimitiveLabel, IsLabel, *]
    obtain ⟨⟨⟩, ⟨_, d⟩, i⟩ := hq w, (pow_pred_eq_one_iff ‹_›).1 g.1, (isAlgebraic _).isIntegral.1 ξ
    have := (g.2 _ (root_pow_card_pow_pred_eq_one (irreducible i) (by aesop) (by simp)).1).antisymm
      (pow_sub_one_dvd_pow_sub_one _
      ((root_pow_card_pow_eq_self_iff (irreducible i) (by simp)).1 d))
    simp_all [monic, irreducible]; use Nat.pow_right_injective h1 (by lia), ξ, by simp
    grw [card_le_degree_of_subset_roots (p := ξ.map (algebraMap ..)) fun _ ↦ _] <;> aesop
  refine' (_ : _ → _) (prod_le_prod₀ (by grind) fun w _ ↦ show 1 -
    ε ≤ #(monicsOfDegree _ r \ ((insert 0 (nthRoots M (1 : k w)).toFinset).image₂ ((X - C ·) · * ·)
    (monicsOfDegree _ (r - 1)) ∪ (range r).biUnion fun d ↦
    (monicsOfDegree _ ((r - d) / 2)).image₂ (· ^ 2 * ·) (monicsOfDegree _ d))) • m by
    grw [← hs, nsmul_eq_mul, ← sdiff_inter_self_left, cast_card_sdiff, inter_subset_right,
      card_union_le, card_image₂_le, card_insert_le, Multiset.toFinset_card_le, card_nthRoots,
      card_biUnion_le, card_image₂_le,
      sum_le_card_nsmul _ _ (q ^ (r - 1))] <;> simp [monicsOfDegree,
      ofEquiv_card, ← hq w, pow_sub₀, hn.le, field, ← pow_add, pow_le_pow_iff_right₀ one_lt_card]
    nlinarith; lia)
  grw [prod_smul, ← card_piFinset, card_le_card_sdiff_add_card, add_smul, card_piFinset,
    ← prod_smul, B, card_le_card, card_nsmul_le_sum (goodTuples M r) (tupleIdem n · |>.coeff 1
    |>.re) _ fun c g ↦ mod_cast (prod_le_prod₀ (by simp_all) fun w _ ↦ show (m : ℂ) ≤ _ by
    obtain ⟨⟨⟩, l, _⟩ := hr, (mem_filter.1 g).2.1 w
    simpa [labelIdem, m, ← hq w, l] using (labelChar_degree_bounds _ l).2).1] <;>
    simp_all [goodTuples, sq, monicsOfDegree, NeZero.pos, subset_iff, ↓← dvd_iff_isRoot]
  grind [one_add_mul_sub_le_pow, @one_sub_div_pow_le_exp_neg f _ (hL.trans (by bound))]
  refine' fun c g _ _ w ↦ ⟨⟨_, fun Q q ↦ by_contra
    (let ⟨_, _, _, h⟩ := Q.exists_monic_irreducible_factor ·
    ((mul_dvd_mul h h).trans q).rec _), _⟩, _⟩ <;> grind [Irreducible.natDegree_pos,
    Monic.natDegree_mul, monic_X_sub_C, natDegree_X_sub_C, =_ X_dvd_iff, monic_X, natDegree_X,
    dvd_def, Monic.mul, → Monic.of_mul_monic_left]
