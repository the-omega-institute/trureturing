import GRH.Lib.General.NumberTheory.QuadField
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Primes and residue degrees, Frobenius on quadratic integers, lifting the exponent at 2.
Decomposition of rational primes in Q(√-d) by the Legendre symbol. -/

open Ideal FiniteField Int NumberField ZMod legendreSym Ideal.Quotient
  IsDedekindDomain.HeightOneSpectrum

variable {F} [Field F] [NumberField F] {d p : ℕ} [hp : Fact p.Prime] {R} [CommRing R] [CharP R p]
  [PrimeSevenModEight d] (h2 : p ≠ 2) (φ : 𝓞 (QuadField d) →+* R) (w : FinPlace F)

variable (F p) in
lemma FinPlace.exists_natCast_mem : ∃ w : FinPlace F, ↑p ∈ w.1 :=
  (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 F).elim
  fun ⟨P, i, ⟨e⟩⟩ ↦ ⟨⟨P, i, (by simp [·, NeZero.ne] at e)⟩, by simpa using e.le⟩

attribute [local instance] Quotient.field

lemma FinPlace.charP_quotient (h : ↑p ∈ w.1) : CharP (_ ⧸ w.1) p :=
  .of_eq_zero hp.1 (eq_zero_iff_mem.2 h)

protected lemma FinPlace.natCast_mem_iff_dvd (h : ↑p ∈ w.1) {n} :
    ↑n ∈ w.1 ↔ p ∣ n := by erw [← (w.charP_quotient h).1, eq_zero_iff_mem]

attribute [local instance] ZMod.algebra

/-- For a finite place w of a number field F above the prime p there is f with Nw = p^f, such
that x^{pⁿ} ≡ x mod w holds for all integers x of F if and only if f divides n. -/
lemma FinPlace.exists_q_eq_pow (h : ↑p ∈ w.1) : ∃ f, w.q = p ^ f ∧ ∀ n, f ∣ n ↔ ∀ x,
  Ideal.Quotient.mk w.1 x ^ p ^ n = Ideal.Quotient.mk _ x := have := w.charP_quotient h
  ⟨_, .symm (pow_finrank_eq_natCard p (_ ⧸ w.1)), by simp [AlgHom.ext_iff, mk_surjective.forall,
    ← orderOf_frobeniusAlgHom, coe_frobeniusAlgHom, orderOf_dvd_iff_pow_eq_one]⟩

lemma QuadField.map_sqrtNegDInt_sq :
  φ (sqrtNegDInt d) ^ 2 = -d := by simp [↓← map_pow, sqrtNegDInt_sq]

omit [Fact p.Prime] in
/-- For a prime d ≡ 7 mod 8, χ_K(p) = 1 when p = 2: the Legendre symbol (2/d) is 1, that is, 2
splits in K = ℚ(√−d). -/
lemma QuadField.chiK_two : p = 2 →
  chiK d p = 1 := by grind [chiK_eq_legendreSym, PrimeSevenModEight, at_two, χ₈_nat_eq_if_mod_eight]

lemma QuadField.legendreSym_eq_pow_of_sq_eq_neg (h2 : p ≠ 2) {x : R} (e : x ^ 2 = -d) : chiK d p =
  x ^ (p - 1) := by simpa [*, chiK_eq_legendreSym, neg_one_pow_eq_ite,
  quadratic_reciprocity' h2, neg_pow (d : R), pow_mul, ← p.two_mul_odd_div_two,
  hp.1.mod_two_eq_one_iff_ne_two, (by grind [PrimeSevenModEight] : d ≠ 2 ∧ Odd (d / 2))
  ] using congr((-1) ^ (p / 2) * (cast $(eq_pow p d) : R))

include h2 in
/-- Let d be a prime ≡ 7 mod 8, p an odd prime, φ : 𝓞_K → R a ring map to characteristic p, ε =
(1 + √−d)/2. Then x = φ(ε)^{p^n} if and only if 2x − 1 = (p/d)^n (2φ(ε) − 1). -/
lemma QuadField.eq_map_c₀_pow_iff n x : x = φ (c₀ d) ^ p ^ n ↔ 2 * x - 1 =
  chiK d p ^ n * φ (sqrtNegDInt d) := by
  rw [show _ * φ _ = φ (sqrtNegDInt d) ^ p ^ n by induction n <;> simp_all [pow_succ', pow_mul,
    mul_assoc, ← iterateFrobenius_def, ← pow_sub_one_mul hp.1.ne_zero,
    ← legendreSym_eq_pow_of_sq_eq_neg h2 (map_sqrtNegDInt_sq φ), -map_sub]]
  simp [← iterateFrobenius_def, IsUnit.mul_right_inj, map_ofNat, *, CharP.isUnit_ofNat_iff,
    p.prime_dvd_prime_iff_eq, Fact.out]

/-- The number q: p² if (p/d) = −1, and p otherwise. -/
abbrev primeNorm (d p : ℕ) [Fact d.Prime] := ite (chiK d p = -1) (p ^ 2) p

/-- The number ρ_p: 1/(p² − 1) if (p/d) = −1, 1/(2(p − 1)) if p = d, and 1/(p − 1) otherwise. -/
noncomputable def nonsplitWeight (d p : ℕ) [Fact d.Prime] : ℝ :=
  (1 + chiK d p ^ 2) / 2 / (primeNorm d p - 1)

lemma chiK_cases (d p : ℕ) [hp : Fact p.Prime] [Fact d.Prime] :
    p = d ∧ chiK d p = 0 ∨ p ≠ d ∧ (chiK d p = 1 ∨ chiK d p = -1) := by
  simp [chiK, quadraticCharFun]; grind [prime_ne_zero, natCast_self d]

variable {q : ℤ} {o s d p : ℕ} [Fact (d % 4 = 3)] [hp : Fact p.Prime] (w : FinPlace (QuadField d))

/-- If q is an integer, o is a nonzero natural number and q^o ≡ 1 mod 2^(s+1), then 2^s divides
(q − 1)o or (q + 1)o. -/
lemma two_pow_dvd_or_of_pow_eq_one (ho : 0 < o) (h : (q : ZMod (2 ^ (s + 1))) ^ o = 1) :
    2 ^ s ∣ (q - 1) * o ∨ 2 ^ s ∣ (q + 1) * o := by
  have := (intCast_eq_intCast_iff_dvd_sub 1 (q ^ (o * 2)) (2 ^ s.succ)).1 (by simp [h, pow_mul])
  cases (by grind [even_pow, → Even.trans_dvd] : 4 ∣ q - 1 ∨ 4 ∣ q - -1) <;>
    have := two_pow_sub_pow' (o * 2) ‹_› (by lia) <;> simp_all [pow_dvd_iff_le_emultiplicity,
    emultiplicity_mul prime_two, ← add_assoc, finiteMultiplicity_iff]

/-- If q is an integer with |q| > 1, o is a nonzero natural number and q^o ≡ 1 mod 2^(s+1), then
2^s ≤ (|q| + 1)·o. -/
lemma two_pow_le_of_pow_eq_one (h1 : 1 < q.natAbs) {o s} (ho : 0 < o) (h : (q : ZMod (2 ^ (s + 1)))
  ^ o = 1) : 2 ^ s ≤ (q.natAbs + 1) * o := by cases two_pow_dvd_or_of_pow_eq_one ho h <;> zify <;>
  apply (le_abs_of_dvd _ ‹_›).trans <;> simp [*] <;> grind

/-- Let d be a prime ≡ 7 mod 8 and w a prime of K = ℚ(√−d) above the rational prime p. Then w
has absolute norm p if and only if the Legendre symbol (p/d) is not −1. -/
lemma QuadField.q_eq_iff_legendreSym_ne_neg_one (hw : ↑p ∈ w.1) [PrimeSevenModEight d] : w.q = p ↔
  chiK d p ≠ -1 := by
  obtain ⟨c, ⟨⟩⟩ := w.charP_quotient hw, w.exists_q_eq_pow hw, chiK_cases d p
  simp [*, hp.1.pow_eq_iff, ← Nat.dvd_one]
  apply Iff.trans ⟨(· (c₀ d)), fun _ ↦
    (by induction (different_eq_span_and_adjoin_c₀ d).2.ge (x := ·) ⟨⟩ using
    Algebra.adjoin_induction <;> simp_all [← frobenius_def])⟩
  obtain rfl | h := eq_or_ne p 2
  grind [chiK_two rfl, PrimeSevenModEight, c.1, congr(Ideal.Quotient.mk w $(c₀_mul_one_sub d)),
    map_natCast]
  erw [← pow_one p, eq_comm, eq_map_c₀_pow_iff h, eq_comm, mul_left_eq_self₀, ← sq_eq_zero_iff,
    map_sqrtNegDInt_sq]
  aesop (add simp [_root_.neg_one_eq_one_iff, ringChar.eq, (c.1), Nat.dvd_prime, Fact.out])

/-- Let d ≡ 3 mod 4 and let w lie above the prime p in K = ℚ(√−d). For some J the primes above p
are w and J, and either J = w, Nw = p², or Nw = NJ = p, (p) = wJ. -/
lemma QuadField.prime_inert_or_eq_mul (hw : ↑p ∈ w.1) : ∃ J, (∀ u, ↑p ∈ u.1 ↔ u = w ∨ u = J) ∧
    (w = J ∧ w.q = p ^ 2 ∨ w.q = p ∧ J.q = p ∧ span {↑p} = w.1 * J.1) :=
    (dvd_span_singleton.2 hw).elim fun J _ ↦ by by_cases J = ⊤
  <;> (have := by simpa [*, ← Nat.cast_mul, sq p ▸ hp.1.mul_eq_prime_sq_iff, w.2.1]
    using absNorm_span_eq_mul_star d p) <;> [use w; use (ofPrime (irreducible_of_irreducible_absNorm
  (this.2 ▸ hp.1)).prime)] <;> generalize_proofs <;> simp_all [← dvd_span_singleton, prime, ofPrime,
  sq, Prime.dvd_mul, prime_dvd_prime_iff_eq, IsDedekindDomain.HeightOneSpectrum.ext_iff]
