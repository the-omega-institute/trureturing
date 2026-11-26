import GRH.Lib.General.NumberTheory.ZeroSymmetry
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Voronoi's congruence for twisted power sums and trivial zeros of Dirichlet
L-functions. The form here is twisted by a possibly imprimitive character and stated for power sums.
One non-zero integer with an explicit size bound is divisible by the Stickelberger elements for all
primes, characters ψ with ψ(−1) = −(−1)^e, and coefficient rings. Source: K. Ireland, M. Rosen, A
Classical Introduction to Modern Number Theory, 2nd ed. 1990; for the untwisted statement also M.
Eberl, Kummer's congruence, Archive of Formal Proofs 2024.

This file: Twisted Voronoi congruence, trivial zeros, one bounded integer divisible by all
Stickelberger elements. -/

open Finset DirichletCharacter Matrix Nat Polynomial Complex NeZero ZMod Real

lemma Nat.ModEq.coprime_of_modEq_one {a b} (h : a ≡ 1 [MOD b]) : a.Coprime b := by simpa using
  h.gcd_eq


variable (N e : ℕ) [NeZero N]

lemma smul_bernoulli_mem_lifts n : ((n + 1)! * N ^ n) • Polynomial.bernoulli n ∈
  (liftsRing (algebraMap ℤ ℚ)).comap (C N.cast⁻¹ * X).compRingHom := by
  rw [factorial, mul_assoc, mul_nsmul, bernoulli_eq_sub_sum, smul_sub, sum_range, smul_sum]
  refine sub_mem ⟨monomial _ (n + 1)!, funext (by simp [factorial, field, mul_pow])⟩ (sum_mem ?_)
  intros; rw [smul_comm, ← @Nat.div_mul_cancel _ (_ * _), mul_smul]
  solve_by_elim [nsmul_mem, smul_bernoulli_mem_lifts]; gcongr <;> lia

/-- Each prime l has some c ≡ 1 mod N, l ∤ c, with (c^e − 1)(c^{e+1} − 1) ∣ X; and for every c ≡
1 mod N and character ψ mod N into a characteristic zero domain O with (−1)^eψ(−1) = −1, one
w in O has (c^{e+1} − 1)X ≡ 2w∑_{0≤a<Nm} ⌊ca/(Nm)⌋a^eψ(a) mod m for all m ≥ 1 prime to c. -/
def IsStickelbergerBound X := (∀ l, Nat.Prime l → ∃ c, c ≡ 1 [MOD N] ∧ l.Coprime c ∧ (c ^ e - 1) *
  (c ^ (e + 1) - 1) ∣ X) ∧ ∀ c, c ≡ 1 [MOD N] → ∀ O [CommRing.{0} O] [IsDomain O] [CharZero O] (ψ :
  DirichletCharacter O N), ψ (-1) = -(-1) ^ e → ∃ w, ∀ m [NeZero m], m.Coprime c → ↑m ∣
  (c ^ (e + 1) - 1) * X - 2 * w * ∑ a ∈ range (N * m), ↑(c * a / (N * m)) * (a ^ e * ψ a)

attribute [local grind =] neg_one_pow_eq_ite Even.eval_neg Odd.eval_neg

/-- Trivial zeros: for a complex Dirichlet character χ mod N, not necessarily primitive, and e ≥
1, L(χ, −e) = 0 exactly when χ(−1) = (−1)^e.

Known result: Voronoi's congruence for twisted power sums; trivial zeros of Dirichlet
L-functions. -/
lemma LFunction_neg_nat_eq_zero_iff (χ : DirichletCharacter ℂ N) (he : e ≠ 0) :
    χ.LFunction (-e) = 0 ↔ χ (-1) = (-1) ^ e := by
  have := LFunction_one_sub_eq_zero χ (-e)
  simp_all [LFunction_ne_zero_of_one_le_re, LFunction_eq_completed_div_gammaFactor,
    gammaFactor, ite_eq_iff, Gammaℝ_eq_zero_iff]
  norm_cast at *
  grind [e.even_or_odd', χ.even_or_odd]

omit [NeZero N] in
/-- Voronoi's congruence, twisted by a Dirichlet character χ mod N: for f = Nm and c ≡ 1 mod N
prime to m, (c^{e+1} − 1)∑ χ(t)t^{e+1} ≡ (e+1)c^e f ∑ ⌊ct/f⌋t^e χ(t) mod f², both sums over
0 ≤ t < f.

Known result: Voronoi's congruence for twisted power sums; trivial zeros of Dirichlet
L-functions. -/
lemma voronoi_congruence {O} [CommRing O] (χ : DirichletCharacter O N) {f m c} [NeZero f] (h : f = N
  * m) (hc : m.Coprime c) (h₁ : c ≡ 1 [MOD N]) : (f : O) ^ 2 ∣ (c ^ (e + 1) - 1) * ∑ t, χ (@val f t)
  * t.val ^ (e + 1) - (e + 1) * c ^ e * f * ∑ t, ↑(c * @val f t / f) * (χ t.val * t.val ^ e) := by
  rw [sub_one_mul, mul_sum, sub_sub, dvd_sub_comm, ← Equiv.sum_comp (unitOfCoprime c (h ▸
    h₁.coprime_of_modEq_one.mul_right hc.symm)).mulLeft, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  exact dvd_sum fun t _ ↦ .trans ⟨_, mul_pow _ (-↑(c * t.val / f)) 2⟩
    ((sq_dvd_add_pow_sub_sub _ ↑(c * t.val) (e + 1)).trans ⟨_, by
    simp [val_mul, (c * _).mod_def, mul_div_le, h, (natCast_eq_natCast_iff ..).2 h₁]; ring⟩)

/-- For N, e ≥ 1 there is an integer 1 ≤ X ≤ 2^{(N+e+3)^6} with the property `IsStickelbergerBound`
N e X. -/
lemma exists_isStickelbergerBound (he : e ≠ 0) : ∃ X ≠ 0, X ≤ 2 ^ (N + e + 3) ^ 6 ∧
  IsStickelbergerBound N e X := by
  obtain ⟨⟨p, hp⟩, _⟩ := smul_bernoulli_mem_lifts N (e + 2), ne N
  let D := (e + 3)! * (e + 2) * N; let b := p.derivative.eval
  let M := D * N ^ e * (e + 1)!
  have (K) [RCLike.{0} K] t : b t = D * N ^ e * aeval (t / N : K) (bernoulli (e + 1)) := by
    have := congr((derivative $hp).aeval (t : K))
    simp [aeval_def, eval₂_comp, derivative_comp, derivative_bernoulli, derivative_pow] at *; grind
  replace hp t : p.eval (N.cast + t) = p.eval t + t ^ (e + 1) * D := by
    qify; replace hp (t : ℤ) := congr(eval ↑t $hp)
    simp_all [D, mul_add, bernoulli_eval_one_add, mul_pow]; field
  let g t := 2 * b (@val N t) + ite (t = 1) ((-1) ^ e) 0 + ite (t = -1) 1 0
  let T := of fun s t : _ˣ ↦ g (t / s).1
  have key O [CommRing O] (ψ : MulChar _ O) : T.map (↑) *ᵥ (ψ ·.1) = (∑ t, ψ t * g t) • (ψ ·.1) :=
    by
    ext s; apply (Equiv.sum_comp (.mulLeft s) _).symm.trans; simp [sum_mul]
    apply sum_of_injOn (↑) <;> simp_all [T, ψ.map_nonunit, IsUnit, Units.val_injective]; grind
  have := (Int.cast_det T).trans_ne (separatingLeft_iff_det_ne_zero.1 (separatingLeft_def.2 fun w h
    ↦ have k χ := (by simpa using (key ℂ χ ▸ h _ :) :).resolve_left (by
    have := (LFunction_neg_nat_eq_zero_iff N e χ he).symm.trans mul_eq_zero
    simp_all [g, mul_add, -natCast_val, toAddCircle_apply, ← mul_sum, val_le,
      mul_left_comm, HurwitzZeta.hurwitzZeta_neg_nat, cast_add_one_ne_zero, ↓unitInterval.div_mem]
    grind [even_or_odd χ, @ne ℂ _ M ⟨by norm_cast; positivity⟩])
    by ext a; simpa [dotProduct, sum_mul, sum_comm, ← mul_sum, mul_assoc, ← map_mul, ne,
      sum_characters_eq, -map_units_inv, Units.val_inj] using congr(∑ χ, $(k χ) * χ a⁻¹)))
  refine ⟨_, by simp_all [tsub_eq_zero_iff_le, add_assoc], ?_, fun l h ↦ (coprime_or_dvd_of_prime
    h _).elim (⟨_, add_modEq_right, ·, _, rfl⟩) (⟨1 + N + N, by simp, .of_dvd_left · (by simp),
    .mul_left ⟨T.det.natAbs, rfl⟩ _⟩), fun c h₃ O _ _ _ χ _ ↦ Dvd.elim (.trans ⟨_, by simpa
    [adjugate_mul, ← Int.cast_det] using (congr(toLin' (T.map (↑)).adjugate $(key O
    χ) 1))⟩ (by simp [← mul_assoc, ← sign_mul_self])) fun u U ↦ ⟨u * D * c ^ e * (e + 1), fun m _ hv
    ↦ (voronoi_congruence N e χ rfl hv h₃).elim fun v _ ↦
    ⟨2 * N * u * (D * v - (c ^ (e + 1) - 1) * ∑ t, χ t *
    p.binomExpansion t.val (N * m)), congr(_ * $U - _).trans (mul_left_cancel₀ (ne ↑(N * m)) ?_)⟩⟩⟩
  have (t) (_ : t ≤ N) : |b t| < M * 17 := by
    have := (@hasSum_one_div_nat_pow_mul_fourier (e + 1) (by lia) (t / N) ·
      |>.norm_le_of_bounded (hasSum_zeta_two.mul_right 6) fun n ↦ by
      grw [norm_mul, norm_add_le]; cases n <;> simp [-Nat.cast_add]; bound [he.pos])
    rify; simp [M, *, field, bernoulliFun] at *
    grw [← one_le_pow₀, pi_lt_four] at this <;> grind [two_le_pi]
  grw [show Int.natAbs _ ≤ _ * (M * 64) ^ _ by
    zify; simpa using T.det_le (abv := .abs) (by simp [T]; grind)]
  trans; apply_rules [tsub_le_self.trans, (factorial_le_pow _).trans,
    pow_le_pow_left', mul_le_mul', Nat.lt_two_pow_self.le]
  simp only [← pow_mul, ← pow_add]; gcongr; grw [totient_le]; lia
  have : ∀ f [NeZero f] F, (range f).sum F = ∑ a, (F (@val f a) : O) | _ + 1, _ => sum_range
  replace U := congr(∑ t ∈ range $(add_comm N (N * m)), χ t * p.eval ↑t)
  simp_all [add_comm (N * _), (p.binomExpansion _ (_ * _)).2, mul_add, g,
    ← mul_assoc, ← sum_mul, ↓sum_range_add, two_mul]; grind
