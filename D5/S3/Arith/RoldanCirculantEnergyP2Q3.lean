/- GID: D5/S3/Arith/RoldanCirculantEnergyP2Q3
   generality: I
   mirror-B: D5/B/S3/Arith/RoldanCirculantEnergyP2Q3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The unique maximum energy at order p squared q cubed. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19204.

admission_basis: open-problem-resolution (#19144; Proved).
proof_shape: result: content; escape_witness: none.
Direct frozen dependencies (declaration identities on the dev base):
  D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.finEquiv_eq_natCast
  statement_id sha256:6062729cd00b090edb5dfcccd635f4a563a8a66f60deb5d1c6d91f2195edc1b1.
  D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.circulant_spectral
  statement_id sha256:c0c4758ccc24a85ddcb6430f1368fa477dcc97806137246966f740473972a4c0.
  D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.transform_unitary
  statement_id sha256:efa8366c2ffbe97c466a47cde0fa1bf8aea043e2121045f7338c075daf53d748.
  D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.transform
  statement_id sha256:bc5ccc0b9c6c5a7a63a3c96211c723596ca12ab786b9c0cf4cbd4907f812603f.
  D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.spectralValue
  statement_id sha256:5c76af6f912bc476b8b2627b4c4e4af6068c4792ec7ead5d9e1752cbc0ce33fc.
  D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.sum_ramanujanSum_divisors
  statement_id sha256:e84aedcf519a93b3d92c3f00b87b1f2f24ad6024a3148bd06815f5e546b64020.
  D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.ramanujanSum
  statement_id sha256:908a77e52c19378791b1586759e38bf57a8f5795e3c16983c9184dba91a1b789.
The source adjacency, energy, divisor set and claim use the expressions of #19144.
The spectral proof uses the original Fourier and Ramanujan owners.

Declaration classification:
  CirculantCharpoly.circulant_charpoly: reused from D5/S3/Quantum/Matrix/CirculantCharpoly; consumer: real_circulant_roots.
  CirculantCharpoly.dft_real_of_even: reused from D5/S3/Quantum/Matrix/CirculantCharpoly; consumer: real_circulant_charpoly.
  CirculantCharpoly.real_circulant_charpoly: reused from D5/S3/Quantum/Matrix/CirculantCharpoly; consumer: real_circulant_roots.
  real_circulant_roots: bind-only; consumers: energy_eq_dft.
  ramanujan_prime_power: bind-only; consumers: ramanujan_prime_power_values.
  ramanujan_prime_power_values: bind-only; consumers: ramanujan_prime_power_mixed.
  ramFn_mul_zeta: bind-only; consumers: ramFn_eq_moebius_convolution.
  ramFn_eq_moebius_convolution: bind-only; consumers: ramanujan_multiplicative.
  divFn_multiplicative: bind-only; consumers: ramanujan_multiplicative.
  ramanujan_multiplicative: bind-only; consumers: ramanujan_grid_table.
  ramanujan_moebius: bind-only; consumers: ramanujan_gcd_of_dvd.
  ramanujan_gcd_of_dvd: bind-only; consumers: energy_divisor_formula.
  ramanujan_one: bind-only; consumers: p2_ramanujan_table, q3_ramanujan_table.
  prime_power_dvd_mixed_power: bind-only; consumers: ramanujan_prime_power_mixed, divisorValue_injective.
  ramanujan_prime_power_mixed: bind-only; consumers: p2_ramanujan_table, q3_ramanujan_table.
  sum_gcd_class: bind-only; consumers: gcd_class_phase_sum.
  gcd_class_phase_sum: bind-only; consumers: gcdRow_dft_ramanujan.
  gcd_val_neg: bind-only; consumers: gcdRow_even.
  gcdRow_even: bind-only; consumers: gcdRow_dft_range, energy_eq_dft.
  fin_equiv_val: bind-only; consumers: gcdRow_dft_range, adjacency_reindex, energy_divisor_formula.
  stdAddChar_mul_nat: bind-only; consumers: gcdRow_dft_range.
  gcdRow_dft_range: bind-only; consumers: gcdRow_dft_ramanujan.
  gcdRow_dft_ramanujan: bind-only; consumers: energy_eq_ramanujan.
  sum_gcd_multiplicity: bind-only; consumers: energy_divisor_formula.
  adjacency_reindex: bind-only; consumers: energy_eq_dft.
  energy_eq_dft: bind-only; consumers: energy_eq_ramanujan.
  energy_eq_ramanujan: bind-only; consumers: energy_divisor_formula.
  energy_divisor_formula: bind-only; consumers: energy_decode_model.
  divisor_exponents: bind-only; consumers: sum_divisor_grid, decode_encode.
  encode_testBit: bind-only; consumers: encode_switch.
  proper_of_factor: bind-only; consumers: dstar_admissible.
  dstar_admissible: bind-only; consumers: result.
  divisorValue_injective: bind-only; consumers: sum_divisor_grid, sum_decode.
  sum_divisor_grid: bind-only; consumers: energy_decode_model.
  encode_switch: bind-only; consumers: decode_encode.
  decode_encode: bind-only; consumers: encode_ne_star, result.
  decode_star: bind-only; consumers: encode_ne_star, result.
  encode_ne_star: bind-only; consumers: result.
  decode_subset_divisors: bind-only; consumers: energy_decode_model.
  sum_decode: bind-only; consumers: energy_decode_model.
  p2_ramanujan_table: bind-only; consumers: ramanujan_grid_table.
  q3_ramanujan_table: bind-only; consumers: ramanujan_grid_table.
  p2_totient_table: bind-only; consumers: totient_grid_table.
  q3_totient_table: bind-only; consumers: totient_grid_table.
  quotient_p2q3: bind-only; consumers: ramanujan_grid_table, totient_grid_table.
  evalW_ofReal: bind-only; consumers: totient_grid_table.
  lcoeff_evaluation: bind-only; consumers: energy_decode_model.
  ramanujan_grid_table: bind-only; consumers: energy_decode_model.
  totient_grid_table: bind-only; consumers: energy_decode_model.
  energy_decode_model: bind-only; consumers: result.
  result: content; consumers: none (settling result).
-/

import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import D5.S3.Quantum.Matrix.CirculantCharpoly
import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration

open D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open scoped BigOperators
open Matrix Polynomial Complex
noncomputable section
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
variable (n : ℕ) [NeZero n]
private theorem real_circulant_roots (b : ZMod n → ℝ) (hb : ∀ k, b (-k) = b k) :
    (Matrix.circulant b).charpoly.roots =
      Finset.univ.val.map (fun j => (ZMod.dft (fun k => (b k : ℂ)) j).re) := by
  rw [D5.S3.Quantum.Matrix.CirculantCharpoly.real_circulant_charpoly n b hb]
  have he := Polynomial.roots_multiset_prod_X_sub_C
    (Finset.univ.val.map (fun j => (ZMod.dft (fun k => (b k : ℂ)) j).re))
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using he
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
private theorem ramanujan_prime_power (p j k : ℕ) (hp : p.Prime) :
    ramanujanSum (p ^ (k + 1)) j =
      (if p ^ (k + 1) ∣ j then (p ^ (k + 1) : ℂ) else 0) -
      (if p ^ k ∣ j then (p ^ k : ℂ) else 0) := by
  have h1 := sum_ramanujanSum_divisors (p ^ (k + 1)) j (pow_pos hp.pos _)
  have h0 := sum_ramanujanSum_divisors (p ^ k) j (pow_pos hp.pos _)
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at h1
  rw [Nat.sum_divisors_prime_pow hp] at h0
  push_cast at h1 h0
  rw [h0] at h1
  exact eq_sub_of_add_eq' h1
private theorem ramanujan_prime_power_values (p j k : ℕ) (hp : p.Prime) :
    ramanujanSum (p ^ (k + 1)) j =
      if p ^ (k + 1) ∣ j then (Nat.totient (p ^ (k + 1)) : ℂ)
      else if p ^ k ∣ j then -(p ^ k : ℂ) else 0 := by
  rw [ramanujan_prime_power p j k hp]
  by_cases h1 : p ^ (k + 1) ∣ j
  · have h0 : p ^ k ∣ j := by
      exact dvd_of_mul_right_dvd (by simpa only [pow_succ] using h1)
    simp only [h1, h0, ite_true, Nat.totient_prime_pow_succ hp]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    rw [pow_succ]
    ring
  · simp only [h1, ite_false]
    split_ifs <;> simp
open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius
private noncomputable def ramFn (j : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => ramanujanSum d j, by simp [ramanujanSum]⟩
private def divFn (j : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d ∣ j then (d : ℂ) else 0, by simp⟩
private theorem ramFn_mul_zeta (j : ℕ) : ramFn j * (ζ : ArithmeticFunction ℂ) = divFn j := by
  ext d
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  change (∑ r ∈ d.divisors, ramanujanSum r j) = if d ∣ j then (d : ℂ) else 0
  by_cases hd : d = 0
  · simp [hd]
  · exact sum_ramanujanSum_divisors d j (Nat.pos_of_ne_zero hd)
private theorem ramFn_eq_moebius_convolution (j : ℕ) :
    ramFn j = divFn j * (μ : ArithmeticFunction ℂ) := by
  calc
    ramFn j = ramFn j * 1 := (mul_one _).symm
    _ = ramFn j * ((ζ : ArithmeticFunction ℂ) * (μ : ArithmeticFunction ℂ)) := by
      rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    _ = (ramFn j * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [ramFn_mul_zeta]
private theorem divFn_multiplicative (j : ℕ) : (divFn j).IsMultiplicative := by
  refine ⟨by simp [divFn], ?_⟩
  intro m n hmn
  change (if m * n ∣ j then ((m * n : ℕ) : ℂ) else 0) =
    (if m ∣ j then (m : ℂ) else 0) * (if n ∣ j then (n : ℂ) else 0)
  have hd : m * n ∣ j ↔ m ∣ j ∧ n ∣ j := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right m n).trans h, (dvd_mul_left n m).trans h⟩
    · rintro ⟨hm, hn⟩
      exact hmn.mul_dvd_of_dvd_of_dvd hm hn
  by_cases hm : m ∣ j <;> by_cases hn : n ∣ j <;> simp [hd, hm, hn]
private theorem ramanujan_multiplicative (m n j : ℕ) (hmn : m.Coprime n) :
    ramanujanSum (m * n) j = ramanujanSum m j * ramanujanSum n j := by
  have h : (ramFn j).IsMultiplicative := by
    rw [ramFn_eq_moebius_convolution]
    exact (divFn_multiplicative j).mul ArithmeticFunction.isMultiplicative_moebius.intCast
  exact h.2 hmn
private theorem ramanujan_moebius (m j : ℕ) (hm : 0 < m) :
    ramanujanSum m j = ∑ x ∈ m.divisorsAntidiagonal,
      (μ x.1 : ℂ) * (if x.2 ∣ j then (x.2 : ℂ) else 0) := by
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun d hd => sum_ramanujanSum_divisors d j hd)
  exact (h m hm).symm
private theorem ramanujan_gcd_of_dvd (m n j : ℕ) (hm : 0 < m) (hmn : m ∣ n) :
    ramanujanSum m j = ramanujanSum m (n.gcd j) := by
  rw [ramanujan_moebius m j hm, ramanujan_moebius m (n.gcd j) hm]
  apply Finset.sum_congr rfl
  intro x hx
  have hxn : x.2 ∣ n :=
    (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).trans hmn
  have hi : x.2 ∣ j ↔ x.2 ∣ n.gcd j := by
    exact ⟨fun h => Nat.dvd_gcd hxn h, fun h => h.trans (Nat.gcd_dvd_right _ _)⟩
  simp only [hi]
private theorem ramanujan_one (j : ℕ) : ramanujanSum 1 j = 1 := by
  simpa using sum_ramanujanSum_divisors 1 j Nat.zero_lt_one
private theorem prime_power_dvd_mixed_power (p q k a b : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    p ^ k ∣ p ^ a * q ^ b ↔ k ≤ a := by
  have hc : (p ^ k).Coprime (q ^ b) := ((Nat.coprime_primes hp hq).mpr hne).pow k b
  exact hc.dvd_mul_right.trans (Nat.pow_dvd_pow_iff_le_right hp.one_lt)
private theorem ramanujan_prime_power_mixed (p q a b k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ramanujanSum (p ^ (k + 1)) (p ^ a * q ^ b) =
      if k + 1 ≤ a then (Nat.totient (p ^ (k + 1)) : ℂ)
      else if k ≤ a then -(p ^ k : ℂ) else 0 := by
  rw [ramanujan_prime_power_values p (p ^ a * q ^ b) k hp]
  simp only [prime_power_dvd_mixed_power p q _ a b hp hq hne]
end D5.S3.Arith.RoldanCirculantEnergyP2Q3


open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
private theorem sum_gcd_class (n d : ℕ) (hdn : d ∣ n) (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range n with n.gcd k = d, f k) =
      ∑ t ∈ Finset.range (n / d) with t.Coprime (n / d), f (d * t) := by
  rcases hdn with ⟨m, rfl⟩
  rw [Nat.mul_div_cancel_left m hd]
  symm
  apply Finset.sum_bij (fun k _ => d * k)
  · simp only [Finset.mem_filter, Finset.mem_range, and_imp, Nat.Coprime]
    intro a ha1 ha2
    refine ⟨by nlinarith, ?_⟩
    rw [Nat.gcd_mul_left, Nat.gcd_comm m a, ha2, mul_one]
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hd hab
  · simp only [Finset.mem_filter, Finset.mem_range, exists_prop, and_imp]
    intro b hb1 hb2
    have hdb : d ∣ b := by
      rw [← hb2]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨t, rfl⟩ := hdb
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact (Nat.mul_lt_mul_left hd).mp hb1
    · rw [Nat.gcd_mul_left] at hb2
      have hb3 : m.gcd t = 1 := Nat.eq_of_mul_eq_mul_left hd (by simpa using hb2)
      simpa [Nat.Coprime, Nat.gcd_comm] using hb3
  · intro a ha
    rfl
private theorem gcd_class_phase_sum (n d j : ℕ) (hn : 0 < n) (hdn : d ∣ n) :
    (∑ k ∈ Finset.range n with n.gcd k = d,
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) * j / n))) =
      ramanujanSum (n / d) j := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  rw [sum_gcd_class n d hdn hd]
  unfold ramanujanSum
  apply Finset.sum_congr rfl
  intro t ht
  apply congrArg Complex.exp
  have hn' : n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
  conv_lhs => rw [hn']
  push_cast
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm' : ((n / d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hn hdn) hd).ne'
  field_simp [hd', hm']
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
noncomputable section
private theorem gcd_val_neg (n : ℕ) [NeZero n] (k : ZMod n) :
    n.gcd (-k).val = n.gcd k.val := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ZMod.neg_val, ite_eq_right hk, Nat.gcd_self_sub_right (Nat.le_of_lt (ZMod.val_lt k))]
private theorem gcdRow_even (n : ℕ) [NeZero n] (D : Finset ℕ) (k : ZMod n) :
    (fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) (-k) = (fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) k := by
  simp only [gcd_val_neg]
private theorem fin_equiv_val (n : ℕ) [NeZero n] (k : Fin n) :
    (ZMod.finEquiv n k).val = k.val := by
  rw [D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast]
  exact ZMod.val_natCast_of_lt k.isLt
private theorem stdAddChar_mul_nat (n : ℕ) [NeZero n] (k j : ZMod n) :
    ZMod.stdAddChar (k * j) =
      Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) * j.val / n)) := by
  have he : (((k.val : ℤ) * j.val : ℤ) : ZMod n) = k * j := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← he, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring
private theorem gcdRow_dft_range (n : ℕ) [NeZero n] (D : Finset ℕ) (j : ZMod n) :
    ZMod.dft (fun k => ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) k : ℂ)) j =
      ∑ k ∈ Finset.range n,
        Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) * j.val / n)) *
          if n.gcd k ∈ D then 1 else 0 := by
  rw [ZMod.dft_apply]
  have he : (∑ k : ZMod n, ZMod.stdAddChar (-(k * j)) * ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) k : ℂ)) =
      ∑ k : ZMod n, ZMod.stdAddChar (k * j) * ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) k : ℂ) := by
    apply Fintype.sum_equiv (Equiv.neg (ZMod n))
    intro k
    simp only [Equiv.neg_apply, neg_mul, gcdRow_even]
  simp only [smul_eq_mul]
  rw [he]
  calc
    _ = ∑ k : Fin n, ZMod.stdAddChar (ZMod.finEquiv n k * j) *
        ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) (ZMod.finEquiv n k) : ℂ) :=
      (Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _ (fun k => rfl)).symm
    _ = _ := by
      simp only [stdAddChar_mul_nat, fin_equiv_val]
      simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using
        (Fin.sum_univ_eq_sum_range (fun k =>
        Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) * j.val / n)) *
          if n.gcd k ∈ D then 1 else 0) n)
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
open scoped BigOperators
noncomputable section
private theorem gcdRow_dft_ramanujan (n : ℕ) [NeZero n] (D : Finset ℕ)
    (hD : D ⊆ n.divisors) (j : ZMod n) :
    ZMod.dft (fun k => ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) k : ℂ)) j =
      ∑ d ∈ D, ramanujanSum (n / d) j.val := by
  rw [gcdRow_dft_range]
  let phase : ℕ → ℂ := fun k =>
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) * j.val / n))
  have hg (k : ℕ) (_ : k ∈ Finset.range n) : n.gcd k ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne n⟩
  have hs := Finset.sum_fiberwise_of_maps_to hg
    (fun k => phase k * if n.gcd k ∈ D then (1 : ℂ) else 0)
  rw [← hs]
  calc
    _ = ∑ d ∈ n.divisors, if d ∈ D then ramanujanSum (n / d) j.val else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have h1 : (∑ k ∈ Finset.range n with n.gcd k = d,
          phase k * if n.gcd k ∈ D then (1 : ℂ) else 0) =
          if d ∈ D then (∑ k ∈ Finset.range n with n.gcd k = d, phase k) else 0 := by
        by_cases hmem : d ∈ D
        · simp only [hmem, ite_true]
          apply Finset.sum_congr rfl
          intro k hk
          rw [(Finset.mem_filter.mp hk).2, ite_eq_left hmem, mul_one]
        · simp only [hmem, ite_false]
          apply Finset.sum_eq_zero
          intro k hk
          rw [(Finset.mem_filter.mp hk).2, ite_eq_right hmem, mul_zero]
      rw [h1]
      split_ifs
      · exact gcd_class_phase_sum n d j.val (NeZero.pos n) (Nat.mem_divisors.mp hd).1
      · rfl
    _ = ∑ d ∈ D, ramanujanSum (n / d) j.val := by
      rw [← Finset.sum_subset hD]
      · apply Finset.sum_congr rfl
        intro d hd
        simp only [hd, ite_true]
      · intro d hd hnot
        simp only [hnot, ite_false]
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
theorem sum_gcd_multiplicity (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, F (n.gcd j)) =
      ∑ e ∈ n.divisors, (Nat.totient (n / e) : ℝ) * F e := by
  have hg (j : ℕ) (_ : j ∈ Finset.range n) : n.gcd j ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hg (fun j => F (n.gcd j))]
  apply Finset.sum_congr rfl
  intro e he
  calc
    _ = ∑ j ∈ Finset.range n with n.gcd j = e, F e := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = (Nat.totient (n / e) : ℝ) * F e := by
      rw [Nat.totient_div_of_dvd (Nat.mem_divisors.mp he).1]
      simp only [Finset.sum_const, nsmul_eq_mul]
end D5.S3.Arith.RoldanCirculantEnergyP2Q3


/-! Binding conventions for D. G. Roldán, "Graph Energy Maximisation for Integral Circulant Graphs of Order
n = p^2 q^3", arXiv:2604.09491v1, Section 1 (integral circulant graphs, energy) and Conjecture 1.3. -/
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
def adjacency (n : ℕ) (D : Finset ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => if Nat.gcd ((a - b : Fin n) : ℕ) n ∈ D then 1 else 0
noncomputable def energy (n : ℕ) (D : Finset ℕ) : ℝ :=
  (((adjacency n D).charpoly.roots).map fun x => |x|).sum
def Dstar (p q : ℕ) : Finset ℕ := {1, p ^ 2, p * q, q ^ 2, p ^ 2 * q ^ 2, p * q ^ 3}
def claim : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → Odd p → Odd q →
    Dstar p q ⊆ (p ^ 2 * q ^ 3).properDivisors ∧
    ∀ D : Finset ℕ, D.Nonempty → D ⊆ (p ^ 2 * q ^ 3).properDivisors → D ≠ Dstar p q →
      energy (p ^ 2 * q ^ 3) D < energy (p ^ 2 * q ^ 3) (Dstar p q)
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
open Matrix
noncomputable section
private theorem adjacency_reindex (n : ℕ) [NeZero n] (D : Finset ℕ) :
    D5.S3.Arith.RoldanCirculantEnergyP2Q3.adjacency n D =
      Matrix.reindex (ZMod.finEquiv n).symm.toEquiv (ZMod.finEquiv n).symm.toEquiv
        (Matrix.circulant ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0))) := by
  ext a b
  change (if Nat.gcd ((a - b : Fin n) : ℕ) n ∈ D then (1 : ℝ) else 0) =
    if n.gcd ((ZMod.finEquiv n a) - (ZMod.finEquiv n b)).val ∈ D then 1 else 0
  rw [← map_sub, fin_equiv_val, Nat.gcd_comm]
private theorem energy_eq_dft (n : ℕ) [NeZero n] (D : Finset ℕ) :
    D5.S3.Arith.RoldanCirculantEnergyP2Q3.energy n D =
      ∑ j : ZMod n, |(ZMod.dft (fun k => ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0) k : ℂ)) j).re| := by
  unfold D5.S3.Arith.RoldanCirculantEnergyP2Q3.energy
  rw [adjacency_reindex, Matrix.charpoly_reindex,
    real_circulant_roots n ((fun k : ZMod n => if n.gcd k.val ∈ D then (1 : ℝ) else 0)) (gcdRow_even n D)]
  simp only [Multiset.map_map, Function.comp_def, Finset.sum]
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
noncomputable section
private theorem energy_eq_ramanujan (n : ℕ) [NeZero n] (D : Finset ℕ)
    (hD : D ⊆ n.divisors) :
    D5.S3.Arith.RoldanCirculantEnergyP2Q3.energy n D =
      ∑ j : ZMod n, |(∑ d ∈ D, ramanujanSum (n / d) j.val).re| := by
  rw [energy_eq_dft]
  apply Finset.sum_congr rfl
  intro j hj
  rw [gcdRow_dft_ramanujan n D hD j]
private theorem energy_divisor_formula (n : ℕ) [NeZero n] (D : Finset ℕ)
    (hD : D ⊆ n.divisors) :
    D5.S3.Arith.RoldanCirculantEnergyP2Q3.energy n D =
      ∑ e ∈ n.divisors, (Nat.totient (n / e) : ℝ) *
        |(∑ d ∈ D, ramanujanSum (n / d) e).re| := by
  rw [energy_eq_ramanujan n D hD]
  let F : ℕ → ℝ := fun e => |(∑ d ∈ D, ramanujanSum (n / d) e).re|
  have hclass (j : ℕ) :
      (∑ d ∈ D, ramanujanSum (n / d) j) =
        ∑ d ∈ D, ramanujanSum (n / d) (n.gcd j) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := (Nat.mem_divisors.mp (hD hd)).1
    have hd0 := Nat.pos_of_mem_divisors (hD hd)
    exact ramanujan_gcd_of_dvd (n / d) n j
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hdn) hd0) (Nat.div_dvd_of_dvd hdn)
  calc
    _ = ∑ j : ZMod n, F (n.gcd j.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hclass j.val]
    _ = ∑ j : Fin n, F (n.gcd j.val) := by
      exact (Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _
        (fun j => by
          change F (n.gcd j.val) = F (n.gcd (ZMod.finEquiv n j).val)
          rw [fin_equiv_val])).symm
    _ = ∑ j ∈ Finset.range n, F (n.gcd j) := Fin.sum_univ_eq_sum_range (fun j => F (n.gcd j)) n
    _ = _ := sum_gcd_multiplicity n (NeZero.pos n) F
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

open scoped BigOperators Pointwise
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
private def divisorValue (p q : ℕ) (c : Fin 3) (f : Fin 4) : ℕ := p ^ c.val * q ^ f.val
private def encode (p q : ℕ) (D : Finset ℕ) : Fin 2048 :=
  ⟨Nat.ofBits (fun i : Fin 11 => decide (p ^ (i.val / 4) * q ^ (i.val % 4) ∈ D)),
    Nat.ofBits_lt_two_pow _⟩
private theorem divisor_exponents (p q d : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hd : d ∈ (p ^ 2 * q ^ 3).divisors) :
    ∃ (c : Fin 3) (f : Fin 4), d = divisorValue p q c f := by
  rw [Nat.divisors_mul] at hd
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hd
  obtain ⟨c, hc, rfl⟩ := (Nat.mem_divisors_prime_pow hp 2).mp hx
  obtain ⟨f, hf, rfl⟩ := (Nat.mem_divisors_prime_pow hq 3).mp hy
  exact ⟨⟨c, by omega⟩, ⟨f, by omega⟩, rfl⟩
private theorem encode_testBit (p q : ℕ) (D : Finset ℕ) (i : Fin 11) :
    (encode p q D).val.testBit i.val =
      decide (p ^ (i.val / 4) * q ^ (i.val % 4) ∈ D) := by
  change (Nat.ofBits (fun j : Fin 11 => decide (p ^ (j.val / 4) * q ^ (j.val % 4) ∈ D))).testBit i.val = _
  exact Nat.testBit_ofBits_lt (fun j : Fin 11 => decide (p ^ (j.val / 4) * q ^ (j.val % 4) ∈ D)) i.val i.isLt
end D5.S3.Arith.RoldanCirculantEnergyP2Q3


namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
private theorem proper_of_factor (d r n : ℕ) (hd : 0 < d) (hr : 1 < r) (hn : n = d * r) :
    d ∈ n.properDivisors := by
  rw [hn, Nat.mem_properDivisors]
  exact ⟨dvd_mul_right d r, (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hr hd)⟩
private theorem dstar_admissible (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    Dstar p q ⊆ (p ^ 2 * q ^ 3).properDivisors := by
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hp2 : 1 < p ^ 2 := one_lt_pow₀ hp1 (by decide)
  have hq2 : 1 < q ^ 2 := one_lt_pow₀ hq1 (by decide)
  have hq3 : 1 < q ^ 3 := one_lt_pow₀ hq1 (by decide)
  simp only [Dstar, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact proper_of_factor 1 (p ^ 2 * q ^ 3) _ Nat.zero_lt_one (one_lt_mul_of_lt_of_le hp2 hq3.le) (by ring)
  · exact proper_of_factor (p ^ 2) (q ^ 3) _ (by positivity) hq3 (by ring)
  · exact proper_of_factor (p * q) (p * q ^ 2) _ (mul_pos hp0 hq0) (one_lt_mul_of_lt_of_le hp1 hq2.le) (by ring)
  · exact proper_of_factor (q ^ 2) (p ^ 2 * q) _ (pow_pos hq0 2) (one_lt_mul_of_lt_of_le hp2 hq1.le) (by ring)
  · exact proper_of_factor (p ^ 2 * q ^ 2) q _ (by positivity) hq1 (by ring)
  · exact proper_of_factor (p * q ^ 3) p _ (by positivity) hp1 (by ring)
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
private theorem divisorValue_injective (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Function.Injective (fun cf : Fin 3 × Fin 4 => divisorValue p q cf.1 cf.2) := by
  rintro ⟨c,f⟩ ⟨c',f'⟩ he
  change p ^ c.val * q ^ f.val = p ^ c'.val * q ^ f'.val at he
  have h1 : c.val ≤ c'.val :=
    (prime_power_dvd_mixed_power p q c.val c'.val f'.val hp hq hne).mp
      (he ▸ dvd_mul_right (p ^ c.val) (q ^ f.val))
  have h2 : c'.val ≤ c.val :=
    (prime_power_dvd_mixed_power p q c'.val c.val f.val hp hq hne).mp
      (he.symm ▸ dvd_mul_right (p ^ c'.val) (q ^ f'.val))
  have he' : q ^ f.val * p ^ c.val = q ^ f'.val * p ^ c'.val := by
    simpa [divisorValue, mul_comm] using he
  have h3 : f.val ≤ f'.val :=
    (prime_power_dvd_mixed_power q p f.val f'.val c'.val hq hp hne.symm).mp
      (he' ▸ dvd_mul_right (q ^ f.val) (p ^ c.val))
  have h4 : f'.val ≤ f.val :=
    (prime_power_dvd_mixed_power q p f'.val f.val c.val hq hp hne.symm).mp
      (he'.symm ▸ dvd_mul_right (q ^ f'.val) (p ^ c'.val))
  have hc : c = c' := Fin.le_antisymm h1 h2
  have hf : f = f' := Fin.le_antisymm h3 h4
  simp [hc,hf]
private theorem sum_divisor_grid (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    (∑ e ∈ (p ^ 2 * q ^ 3).divisors, F e) =
      ∑ c : Fin 3, ∑ f : Fin 4, F (divisorValue p q c f) := by
  symm
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_bij (fun cf _ => divisorValue p q cf.1 cf.2)
  · intro cf hcf
    apply Nat.mem_divisors.mpr
    refine ⟨Nat.mul_dvd_mul (pow_dvd_pow p (by omega : cf.1.val ≤ 2))
      (pow_dvd_pow q (by omega : cf.2.val ≤ 3)), by exact (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne'⟩
  · intro a ha b hb hab
    exact divisorValue_injective p q hp hq hne hab
  · intro d hd
    obtain ⟨c,f,rfl⟩ := divisor_exponents p q d hp hq hd
    exact ⟨(c,f), Finset.mem_univ _, rfl⟩
  · intro a ha
    rfl
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
private theorem encode_switch (p q : ℕ) (D : Finset ℕ)
    (hD : D ⊆ (p ^ 2 * q ^ 3).properDivisors) (c : Fin 3) (f : Fin 4) :
    switch (encode p q D).val c f =
      if divisorValue p q c f ∈ D then (1 : ℤ) else 0 := by
  by_cases htop : c.val = 2 ∧ f.val = 3
  · have hn : divisorValue p q c f = p ^ 2 * q ^ 3 := by simp [divisorValue, htop.1, htop.2]
    have hnot : divisorValue p q c f ∉ D := by
      intro h
      have hh := (Nat.mem_properDivisors.mp (hD h)).2
      rw [hn] at hh
      exact (lt_irrefl _) hh
    simp [switch, htop, hnot]
  · have hi : 4 * c.val + f.val < 11 := by omega
    have hb := encode_testBit p q D ⟨4 * c.val + f.val, hi⟩
    have hdiv : (4 * c.val + f.val) / 4 = c.val := by
      rw [Nat.mul_add_div (by decide : 0 < 4), Nat.div_eq_of_lt f.isLt, Nat.add_zero]
    have hmod : (4 * c.val + f.val) % 4 = f.val :=
      (Nat.mul_add_mod 4 c.val f.val).trans (Nat.mod_eq_of_lt f.isLt)
    simp only [hdiv, hmod] at hb
    by_cases hm : p ^ c.val * q ^ f.val ∈ D <;>
      simp [switch, htop, hb, divisorValue, hm]
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
private def decode (p q mask : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun cf : Fin 3 × Fin 4 => switch mask cf.1 cf.2 = 1).image
    (fun cf => divisorValue p q cf.1 cf.2)
private theorem decode_encode (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (D : Finset ℕ) (hD : D ⊆ (p ^ 2 * q ^ 3).properDivisors) :
    decode p q (encode p q D).val = D := by
  ext d
  constructor
  · intro h
    obtain ⟨⟨c,f⟩,hcf,rfl⟩ := Finset.mem_image.mp h
    have hs := (Finset.mem_filter.mp hcf).2
    rw [encode_switch p q D hD] at hs
    split_ifs at hs with hmem
    · exact hmem
    · norm_num at hs
  · intro hd
    have hdiv : d ∈ (p ^ 2 * q ^ 3).divisors :=
      Nat.mem_divisors.mpr ⟨(Nat.mem_properDivisors.mp (hD hd)).1, by exact (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne'⟩
    obtain ⟨c,f,rfl⟩ := divisor_exponents p q d hp hq hdiv
    apply Finset.mem_image.mpr
    refine ⟨(c,f), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [encode_switch p q D hD]
    simp only [hd, ite_true]
private theorem decode_star (p q : ℕ) : decode p q star = Dstar p q := by
  have hs : (Finset.univ.filter fun cf : Fin 3 × Fin 4 =>
      switch star cf.1 cf.2 = 1) =
      {(0,0), (0,2), (1,1), (1,3), (2,0), (2,2)} := by
    exact Finset.val_inj.mp rfl
  unfold decode
  rw [hs]
  simp only [Finset.image_insert, Finset.image_singleton]
  norm_num only [divisorValue, Fin.val_zero, Fin.val_ofNat, pow_zero, pow_one, one_mul, mul_one]
  unfold Dstar
  ext d
  simp only [Finset.mem_insert, Finset.mem_singleton]
  norm_num
  tauto
private theorem encode_ne_star (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (D : Finset ℕ) (hD : D ⊆ (p ^ 2 * q ^ 3).properDivisors) (hne : D ≠ Dstar p q) :
    (encode p q D).val ≠ star := by
  intro he
  apply hne
  rw [← decode_encode p q hp hq D hD, he, decode_star]
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
private theorem decode_subset_divisors (p q mask : ℕ) (hp : 0 < p) (hq : 0 < q) :
    decode p q mask ⊆ (p ^ 2 * q ^ 3).divisors := by
  intro d hd
  obtain ⟨⟨c,f⟩,hcf,rfl⟩ := Finset.mem_image.mp hd
  apply Nat.mem_divisors.mpr
  exact ⟨Nat.mul_dvd_mul (pow_dvd_pow p (by omega : c.val ≤ 2))
    (pow_dvd_pow q (by omega : f.val ≤ 3)), by positivity⟩
private theorem sum_decode (p q mask : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (F : ℕ → ℂ) :
    (∑ d ∈ decode p q mask, F d) =
      ∑ c : Fin 3, ∑ f : Fin 4, (switch mask c f : ℂ) * F (divisorValue p q c f) := by
  unfold decode
  rw [Finset.sum_image]
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro f _
    by_cases ht : c.val = 2 ∧ f.val = 3
    · simp [switch, ht]
    · by_cases hb : mask.testBit (4*c.val+f.val)
      · simp [switch, ht, hb]
      · simp [switch, ht, hb]
  · intro a ha b hb he
    exact divisorValue_injective p q hp hq hne he
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
private theorem p2_ramanujan_table (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a c : Fin 3) (b : ℕ) :
    ramanujanSum (p ^ (2 - c.val)) (p ^ a.val * q ^ b) =
      evalW (A a c) ((p : ℂ) - 3) := by
  fin_cases c <;> norm_num only
  · rw [ramanujan_prime_power_mixed p q a.val b 1 hp hq hne]
    fin_cases a <;>
      norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, A, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hp, Nat.totient_prime hp,
        Nat.cast_sub hp.one_lt.le] <;> ring
  · rw [ramanujan_prime_power_mixed p q a.val b 0 hp hq hne]
    fin_cases a <;>
      norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, A, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hp, Nat.totient_prime hp,
        Nat.cast_sub hp.one_lt.le] <;> ring
  · simp only [pow_zero, ramanujan_one]
    fin_cases a <;> norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, A, Fin.sum_univ_succ]
private theorem q3_ramanujan_table (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : ℕ) (b f : Fin 4) :
    ramanujanSum (q ^ (3 - f.val)) (p ^ a * q ^ b.val) =
      evalW (B b f) ((q : ℂ) - 3) := by
  rw [mul_comm (p ^ a) (q ^ b.val)]
  fin_cases f <;> norm_num only
  · rw [ramanujan_prime_power_mixed q p b.val a 2 hq hp hne.symm]
    fin_cases b <;>
      norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, B, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hq, Nat.totient_prime hq,
        Nat.cast_sub hq.one_lt.le] <;> ring
  · rw [ramanujan_prime_power_mixed q p b.val a 1 hq hp hne.symm]
    fin_cases b <;>
      norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, B, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hq, Nat.totient_prime hq,
        Nat.cast_sub hq.one_lt.le] <;> ring
  · rw [ramanujan_prime_power_mixed q p b.val a 0 hq hp hne.symm]
    fin_cases b <;>
      norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, B, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hq, Nat.totient_prime hq,
        Nat.cast_sub hq.one_lt.le] <;> ring
  · simp only [pow_zero, ramanujan_one]
    fin_cases b <;> norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, B, Fin.sum_univ_succ]
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
private theorem p2_totient_table (p : ℕ) (hp : p.Prime) (a : Fin 3) :
    (Nat.totient (p ^ (2 - a.val)) : ℂ) = evalW (wA a) ((p : ℂ) - 3) := by
  fin_cases a <;>
    norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, wA, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hp, Nat.totient_prime hp,
      Nat.cast_sub hp.one_lt.le] <;> ring
private theorem q3_totient_table (q : ℕ) (hq : q.Prime) (b : Fin 4) :
    (Nat.totient (q ^ (3 - b.val)) : ℂ) = evalW (wB b) ((q : ℂ) - 3) := by
  fin_cases b <;>
    norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, wB, Fin.sum_univ_succ, Nat.totient_prime_pow_succ hq, Nat.totient_prime hq,
      Nat.cast_sub hq.one_lt.le] <;> ring
private theorem quotient_p2q3 (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (c : Fin 3) (f : Fin 4) :
    (p ^ 2 * q ^ 3) / (p ^ c.val * q ^ f.val) = p ^ (2 - c.val) * q ^ (3 - f.val) := by
  apply Nat.div_eq_of_eq_mul_right (by positivity : 0 < p ^ c.val * q ^ f.val)
  rw [show (p ^ c.val * q ^ f.val) * (p ^ (2 - c.val) * q ^ (3 - f.val)) =
    (p ^ c.val * p ^ (2 - c.val)) * (q ^ f.val * q ^ (3 - f.val)) by ring]
  rw [← pow_add, ← pow_add, Nat.add_sub_of_le (by omega : c.val ≤ 2),
    Nat.add_sub_of_le (by omega : f.val ≤ 3)]
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open scoped BigOperators
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
noncomputable section
private theorem evalW_ofReal {r : ℕ} (C : Fin r → ℤ) (x : ℝ) :
    evalW C (x : ℂ) = (evalW (R := ℝ) C x : ℂ) := by
  simp [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
private theorem lcoeff_evaluation (mask : ℕ) (a : Fin 3) (b : Fin 4) (u v : ℝ) :
    (eval (lcoeff mask a b) u v : ℂ) =
      ∑ c : Fin 3, ∑ f : Fin 4,
        (switch mask c f : ℂ) * evalW (A a c) (u : ℂ) * evalW (B b f) (v : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate.eval, evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
      Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate.lcoeff, A, B, Fin.sum_univ_succ] <;> ring
private theorem ramanujan_grid_table (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a c : Fin 3) (b f : Fin 4) :
    ramanujanSum ((p ^ 2 * q ^ 3) / divisorValue p q c f) (divisorValue p q a b) =
      evalW (A a c) ((p : ℂ)-3) * evalW (B b f) ((q : ℂ)-3) := by
  unfold divisorValue
  rw [quotient_p2q3 p q hp.pos hq.pos,
    ramanujan_multiplicative _ _ _ (((Nat.coprime_primes hp hq).mpr hne).pow _ _),
    p2_ramanujan_table p q hp hq hne a c b.val,
    q3_ramanujan_table p q hp hq hne a.val b f]
private theorem totient_grid_table (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : Fin 3) (b : Fin 4) :
    (Nat.totient ((p ^ 2 * q ^ 3) / divisorValue p q a b) : ℝ) =
      evalW (wA a) ((p : ℝ)-3) * evalW (wB b) ((q : ℝ)-3) := by
  apply Complex.ofReal_injective
  push_cast
  unfold divisorValue
  rw [quotient_p2q3 p q hp.pos hq.pos,
    Nat.totient_mul (((Nat.coprime_primes hp hq).mpr hne).pow _ _)]
  push_cast
  rw [p2_totient_table p hp a, q3_totient_table q hq b]
  rw [← evalW_ofReal, ← evalW_ofReal]
  push_cast
  rfl
private theorem energy_decode_model (p q mask : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    D5.S3.Arith.RoldanCirculantEnergyP2Q3.energy (p ^ 2 * q ^ 3) (decode p q mask) =
      modelEnergy mask ((p : ℝ)-3) ((q : ℝ)-3) := by
  let : NeZero (p ^ 2 * q ^ 3) := ⟨(Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne'⟩
  rw [energy_divisor_formula _ _ (decode_subset_divisors p q mask hp.pos hq.pos),
    sum_divisor_grid p q hp hq hne]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [totient_grid_table p q hp hq hne a b, sum_decode p q mask hp hq hne]
  simp_rw [ramanujan_grid_table p q hp hq hne]
  have hlin := lcoeff_evaluation mask a b ((p : ℝ)-3) ((q : ℝ)-3)
  push_cast at hlin
  simp only [mul_assoc] at hlin
  rw [← hlin, Complex.ofReal_re]
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3

namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3
open D5.S3.Arith.RoldanCirculantEnergyP2Q3
theorem result : claim := by
  intro p q hp hq hne hop hoq
  refine ⟨dstar_admissible p q hp hq, ?_⟩
  intro D hDnon hD hDne
  have hp3 : 3 ≤ p := hp.odd_iff.mp hop
  have hq3 : 3 ≤ q := hq.odd_iff.mp hoq
  have hu : 0 ≤ (p : ℝ)-3 := sub_nonneg.mpr (by exact_mod_cast hp3)
  have hv : 0 ≤ (q : ℝ)-3 := sub_nonneg.mpr (by exact_mod_cast hq3)
  have hg := model_gap (encode p q D) (encode_ne_star p q hp hq D hD hDne)
    ((p : ℝ)-3) ((q : ℝ)-3) hu hv
  rw [← energy_decode_model p q star hp hq hne,
    ← energy_decode_model p q (encode p q D).val hp hq hne,
    decode_star, decode_encode p q hp hq D hD] at hg
  linarith
end D5.S3.Arith.RoldanCirculantEnergyP2Q3
