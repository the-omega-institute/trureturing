/- GID: D5/S3/Arith/Divisors/SunA228884
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/SunA228884
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Zhi-Wei Sun OEIS A228884 composite gcd-determinant prime divisors. -/

/- Judgement form for the external named open-problem settlement.
   proof_shape: result: bind-only; consumer=none.
   proof_shape: B_le_pow: bind-only; consumers=prime_dvd_B_lt.
   proof_shape: prime_dvd_B_lt: bind-only; consumers=prime_dvd_zero_eigen_lt.
   proof_shape: prime_dvd_zero_eigen_lt: bind-only; consumers=E_higher_support.
   proof_shape: prime_dvd_nonzero_eigen_lt: bind-only; consumers=E_higher_support.
   proof_shape: gcd_zmod: bind-only; consumers=C_eq_K.
   proof_shape: C_eq_K: bind-only; consumers=D_eq_det_K.
   proof_shape: D_eq_det_K: bind-only; consumers=D_coprime, D_spectral.
   proof_shape: K_crt: bind-only; consumers=D_coprime.
   proof_shape: D_coprime: bind-only; consumers=all_support.
   proof_shape: gcd_dft: bind-only; consumers=gcd_dft_prime_power.
   proof_shape: divCount_succ: bind-only; consumers=localSpectrum_formula.
   proof_shape: localSpectrum_succ: bind-only; consumers=localSpectrum_formula.
   proof_shape: localSpectrum_formula: bind-only; consumers=D_prime_power.
   proof_shape: gcd_dft_prime_power: bind-only; consumers=D_prime_power.
   proof_shape: det_circulant: bind-only; consumers=D_spectral.
   proof_shape: D_spectral: bind-only; consumers=D_prime_power.
   proof_shape: D_prime_power: bind-only; consumers=prime_power_support.
   proof_shape: divCount_bounds: bind-only; consumers=E_higher_support.
   proof_shape: E_zero: bind-only; consumers=E_higher_support.
   proof_shape: E_one_exponent_support: bind-only; consumers=prime_power_support.
   proof_shape: E_higher_support: bind-only; consumers=prime_power_support.
   proof_shape: prime_power_support: bind-only; consumers=all_support.
   proof_shape: all_support: bind-only; consumers=result.
   escape_witness: none.
   admission_basis: open-problem-resolution (#22131; Proved).
   Direct frozen dependencies (dev report; original private identities for published owners):
     D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast
       sha256:6062729cd00b090edb5dfcccd635f4a563a8a66f60deb5d1c6d91f2195edc1b1.
     D5.S3.Quantum.Matrix.CirculantCharpoly.circulant_charpoly
       sha256:2eed444fe2ee2450ea82737e4427ae3c2655e6ce6da422d2c7190f6bd536c70d.
     D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity.ramanujanSum
       sha256:908a77e52c19378791b1586759e38bf57a8f5795e3c16983c9184dba91a1b789.
     _private.D5.S3.Arith.RoldanCirculantEnergyP2Q3.0.D5.S3.Arith.RoldanCirculantEnergyP2Q3.gcdRow_dft_ramanujan
       sha256:ca22353ffbf79c4e8fc837e7948b6623baaa1342547c9da66522ade278f7427c.
     _private.D5.S3.Arith.RoldanCirculantEnergyP2Q3.0.D5.S3.Arith.RoldanCirculantEnergyP2Q3.ramanujan_prime_power
       sha256:20b64bb2fc5b18dbe67a0f38f373ebb60c92554c3dc6f241bbcc8eef701c3f95.
     _private.D5.S3.Arith.RoldanCirculantEnergyP2Q3.0.D5.S3.Arith.RoldanCirculantEnergyP2Q3.ramanujan_one
       sha256:e327ebb4f79e5bf7da2e3f395cec85aabff1f9e6b52539dc091acaa38616cfd3.
   The source matrix is stated with integer subtraction and Int.gcd.
   Its ZMod implementation uses Matrix.circulant, and the proof applies the original Roldan
   Fourier and Ramanujan declarations by their public names.
   The three original private identities above identify the unchanged statements and proofs.
   The public owner and its frozen importers require canonical re-pinning in Stage B.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22671.
-/

import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import D5.S3.Arith.RoldanCirculantEnergyP2Q3
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import D5.S3.Quantum.Matrix.CirculantCharpoly

/-! Binding definitions for Zhi-Wei Sun, OEIS A228884, COMMENTS clause (ii).
The matrix uses the source's row and column labels 1, ..., n.
Integer subtraction precedes Int.gcd; there is no truncated natural subtraction.
-/

namespace D5.S3.Arith.Divisors.SunA228884

/-- The integer matrix with (i,j)-entry gcd(i-j,n), for 1 <= i,j <= n. -/
def C (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (Int.gcd (((i.val : ℤ) + 1) - ((j.val : ℤ) + 1)) (n : ℤ) : ℤ)

/-- The source sequence a(n), including the determinant of the empty matrix. -/
def D (n : ℕ) : ℤ := Matrix.det (C n)

/-- Clause (ii): every prime divisor of a(n) is smaller than a composite index n. -/
def claim : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ¬ Nat.Prime n →
    ∀ (q : ℕ), Nat.Prime q → (q : ℤ) ∣ D n → q < n

end D5.S3.Arith.Divisors.SunA228884

namespace D5.S3.Arith.Divisors.SunA228884

private def B (p a : ℕ) : ℕ := (a + 1) * (p - 1) + 1

private theorem B_le_pow (p a : ℕ) (hp : 2 ≤ p) (ha : 2 ≤ a) :
    B p a ≤ p ^ a := by
  have hlow : B p a ≤ p * (1 + (a-1)*(p-1)) := by
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hp
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le ha
    have hx : 2+x-1 = x+1 := by
      simpa only [Nat.add_comm] using
        (Nat.sub_add_comm (n := 2) (m := x) (k := 1) (by decide))
    have hy : 2+y-1 = y+1 := by
      simpa only [Nat.add_comm] using
        (Nat.sub_add_comm (n := 2) (m := y) (k := 1) (by decide))
    simp only [B, hx, hy]
    nlinarith [Nat.zero_le (y*x^2), Nat.zero_le (2*y*x), Nat.zero_le (x^2)]
  have hb := one_add_mul_le_pow_of_sq_nonneg
    (a := p-1) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (a-1)
  have hp' : 1 + (p-1) = p := by
    exact Nat.add_sub_of_le (Nat.le_trans (by decide : 1 ≤ 2) hp)
  rw [hp'] at hb
  calc
    B p a ≤ p * (1 + (a-1)*(p-1)) := hlow
    _ ≤ p * p^(a-1) := Nat.mul_le_mul_left p hb
    _ = p^a := by rw [← pow_succ']; congr 1; omega

private theorem prime_dvd_B_lt (p a q : ℕ) (hp : Nat.Prime p)
    (ha : 2 ≤ a) (hq : Nat.Prime q) (hd : q ∣ B p a) : q < p ^ a := by
  have hbpos : 0 < B p a := by
    exact Nat.zero_lt_succ ((a + 1) * (p - 1))
  have hle := (Nat.le_of_dvd hbpos hd).trans (B_le_pow p a hp.two_le ha)
  refine lt_of_le_of_ne hle ?_
  intro heq
  exact Nat.Prime.not_prime_pow ha (heq ▸ hq)

private theorem prime_dvd_zero_eigen_lt (p a q : ℕ) (hp : Nat.Prime p)
    (ha : 2 ≤ a) (hq : Nat.Prime q)
    (hd : q ∣ p ^ (a - 1) * B p a) : q < p ^ a := by
  rcases hq.dvd_mul.mp hd with hd | hd
  · have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)
    subst q
    calc
      p = p ^ 1 := (pow_one p).symm
      _ < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  · exact prime_dvd_B_lt p a q hp ha hq hd

private theorem prime_dvd_nonzero_eigen_lt (p a s q : ℕ) (hp : Nat.Prime p)
    (ha : 2 ≤ a) (hs : s < a) (hq : Nat.Prime q)
    (hd : q ∣ (s + 1) * (p - 1) * p ^ (a - 1)) : q < p ^ a := by
  have hplt : p < p ^ a := by
    calc
      p = p ^ 1 := (pow_one p).symm
      _ < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  rcases hq.dvd_mul.mp hd with hd | hd
  · rcases hq.dvd_mul.mp hd with hd | hd
    · calc
        q ≤ s + 1 := Nat.le_of_dvd (by omega) hd
        _ ≤ a := by omega
        _ < 2 ^ a := Nat.lt_two_pow_self
        _ ≤ p ^ a := Nat.pow_le_pow_left hp.two_le a
    · exact (Nat.le_of_dvd (by have := hp.two_le; omega) hd).trans_lt
        ((Nat.sub_lt hp.pos (by omega)).trans hplt)
  · have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)
    simpa [heq] using hplt

end D5.S3.Arith.Divisors.SunA228884

namespace D5.S3.Arith.Divisors.SunA228884
noncomputable section
open Matrix
open scoped Kronecker

private def K (n : ℕ) : Matrix (ZMod n) (ZMod n) ℤ :=
  Matrix.circulant (fun k => (Nat.gcd k.val n : ℤ))

private theorem gcd_zmod (n : ℕ) [NeZero n] (t : ℤ) :
    Nat.gcd (t : ZMod n).val n = Int.gcd t (n : ℤ) := by
  rw [← Int.gcd_natCast_natCast, ZMod.val_intCast, Int.gcd_emod]

private theorem C_eq_K (n : ℕ) [NeZero n] :
    C n = (K n).submatrix (ZMod.finEquiv n) (ZMod.finEquiv n) := by
  ext i j
  have he (k : Fin n) : ZMod.finEquiv n k = (k.val : ZMod n) := by
    exact D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.finEquiv_eq_natCast k
  simp only [C, K, Matrix.submatrix_apply, he]
  have ht : ((i.val : ℤ) + 1) - ((j.val : ℤ) + 1) = (i.val : ℤ) - j.val := by
    exact Int.add_sub_add_right (i.val : ℤ) 1 (j.val : ℤ)
  rw [ht, ← gcd_zmod n ((i.val : ℤ) - j.val)]
  simp

private theorem D_eq_det_K (n : ℕ) [NeZero n] : D n = (K n).det := by
  rw [D, C_eq_K]
  exact Matrix.det_submatrix_equiv_self (ZMod.finEquiv n).toEquiv (K n)

private theorem K_crt (u v : ℕ) [NeZero u] [NeZero v] (h : u.Coprime v) :
    K (u*v) = (K u ⊗ₖ K v).submatrix (ZMod.chineseRemainder h) (ZMod.chineseRemainder h) := by
  haveI : NeZero (u*v) := ⟨Nat.mul_ne_zero (NeZero.ne u) (NeZero.ne v)⟩
  have hf (x : ZMod (u*v)) :
      (ZMod.chineseRemainder h x).1 = (x.val : ZMod u) := by
    simpa only [ZMod.natCast_zmod_val, Prod.fst_natCast] using
      congrArg Prod.fst (map_natCast (ZMod.chineseRemainder h) x.val)
  have hg (x : ZMod (u*v)) :
      (ZMod.chineseRemainder h x).2 = (x.val : ZMod v) := by
    simpa only [ZMod.natCast_zmod_val, Prod.snd_natCast] using
      congrArg Prod.snd (map_natCast (ZMod.chineseRemainder h) x.val)
  ext i j
  change (Nat.gcd (i-j).val (u*v) : ℤ) =
    (Nat.gcd ((ZMod.chineseRemainder h i).1 - (ZMod.chineseRemainder h j).1).val u : ℤ) *
    (Nat.gcd ((ZMod.chineseRemainder h i).2 - (ZMod.chineseRemainder h j).2).val v : ℤ)
  have hd1 : (ZMod.chineseRemainder h i).1 - (ZMod.chineseRemainder h j).1 =
      ((i-j).val : ZMod u) := by
    simpa only [map_sub, Prod.fst_sub] using hf (i-j)
  have hd2 : (ZMod.chineseRemainder h i).2 - (ZMod.chineseRemainder h j).2 =
      ((i-j).val : ZMod v) := by
    simpa only [map_sub, Prod.snd_sub] using hg (i-j)
  rw [hd1, hd2, ZMod.val_natCast, ZMod.val_natCast]
  rw [← Nat.gcd_rec u (i-j).val, ← Nat.gcd_rec v (i-j).val]
  rw [Nat.Coprime.gcd_mul _ h, Nat.cast_mul]
  simp only [Nat.gcd_comm]

private theorem D_coprime (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (h : u.Coprime v) :
    D (u*v) = D u ^ v * D v ^ u := by
  letI : NeZero u := ⟨hu.ne'⟩
  letI : NeZero v := ⟨hv.ne'⟩
  letI : NeZero (u*v) := ⟨(Nat.mul_pos hu hv).ne'⟩
  rw [D_eq_det_K, K_crt u v h]
  change ((K u ⊗ₖ K v).submatrix (ZMod.chineseRemainder h).toEquiv
    (ZMod.chineseRemainder h).toEquiv).det = _
  rw [Matrix.det_submatrix_equiv_self,
    Matrix.det_kronecker, ZMod.card, ZMod.card, ← D_eq_det_K, ← D_eq_det_K]

end
end D5.S3.Arith.Divisors.SunA228884

namespace D5.S3.Arith.Divisors.SunA228884
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators
open Finset
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

private theorem gcd_dft (n : ℕ) [NeZero n] (j : ZMod n) :
    ZMod.dft (fun k : ZMod n => (Nat.gcd n k.val : ℂ)) j =
    ∑ d ∈ n.divisors, (d : ℂ) * ramanujanSum (n/d) j.val := by
  classical
  have hh (d : ℕ) (hd : d ∈ n.divisors) :
      ZMod.dft (fun k : ZMod n => if n.gcd k.val = d then (1 : ℂ) else 0) j =
        ramanujanSum (n/d) j.val := by
    simpa [apply_ite] using D5.S3.Arith.RoldanCirculantEnergyP2Q3.gcdRow_dft_ramanujan n {d} (Finset.singleton_subset_iff.mpr hd) j
  have hg : (fun k : ZMod n => (n.gcd k.val : ℂ)) =
      ∑ d ∈ n.divisors, (d : ℂ) • (fun k : ZMod n => if n.gcd k.val = d then (1 : ℂ) else 0) := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [Nat.mem_divisors, Nat.gcd_dvd_left, NeZero.ne n]
  rw [hg, map_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hh d hd]

private def divCount (p a j : ℕ) : ℕ :=
  ((range a).filter (fun r => p ^ r ∣ j)).card

private def localSpectrum (p a j : ℕ) : ℂ :=
  ∑ r ∈ range (a+1), (p : ℂ) ^ (a-r) * ramanujanSum (p ^ r) j

private theorem divCount_succ (p a j : ℕ) :
    divCount p (a+1) j = divCount p a j + if p^a ∣ j then 1 else 0 := by
  classical
  unfold divCount
  rw [range_add_one, filter_insert]
  by_cases h : p^a ∣ j
  · simp [h, mem_filter]
  · simp [h]

private theorem localSpectrum_succ (p a j : ℕ) :
    localSpectrum p (a+1) j = (p : ℂ) * localSpectrum p a j + ramanujanSum (p^(a+1)) j := by
  classical
  unfold localSpectrum
  rw [sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul, mul_sum]
  congr 1
  apply sum_congr rfl
  intro r hr
  have he : a + 1 - r = a - r + 1 := by
    exact Nat.sub_add_comm (Nat.le_of_lt_succ (mem_range.mp hr))
  rw [he, pow_succ']
  ring

private theorem localSpectrum_formula (p a j : ℕ) (hp : Nat.Prime p) :
    localSpectrum p (a+1) j = (p : ℂ)^a *
      (((p-1 : ℕ) : ℂ) * divCount p (a+1) j +
        (p : ℂ) * if p^(a+1) ∣ j then 1 else 0) := by
  classical
  have hps : ((p-1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
    simp only [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  induction a
  case zero =>
      rw [localSpectrum_succ, D5.S3.Arith.RoldanCirculantEnergyP2Q3.ramanujan_prime_power p j 0 hp]
      simp [localSpectrum, divCount, D5.S3.Arith.RoldanCirculantEnergyP2Q3.ramanujan_one, hps, Finset.filter_singleton] <;> ring
  case succ a ih =>
      rw [localSpectrum_succ, ih, D5.S3.Arith.RoldanCirculantEnergyP2Q3.ramanujan_prime_power p j (a+1) hp, divCount_succ p (a+1) j]
      push_cast
      rw [hps, pow_succ]
      split_ifs <;> ring

private theorem gcd_dft_prime_power (p a : ℕ) (hp : Nat.Prime p) (j : ZMod (p^a))
    [NeZero (p^a)] :
    ZMod.dft (fun k : ZMod (p^a) => (Nat.gcd (p^a) k.val : ℂ)) j = localSpectrum p a j.val := by
  rw [gcd_dft, Nat.sum_divisors_prime_pow hp]
  unfold localSpectrum
  have hd (r : ℕ) (hr : r < a+1) : p^a / p^r = p^(a-r) :=
    Nat.pow_div (by omega) hp.pos
  simp_rw [Nat.cast_pow]
  have he : (∑ r ∈ range (a+1), (p : ℂ)^r * ramanujanSum (p^a / p^r) j.val) =
      ∑ r ∈ range (a+1), (p : ℂ)^r * ramanujanSum (p^(a-r)) j.val := by
    apply sum_congr rfl
    intro r hr
    rw [hd r (mem_range.mp hr)]
  rw [he, ← sum_range_reflect]
  apply sum_congr rfl
  intro r hr
  have hr' : r < a+1 := mem_range.mp hr
  congr 2
  all_goals congr 1 <;> omega

private theorem det_circulant (n : ℕ) [NeZero n] (b : ZMod n → ℂ) :
    (Matrix.circulant b).det = ∏ j : ZMod n, ZMod.dft b j := by
  have hh := congrArg (Polynomial.eval 0)
    (D5.S3.Quantum.Matrix.CirculantCharpoly.circulant_charpoly n b)
  rw [Matrix.eval_charpoly, Polynomial.eval_prod] at hh
  simp only [map_zero, zero_sub, Matrix.det_neg, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_neg, Finset.card_univ] at hh
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) hh

end
end D5.S3.Arith.Divisors.SunA228884

namespace D5.S3.Arith.Divisors.SunA228884
noncomputable section
open scoped BigOperators
open Finset

private theorem D_spectral (n : ℕ) [NeZero n] :
    (D n : ℂ) = ∏ j : ZMod n,
      ZMod.dft (fun k : ZMod n => (Nat.gcd n k.val : ℂ)) j := by
  rw [D_eq_det_K]
  have hm : (K n).map (Int.castRingHom ℂ) =
      Matrix.circulant (fun k : ZMod n => (Nat.gcd n k.val : ℂ)) := by
    ext i j
    simp [K, Nat.gcd_comm]
  change Int.castRingHom ℂ ((K n).det) = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, det_circulant]

private def E (p a j : ℕ) : ℕ :=
  p^a * ((p-1) * divCount p (a+1) j + p * (if p^(a+1) ∣ j then 1 else 0))

private theorem D_prime_power (p a : ℕ) (hp : Nat.Prime p) [NeZero (p^(a+1))] :
    D (p^(a+1)) = ∏ j : ZMod (p^(a+1)), (E p a j.val : ℤ) := by
  classical
  haveI : NeZero (p^(a+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_prod, D_spectral]
  apply prod_congr rfl
  intro j _
  rw [gcd_dft_prime_power p (a+1) hp j, localSpectrum_formula p a j.val hp]
  simp only [E, Int.cast_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
  split_ifs <;> push_cast <;> ring

private theorem divCount_bounds (p a j : ℕ) (ha : 0 < a) :
    1 ≤ divCount p a j ∧ divCount p a j ≤ a := by
  classical
  constructor
  · apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    exact ⟨0, by simp [ha]⟩
  · simpa [divCount] using Finset.card_filter_le (range a) (fun r => p^r ∣ j)

private theorem E_zero (p a : ℕ) (hp : Nat.Prime p) :
    E p a 0 = p^a * B p (a+1) := by
  simp only [E, divCount, dvd_zero, filter_true, card_range, ite_true, mul_one]
  unfold B
  have hs : p-1+1 = p := Nat.sub_add_cancel hp.one_lt.le
  congr 1
  nth_rw 2 [← hs]
  ring

private theorem E_one_exponent_support (p j q : ℕ) (hp : Nat.Prime p)
    (hd : q ∣ E p 0 j) : q < 2*p := by
  have hE : E p 0 j = if p ∣ j then 2*p-1 else p-1 := by
    unfold E divCount
    simp only [pow_zero, zero_add, one_mul, range_one, filter_singleton, pow_one,
      one_dvd, ite_true, card_singleton, mul_one]
    split_ifs <;> omega
  have hpos : 0 < E p 0 j := by rw [hE]; split_ifs <;> have := hp.two_le <;> omega
  have hle : E p 0 j < 2*p := by rw [hE]; split_ifs <;> have := hp.two_le <;> omega
  exact (Nat.le_of_dvd hpos hd).trans_lt hle

private theorem E_higher_support (p a q : ℕ) (hp : Nat.Prime p) (ha : 1 ≤ a)
    (j : ZMod (p^(a+1))) (hq : Nat.Prime q) (hd : q ∣ E p a j.val) : q < p^(a+1) := by
  haveI : NeZero (p^(a+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_cases hj : j = 0
  · rw [hj, ZMod.val_zero, E_zero p a hp] at hd
    apply prime_dvd_zero_eigen_lt p (a+1) q hp (by omega) hq
    simpa using hd
  · have hval : 0 < j.val := Nat.pos_of_ne_zero (by simpa using hj)
    have hnd : ¬ p^(a+1) ∣ j.val :=
      Nat.not_dvd_of_pos_of_lt hval (ZMod.val_lt j)
    have hc := divCount_bounds p (a+1) j.val (by omega)
    have hs : divCount p (a+1) j.val - 1 < a+1 := by
      exact Nat.sub_lt_right_of_lt_add hc.1 (Nat.lt_succ_of_le hc.2)
    apply prime_dvd_nonzero_eigen_lt p (a+1) (divCount p (a+1) j.val-1) q
      hp (by omega) hs hq
    simpa [E, hnd, Nat.sub_add_cancel hc.1, mul_comm, mul_left_comm, mul_assoc] using hd

private theorem prime_power_support (p a q : ℕ) (hp : Nat.Prime p) (ha : 0 < a)
    (hq : Nat.Prime q) (hd : (q : ℤ) ∣ D (p^a)) :
    q < 2*p^a ∧ (2 ≤ a → q < p^a) := by
  classical
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  haveI : NeZero (p^(b+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [D_prime_power p b hp] at hd
  have hqi : Prime (q : ℤ) := Int.prime_ofNat_iff.mpr hq
  obtain ⟨j, _, hj⟩ := (hqi.dvd_finsetProd_iff _).mp hd
  have hdj : q ∣ E p b j.val := Int.natCast_dvd_natCast.mp hj
  by_cases hb : b = 0
  · subst b
    simp only [zero_add, pow_one]
    exact ⟨E_one_exponent_support p j.val q hp hdj, by omega⟩
  · have hlt := E_higher_support p b q hp (by omega) j hq hdj
    constructor
    · change q < 2 * p^(b+1)
      omega
    · intro _; exact hlt

private theorem all_support (n : ℕ) (hn : 0 < n) (q : ℕ) (hq : Nat.Prime q)
    (hd : (q : ℤ) ∣ D n) : q < 2*n ∧ (¬Nat.Prime n → q < n) := by
  revert hn q hq hd
  induction n using Nat.recOnPosPrimePosCoprime
  case prime_pow p a hp ha =>
      intro hn q hq hd
      have h := prime_power_support p a q hp ha hq hd
      refine ⟨h.1, ?_⟩
      intro hnp
      have ha2 : 2 ≤ a := by
        by_contra! hsmall
        have he : a = 1 := by
          exact Nat.eq_of_le_of_lt_succ ha hsmall
        simp [he, hp] at hnp
      exact h.2 ha2
  case zero => intro hn; omega
  case one =>
      intro hn q hq hd
      have hd1 : (q : ℤ) ∣ 1 := by simpa [D, C] using hd
      exact ((Int.prime_ofNat_iff.mpr hq).not_dvd_one hd1).elim
  case coprime u v hu hv hcop ihU ihV =>
      intro hn q hq hd
      rw [D_coprime u v (by omega) (by omega) hcop] at hd
      have hqi : Prime (q : ℤ) := Int.prime_ofNat_iff.mpr hq
      have hlt : q < u*v := by
        rcases hqi.dvd_mul.mp hd with hd | hd
        · have hU := (ihU (by omega) q hq (hqi.dvd_of_dvd_pow hd)).1
          have hmul : 2*u ≤ u*v := by
            simpa [mul_comm] using Nat.mul_le_mul_left u (show 2 ≤ v by omega)
          exact hU.trans_le hmul
        · have hV := (ihV (by omega) q hq (hqi.dvd_of_dvd_pow hd)).1
          have hmul : 2*v ≤ u*v := by
            simpa [mul_comm] using Nat.mul_le_mul_right v (show 2 ≤ u by omega)
          exact hV.trans_le hmul
      exact ⟨by omega, fun _ => hlt⟩

theorem result : claim := by
  intro n hn hnp q hq hd
  exact (all_support n (by omega) q hq hd).2 hnp

end
end D5.S3.Arith.Divisors.SunA228884
