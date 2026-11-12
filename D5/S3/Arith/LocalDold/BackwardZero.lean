/- GID: D5/S3/Arith/LocalDold/BackwardZero
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/BackwardZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strictly negative backward zero excludes fixed positive local Dold repairs. -/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Finset.NatDivisors
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.SModEq.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.LocalDold.BackwardZero

open scoped ArithmeticFunction.Moebius
noncomputable section

/-- The integral Möbius transform on positive divisors. -/
def mobiusSum (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, μ (n / d) * u d

/-- All Dold congruences, with no sign or orbit-count hypothesis. -/
def Dold (u : ℕ → ℤ) : Prop := ∀ n : ℕ, 0 < n → (n : ℤ) ∣ mobiusSum u n

/-- The local part uses the valuation of the absolute value. -/
def localPart (p : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (p : ℤ) ^ padicValInt p (a n)

private theorem mobius_inversion (u : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, mobiusSum u d = u n := by
  apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr ?_ n hn
  intro k hk
  simp only [mobiusSum]
  simpa only [Int.cast_id] using (Nat.sum_divisorsAntidiagonal' (f := fun a b => μ a * u b) (n := k))

private theorem divisor_sum_mul_prime (f : ℕ → ℤ) {m q : ℕ}
    (hc : m.Coprime q) (hq : q.Prime) :
    ∑ d ∈ (m*q).divisors, f d = ∑ d ∈ m.divisors, (f d + f (d*q)) := by
  rw [hc.divisors_mul]
  simp only [Finset.sum_map]
  change (∑ z ∈ (m.divisors ×ˢ q.divisors).attach, f (z.val.1*z.val.2)) = _
  rw [Finset.sum_attach (m.divisors ×ˢ q.divisors) (fun z : ℕ × ℕ => f (z.1*z.2)), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  rw [show q = q^1 by simp, Nat.divisors_prime_pow hq 1]
  simp [Finset.sum_range_succ]

/-- The prime-direction congruence follows from the full Möbius divisibilities. -/
theorem dold_prime_congruence {u : ℕ → ℤ} (hu : Dold u)
    {m q : ℕ} (hm : 0 < m) (hq : q.Prime) (hc : m.Coprime q) :
    (q : ℤ) ∣ u (m*q) - u m := by
  rw [← mobius_inversion u (m*q) (Nat.mul_pos hm hq.pos),
    ← mobius_inversion u m hm, divisor_sum_mul_prime _ hc hq,
    Finset.sum_add_distrib, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  exact dvd_trans (by exact_mod_cast (dvd_mul_left q d))
    (hu (d*q) (Nat.mul_pos hdpos hq.pos))

private theorem valuation_eq_of_modEq {p K : ℕ} [Fact p.Prime] {x y : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (he : padicValInt p y < K)
    (h : x ≡ y [ZMOD ((p : ℤ)^K)]) : padicValInt p x = padicValInt p y := by
  have hediv : (p : ℤ) ^ padicValInt p y ∣ x :=
    (Int.ModEq.dvd_iff (h.of_dvd (pow_dvd_pow _ (Nat.le_of_lt he)))).mpr
      (padicValInt_dvd y)
  have hle : padicValInt p y ≤ padicValInt p x :=
    ((padicValInt_dvd_iff _ _).mp hediv).resolve_left hx
  have hnext : ¬ (p : ℤ) ^ (padicValInt p y + 1) ∣ x := by
    intro hd
    have hd' := (Int.ModEq.dvd_iff (h.of_dvd
      (pow_dvd_pow (p : ℤ) (by omega : padicValInt p y + 1 ≤ K)))).mp hd
    have := ((padicValInt_dvd_iff _ _).mp hd').resolve_left hy
    omega
  have hnle : ¬ padicValInt p y + 1 ≤ padicValInt p x := by
    intro he'
    exact hnext ((padicValInt_dvd_iff _ _).mpr (Or.inr he'))
  omega

private theorem period_multiple {a : ℕ → ℤ} {M K r : ℕ} (hr : 0 < r)
    (hstep : ∀ n, 0 < n → a (n+M) ≡ a n [ZMOD (K : ℤ)]) (k : ℕ) :
    a (r+k*M) ≡ a r [ZMOD (K : ℤ)] := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hstep (r+k*M) (by omega)
      rw [show r+(k+1)*M = (r+k*M)+M by ring]
      exact hs.trans ih

/-- A unit-index valuation mismatch contradicts every fixed positive Dold repair.
The proof derives the prime-direction congruence from the full Möbius transform
and uses Dirichlet's theorem to hold the nonzero difference fixed. -/
theorem no_repair_of_unit_mismatch (a : ℕ → ℤ) (p L m r : ℕ)
    (hp : p.Prime) (hL : 0 < L) (hm : 0 < m) (hr : 0 < r)
    (ha : ∀ n, 0 < n → a n ≠ 0)
    (hperiod : ∀ j n, 0 < n → a (n+L*p^j) ≡ a n [ZMOD ((p : ℤ)^(j+1))])
    (hcop : r.Coprime (p*L))
    (hne : padicValInt p (a (m*r)) ≠ padicValInt p (a m)) :
    ∀ c : ℕ, 0 < c → ¬ Dold (fun n => (c : ℤ)*localPart p a n) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro c hc hD
  let e := padicValInt p (a (m*r))
  let M := L*p^e
  let delta : ℤ := (c : ℤ) * (localPart p a (m*r) - localPart p a m)
  have hdelta : delta ≠ 0 := by
    apply mul_ne_zero (by exact_mod_cast hc.ne')
    apply sub_ne_zero.mpr
    exact fun h => hne ((pow_right_injective₀ (by exact_mod_cast hp.pos : (0:ℤ) < p) (by exact_mod_cast hp.ne_one : (p:ℤ) ≠ 1)) h)
  have hrM : r.Coprime M := by
    exact hcop.symm.coprime_mul_left.symm.mul_right (hcop.symm.coprime_mul_right.symm.pow_right e)
  obtain ⟨q, hqbound, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max r (max m delta.natAbs)) (q := M) (a := r) (Nat.mul_ne_zero hL.ne' (pow_ne_zero _ hp.ne_zero)) hrM
  have hqr : r ≤ q := by omega
  obtain ⟨k, hk⟩ : ∃ k, q = r+k*M := by
    obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hqr).mp hqmod.symm
    exact ⟨k,(Nat.eq_add_of_sub_eq hqr hk).trans (by ac_rfl)⟩
  have hclass : a (m*q) ≡ a (m*r) [ZMOD ((p : ℤ)^(e+1))] := by
    rw [hk, show m*(r+k*M) = m*r+(m*k)*M by ring]
    simpa [M, Nat.cast_pow] using period_multiple (Nat.mul_pos hm hr)
      (fun n hn => hperiod e n hn) (m*k)
  have hval : padicValInt p (a (m*q)) = e :=
    valuation_eq_of_modEq (ha _ (Nat.mul_pos hm hq.pos))
      (ha _ (Nat.mul_pos hm hr)) (by dsimp [e]; omega) hclass
  have heq : localPart p a (m*q) = localPart p a (m*r) := by
    simp only [localPart, hval]; rfl
  have hmc : m.Coprime q := by
    exact (hq.coprime_iff_not_dvd.mpr (fun h =>
      (not_le_of_gt (show m < q by omega)) (Nat.le_of_dvd hm h))).symm
  have hd := dold_prime_congruence hD hm hq hmc
  change (q : ℤ) ∣ (c : ℤ)*localPart p a (m*q) - (c : ℤ)*localPart p a m at hd
  rw [heq, ← mul_sub] at hd
  have hdn : q ∣ delta.natAbs := by exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hd)
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hdelta) hdn
  omega

/-- An integral scalar observation of a matrix orbit. -/
def observation {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (x l : Fin d → ℤ) (n : ℕ) : ℤ := dotProduct l ((A^n).mulVec x)

private theorem observation_congr {d K : ℕ} {X Y : Matrix (Fin d) (Fin d) ℤ}
    (h : ∀ i j, (K : ℤ) ∣ X i j - Y i j) (x l : Fin d → ℤ) :
    dotProduct l (X.mulVec x) ≡ dotProduct l (Y.mulVec x) [ZMOD (K : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  have hv : ∀ i, (K : ℤ) ∣ (Y.mulVec x) i - (X.mulVec x) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul]
    apply Finset.dvd_sum
    intro j hj
    simpa only [neg_sub] using dvd_mul_of_dvd_left (dvd_neg.mpr (h i j)) (x j)
  simp only [dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
  exact Finset.dvd_sum (fun i hi => dvd_mul_of_dvd_right (hv i) _)

private theorem exists_matrix_period {d p : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ A.det) :
    ∃ L, 0 < L ∧ ∃ C, A^L = 1+(p : ℤ) • C := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let B := A.map (Int.castRingHom (ZMod p))
  have hbdet : B.det ≠ 0 := by
    change (A.map (Int.castRingHom (ZMod p))).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  obtain ⟨U,hU⟩ := ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hbdet))
  obtain ⟨L,hL,hpow⟩ := (isOfFinOrder_of_finite U).exists_pow_eq_one
  have hB : B^L = 1 := by
    have := congrArg Units.val hpow
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hU] using this
  have hentry : ∀ i j, (p : ℤ) ∣ (A^L) i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j := by
    intro i j
    have he := congrArg (fun X : Matrix (Fin d) (Fin d) (ZMod p) => X i j) hB
    change ((A.map (Int.castRingHom (ZMod p)))^L) i j = (1 : Matrix (Fin d) (Fin d) (ZMod p)) i j at he
    rw [← Matrix.map_pow A (Int.castRingHom (ZMod p)) L] at he
    have he' : (((A^L) i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j : ℤ) : ZMod p) = 0 := by
      simpa [Matrix.map_apply, Matrix.one_apply, sub_eq_zero] using he
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he'
  choose C hC using hentry
  refine ⟨L,hL,C,?_⟩
  ext i j
  have := hC i j
  change (A^L) i j = (1 : Matrix (Fin d) (Fin d) ℤ) i j + (p : ℤ)*C i j
  linarith

private theorem matrix_lift {d p L : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hbase : ∃ C, A^L = 1+(p : ℤ) • C) (j : ℕ) :
    ∃ C, A^(L*p^j) = 1+(p : ℤ)^(j+1) • C := by
  obtain ⟨C,hC⟩ := hbase
  let I : Ideal (Polynomial ℤ) := Ideal.span {(p : Polynomial ℤ)}
  have hpI : (p : Polynomial ℤ) ∈ I := Ideal.mem_span_singleton_self _
  have hx : (1+(p : Polynomial ℤ)*Polynomial.X) ≡ 1 [SMOD I] := by
    apply SModEq.sub_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨Polynomial.X,by ring⟩
  have hs := SModEq.pow_pow_add_one hpI hx j
  rw [SModEq.sub_mem, one_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hs
  obtain ⟨Q,hQ⟩ := hs
  refine ⟨Polynomial.aeval C Q,?_⟩
  have hpoly : (1+(p : Polynomial ℤ)*Polynomial.X)^(p^j) =
      1+(p : Polynomial ℤ)^(j+1)*Q := by rw [← hQ]; ring
  have hm := congrArg (Polynomial.aeval C) hpoly
  simp only [map_pow,map_add,map_one,map_mul,map_natCast,Polynomial.aeval_X] at hm
  rw [pow_mul,hC]
  simpa only [← Nat.cast_pow,Nat.cast_smul_eq_nsmul,nsmul_eq_mul] using hm

private theorem matrix_period {d p L : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (x l : Fin d → ℤ) (hbase : ∃ C, A^L = 1+(p : ℤ) • C) :
    ∀ j n, observation A x l (n+L*p^j) ≡ observation A x l n
      [ZMOD ((p : ℤ)^(j+1))] := by
  intro j n
  obtain ⟨C,hC⟩ := matrix_lift A hbase j
  unfold observation
  apply observation_congr (K := p^(j+1))
  intro i k
  have he : A^(n+L*p^j) = A^n+(p : ℤ)^(j+1) • (A^n*C) := by
    rw [pow_add,hC,Matrix.mul_add,Matrix.mul_one,Matrix.mul_smul]
  rw [he]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_sub_cancel_left,Nat.cast_pow]
  exact dvd_mul_right _ _

/-- Starting a nonvanishing forward orbit a positive number of steps after a
zero observation excludes every positive multiplier at every locally
invertible prime. The zero observation is actual matrix data. -/
theorem kernel_orbit_no_repair {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (y l : Fin d → ℤ) (h : ℕ) (hh : 0 < h)
    (hzero : dotProduct l y = 0) (p : ℕ) (hp : p.Prime)
    (hdet : ¬ (p : ℤ) ∣ A.det)
    (ha : ∀ n, 0 < n → observation A y l (n+h) ≠ 0) :
    ∀ c : ℕ, 0 < c →
      ¬ Dold (fun n => (c : ℤ)*localPart p (fun n => observation A y l (n+h)) n) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L,hL,hbase⟩ := exists_matrix_period A hp hdet
  let a := fun n => observation A y l (n+h)
  let t := padicValInt p (a h)
  let M := L*p^(t+1)
  let r := M-1
  have hM : 1 < M := by
    have hpow : 1 < p^(t+1) := Nat.one_lt_pow (by omega) hp.one_lt
    have := Nat.mul_le_mul_right (p^(t+1)) (show 1 ≤ L by omega)
    dsimp [M]; omega
  have hr : 0 < r := by dsimp [r]; omega
  have hrM : r+1 = M := by dsimp [r]; omega
  have hcopM : r.Coprime M := by
    rw [← hrM]
    simpa [Nat.add_comm] using (Nat.coprime_add_self_right (m := r) (n := 1)).mpr (Nat.coprime_one_right r)
  have hcop : r.Coprime (p*L) := by
    apply hcopM.of_dvd_right
    refine ⟨p^t,?_⟩
    dsimp [M]; rw [pow_succ]; ring
  have hmultiple : ∀ k : ℕ, observation A y l (k*M) ≡ 0
      [ZMOD ((p : ℤ)^(t+2))] := by
    intro k
    induction k with
    | zero => simp [observation,hzero]
    | succ k ih =>
      have hs := matrix_period A y l hbase (t+1) (k*M)
      have he : (k+1)*M = k*M+L*p^(t+1) := by dsimp [M]; ring
      rw [he]
      exact hs.trans ih
  have hdiv : (p : ℤ)^(t+2) ∣ a (h*r) := by
    have hs := hmultiple h
    have he : h*r+h = h*M := by nlinarith [hrM]
    change (p : ℤ)^(t+2) ∣ observation A y l (h*r+h)
    rw [he]
    simpa using hs.symm.dvd
  have hval : t+2 ≤ padicValInt p (a (h*r)) :=
    ((padicValInt_dvd_iff _ _).mp hdiv).resolve_left (ha _ (Nat.mul_pos hh hr))
  apply no_repair_of_unit_mismatch a p L h r hp hL hh hr ha
  · intro j n hn
    have hs := matrix_period A y l hbase j (n+h)
    simpa only [a,show n+L*p^j+h = (n+h)+L*p^j by omega] using hs
  · exact hcop
  · dsimp [t] at hval; omega

private theorem dold_congr {u v : ℕ → ℤ} (he : ∀ n, 0 < n → u n = v n) :
    Dold u ↔ Dold v := by
  have hs : ∀ n, mobiusSum u n = mobiusSum v n := by
    intro n
    apply Finset.sum_congr rfl
    intro d hd
    rw [he d (Nat.pos_of_mem_divisors hd)]
  simp only [Dold,hs]

private theorem adjugate_power {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (h : ℕ) :
    A^h * A.adjugate^h = A.det^h • (1 : Matrix (Fin d) (Fin d) ℤ) := by
  have hc : Commute A A.adjugate := by
    show A*A.adjugate = A.adjugate*A
    rw [Matrix.mul_adjugate,Matrix.adjugate_mul]
  rw [← hc.mul_pow,Matrix.mul_adjugate,smul_pow,one_pow]

/-- Clearing the rational backward denominator gives an integral kernel vector. -/
theorem adjugate_zero_of_backward_zero {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℤ) (x l : Fin d → ℤ) (h : ℕ)
    (hdet : A.det ≠ 0)
    (hzero : dotProduct (fun i => (l i : ℚ))
      ((((A.map (Int.castRingHom ℚ))⁻¹)^h).mulVec (fun i => (x i : ℚ))) = 0) :
    dotProduct l ((A.adjugate^h).mulVec x) = 0 := by
  let f := Int.castRingHom ℚ
  have hdetQ : (A.map f).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    simpa [f] using (Int.cast_ne_zero.mpr hdet : (A.det : ℚ) ≠ 0)
  have he : (A.map f)⁻¹^h = ((A.map f).det⁻¹)^h • (A.adjugate^h).map f := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv,smul_pow]
    congr 1
    rw [← RingHom.mapMatrix_apply,← RingHom.map_adjugate,RingHom.mapMatrix_apply,
      Matrix.map_pow]
  rw [he,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] at hzero
  have hz := (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (inv_ne_zero hdetQ))
  have hmap : ((dotProduct l ((A.adjugate^h).mulVec x) : ℤ) : ℚ) =
      dotProduct (fun i => (l i : ℚ))
        (((A.adjugate^h).map f).mulVec (fun i => (x i : ℚ))) := by
    simp [dotProduct,Matrix.mulVec,f]
  exact_mod_cast (hmap.trans hz)

/-- General backward-zero obstruction for an integer matrix. The backwards
power is taken over the rationals; forward observations may have either sign. -/
theorem matrix_backward_zero_no_repair {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℤ) (x l : Fin d → ℤ) (h : ℕ) (hh : 0 < h)
    (hzero : dotProduct (fun i => (l i : ℚ))
      ((((A.map (Int.castRingHom ℚ))⁻¹)^h).mulVec (fun i => (x i : ℚ))) = 0)
    (ha : ∀ n, 0 < n → observation A x l n ≠ 0)
    (p : ℕ) (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ A.det) :
    ∀ s c : ℕ, 0 < c → ¬ Dold (fun n => (c : ℤ)*localPart p (observation A x l) (n+s)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdet0 : A.det ≠ 0 := fun hz => hdet (hz ▸ dvd_zero _)
  let y := (A.adjugate^h).mulVec x
  have hz : dotProduct l y = 0 := adjugate_zero_of_backward_zero A x l h hdet0 hzero
  have hscale : ∀ n, observation A y l (n+h) = A.det^h * observation A x l n := by
    intro n
    dsimp [observation,y]
    rw [pow_add,Matrix.mulVec_mulVec,Matrix.mul_assoc,adjugate_power,
      Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  intro s
  have hnscale : ∀ n, 0 < n → observation A y l (n+(h+s)) ≠ 0 := by
    intro n hn
    rw [show n+(h+s) = (n+s)+h by omega,hscale]
    exact mul_ne_zero (pow_ne_zero _ hdet0) (ha (n+s) (by omega))
  have hval : ∀ n, 0 < n →
      localPart p (fun n => observation A y l (n+(h+s))) n = localPart p (observation A x l) (n+s) := by
    intro n hn
    dsimp only [localPart]
    rw [show n+(h+s) = (n+s)+h by omega,hscale,padicValInt.mul (pow_ne_zero _ hdet0) (ha (n+s) (by omega))]
    have hunit : ¬ (p : ℤ) ∣ A.det^h := fun hd =>
      hdet ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hd)
    rw [padicValInt.eq_zero_of_not_dvd hunit,zero_add]
  intro c hc hD
  apply kernel_orbit_no_repair A y l (h+s) (by omega) hz p hp hdet hnscale c hc
  exact (dold_congr (fun n hn => congrArg ((c : ℤ)*·) (hval n hn))).mpr hD

end
end D5.S3.Arith.LocalDold.BackwardZero
