/- GID: D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The Baker pair over coefficientwise nonnegative polynomials admits no exchange chain. -/

import D5.S0.Tower.DBonacci.Irreducibility
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Baker polynomial obstruction

The fixed pair in Jeandel's archived draft question admits no coupled lag
witnesses over Polynomial Nat, and hence no finite rectangular exchange chain.
The source question is after the end of the rendered arXiv:2609.03567v1 document.
Four-slot escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/25126.
The proof reuses the order-two multinacci irreducibility theorem, the negated-X
automorphism, prime-power divisors, and the existing exchange-chain lag theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.BakerPolynomialObstruction

open Polynomial
open scoped Matrix
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

def A : Matrix (Fin 2) (Fin 2) ℕ[X] := !![1, X + 1; X, 1]

def B : Matrix (Fin 2) (Fin 2) ℕ[X] := !![1, X ^ 2 + X; 1, 1]

private def rForm (a c : ℕ[X]) : Matrix (Fin 2) (Fin 2) ℕ[X] :=
  !![a, (X + 1) * c; c, X * a]

private def sForm (h g : ℕ[X]) : Matrix (Fin 2) (Fin 2) ℕ[X] :=
  !![X * h, (X + 1) * g; g, h]

private theorem add_left_cancel_nat {p q r : ℕ[X]} (h : p + q = p + r) : q = r := by
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun f : ℕ[X] => f.coeff n) h
  simp only [coeff_add] at hc
  exact Nat.add_left_cancel hc

private theorem r_form (R : Matrix (Fin 2) (Fin 2) ℕ[X])
    (hR : A * R = R * B) : R = rForm (R 0 0) (R 1 0) := by
  have hb : (X + 1) * R 1 0 = R 0 1 := by
    apply add_left_cancel_nat (p := R 0 0)
    simpa [A, B, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => M 0 0) hR
  have h10 : X * R 0 0 + R 1 0 = R 1 0 + R 1 1 := by
    simpa [A, B, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => M 1 0) hR
  have hd : X * R 0 0 = R 1 1 :=
    add_left_cancel_nat ((add_comm _ _).trans h10)
  funext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [rForm] using hb.symm
  · rfl
  · simpa [rForm] using hd.symm

private theorem s_form (S : Matrix (Fin 2) (Fin 2) ℕ[X])
    (hS : B * S = S * A) : S = sForm (S 1 1) (S 1 0) := by
  have h10 : S 0 0 + S 1 0 = S 1 0 + X * S 1 1 := by
    simpa [A, B, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => M 1 0) hS
  have he : S 0 0 = X * S 1 1 :=
    add_left_cancel_nat ((add_comm _ _).trans h10)
  have hf : S 0 1 = (X + 1) * S 1 0 := by
    apply add_left_cancel_nat (p := S 1 1)
    simpa [A, B, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => M 1 1) hS
  funext i j
  fin_cases i <;> fin_cases j
  · simpa [sForm] using he
  · simpa [sForm] using hf
  · rfl
  · rfl

/- Coefficientwise nonnegativity is used here, over Nat itself. In particular,
   equal leading degrees cannot cancel. These statements include zero inputs. -/
private theorem natDegree_add_nat (f g : ℕ[X]) :
    (f + g).natDegree = max f.natDegree g.natDegree := by
  have left_le (p q : ℕ[X]) : p.natDegree ≤ (p + q).natDegree := by
    by_cases hp : p = 0
    · simp only [hp, natDegree_zero]
      exact Nat.zero_le _
    · apply le_natDegree_of_ne_zero
      rw [coeff_add]
      have hc : p.coeff p.natDegree ≠ 0 := by
        simpa only [coeff_natDegree, leadingCoeff_ne_zero] using hp
      omega
  exact le_antisymm (natDegree_add_le f g)
    (max_le (left_le f g) (by simpa only [add_comm] using left_le g f))

private theorem add_ne_zero_nat (f g : ℕ[X]) (hf : f ≠ 0) : f + g ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℕ[X] => p.coeff f.natDegree) h
  simp only [coeff_add, coeff_zero] at hc
  have hfc : f.coeff f.natDegree ≠ 0 := by
    simpa only [coeff_natDegree, leadingCoeff_ne_zero] using hf
  omega

private theorem xadd1_ne_nat : (X + 1 : ℕ[X]) ≠ 0 := by
  simpa only [map_one] using (X_add_C_ne_zero (1 : ℕ))

private theorem xadd1_ne_rat : (X + 1 : ℚ[X]) ≠ 0 := by
  simpa only [map_one] using (X_add_C_ne_zero (1 : ℚ))

private abbrev toQ : ℕ[X] →+* ℚ[X] :=
  Polynomial.mapRingHom (Nat.castRingHom ℚ)

private abbrev matrixToQ :
    Matrix (Fin 2) (Fin 2) ℕ[X] →+* Matrix (Fin 2) (Fin 2) ℚ[X] :=
  toQ.mapMatrix

private theorem toQ_natDegree (f : ℕ[X]) : (toQ f).natDegree = f.natDegree := by
  change (f.map (Nat.castRingHom ℚ)).natDegree = f.natDegree
  exact natDegree_map_eq_of_injective (f := Nat.castRingHom ℚ) Nat.cast_injective f

private def detPolynomial : ℚ[X] := 1 - X - X ^ 2

private theorem detPolynomial_irreducible : Irreducible detPolynomial := by
  have hi : Irreducible (X ^ 2 - (1 + X) : ℚ[X]) := by
    simpa [Finset.sum_range_succ] using
      (D5.S0.Tower.DBonacci.PerronRoot.dbonacci_irreducible 2 (by norm_num)).2
  have hchange :
      Polynomial.algEquivAevalNegX (R := ℚ) (X ^ 2 - (1 + X)) =
        -detPolynomial := by
    change Polynomial.aeval (-X : ℚ[X]) (X ^ 2 - (1 + X)) = -detPolynomial
    simp [detPolynomial] <;> ring
  have himage : Irreducible (-detPolynomial) := by
    rw [← hchange]
    exact (MulEquiv.irreducible_iff (Polynomial.algEquivAevalNegX (R := ℚ))).mpr hi
  exact (irreducible_isUnit_mul (isUnit_neg_one : IsUnit (-1 : ℚ[X]))).mp
    (by simpa only [neg_one_mul] using himage)

private theorem detPolynomial_natDegree : detPolynomial.natDegree = 2 := by
  unfold detPolynomial
  compute_degree!

private theorem det_A : Matrix.det (matrixToQ A) = detPolynomial := by
  simp [Matrix.det_fin_two, matrixToQ, A, toQ, detPolynomial]
  <;> ring

private def normForm (f k : ℚ[X]) : ℚ[X] := X * f ^ 2 - (X + 1) * k ^ 2

private theorem det_rForm (a c : ℕ[X]) :
    Matrix.det (matrixToQ (rForm a c)) = normForm (toQ a) (toQ c) := by
  simp [Matrix.det_fin_two, matrixToQ, rForm, toQ, normForm]
  <;> ring

private theorem det_sForm (h g : ℕ[X]) :
    Matrix.det (matrixToQ (sForm h g)) = normForm (toQ h) (toQ g) := by
  simp [Matrix.det_fin_two, matrixToQ, sForm, toQ, normForm]
  <;> ring

private theorem prime_power_divisor_degree {f : ℚ[X]} {n : ℕ}
    (hf : f ∣ detPolynomial ^ n) : f ≠ 0 ∧ ∃ j : ℕ, f.natDegree = 2 * j := by
  have hp0 : detPolynomial ≠ 0 := detPolynomial_irreducible.ne_zero
  have hf0 : f ≠ 0 := by
    intro hz
    have : detPolynomial ^ n = 0 := by simpa only [hz, zero_dvd_iff] using hf
    exact pow_ne_zero n hp0 this
  obtain ⟨j, _, hj⟩ := (dvd_prime_pow detPolynomial_irreducible.prime n).mp hf
  have hd := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hj)
  rw [natDegree_pow, detPolynomial_natDegree] at hd
  exact ⟨hf0, j, by omega⟩

/- An even-degree nonzero norm has two nonzero inputs of the same degree.
   For unequal input degrees both summands have odd, unequal degrees. -/
private theorem normForm_even_degree (f k : ℚ[X]) (hn : normForm f k ≠ 0)
    (he : ∃ j : ℕ, (normForm f k).natDegree = 2 * j) :
    f ≠ 0 ∧ k ≠ 0 ∧ f.natDegree = k.natDegree := by
  obtain ⟨j, hj⟩ := he
  have hf : f ≠ 0 := by
    intro hz
    have hk : k ≠ 0 := by
      intro hk
      apply hn
      simp [normForm, hz, hk]
    have hd : (normForm f k).natDegree = 1 + 2 * k.natDegree := by
      simp only [normForm, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        zero_sub, natDegree_neg]
      rw [natDegree_mul xadd1_ne_rat (pow_ne_zero 2 hk), natDegree_pow]
      simp
    omega
  have hk : k ≠ 0 := by
    intro hz
    have hd : (normForm f k).natDegree = 1 + 2 * f.natDegree := by
      simp only [normForm, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        sub_zero]
      rw [natDegree_mul X_ne_zero (pow_ne_zero 2 hf), natDegree_pow, natDegree_X]
    omega
  refine ⟨hf, hk, ?_⟩
  have hdL : (X * f ^ 2).natDegree = 1 + 2 * f.natDegree := by
    rw [natDegree_mul X_ne_zero (pow_ne_zero 2 hf), natDegree_pow, natDegree_X]
  have hdR : ((X + 1) * k ^ 2).natDegree = 1 + 2 * k.natDegree := by
    rw [natDegree_mul xadd1_ne_rat (pow_ne_zero 2 hk), natDegree_pow]
    simp
  rcases lt_trichotomy f.natDegree k.natDegree with hlt | heq | hgt
  · have hd : (normForm f k).natDegree = 1 + 2 * k.natDegree := by
      unfold normForm
      rw [natDegree_sub_eq_right_of_natDegree_lt
        (p := X * f ^ 2) (q := (X + 1) * k ^ 2) (by omega), hdR]
    omega
  · exact heq
  · have hd : (normForm f k).natDegree = 1 + 2 * f.natDegree := by
      unfold normForm
      rw [natDegree_sub_eq_left_of_natDegree_lt
        (p := X * f ^ 2) (q := (X + 1) * k ^ 2) (by omega), hdL]
    omega

private theorem product_row_degrees (a c h g : ℕ[X])
    (ha : a ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0) (hg : g ≠ 0)
    (hac : a.natDegree = c.natDegree) (hhg : h.natDegree = g.natDegree) :
    ((rForm a c * sForm h g) 0 0).natDegree =
        ((rForm a c * sForm h g) 0 1).natDegree ∧
      (rForm a c * sForm h g) 0 1 ≠ 0 := by
  have h00 : (rForm a c * sForm h g) 0 0 =
      X * a * h + (X + 1) * c * g := by
    simp [rForm, sForm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h01 : (rForm a c * sForm h g) 0 1 =
      (X + 1) * (a * g + c * h) := by
    simp [rForm, sForm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hsum : a * g + c * h ≠ 0 := add_ne_zero_nat _ _ (mul_ne_zero ha hg)
  have hd00 : ((rForm a c * sForm h g) 0 0).natDegree =
      a.natDegree + h.natDegree + 1 := by
    rw [h00, natDegree_add_nat,
      natDegree_mul (mul_ne_zero X_ne_zero ha) hh,
      natDegree_mul (mul_ne_zero xadd1_ne_nat hc) hg,
      natDegree_mul X_ne_zero ha, natDegree_mul xadd1_ne_nat hc]
    simp only [natDegree_add_one, natDegree_X]
    omega
  have hd01 : ((rForm a c * sForm h g) 0 1).natDegree =
      a.natDegree + h.natDegree + 1 := by
    rw [h01, natDegree_mul xadd1_ne_nat hsum, natDegree_add_nat (a * g) (c * h),
      natDegree_mul ha hg, natDegree_mul hc hh]
    simp only [natDegree_add_one, natDegree_X]
    omega
  exact ⟨hd00.trans hd01.symm, by rw [h01]; exact mul_ne_zero xadd1_ne_nat hsum⟩

private def diagonal (n : ℕ) : ℕ[X] := (A ^ n) 0 0

private def upper (n : ℕ) : ℕ[X] := (A ^ n) 0 1

private theorem row_succ (n : ℕ) :
    diagonal (n + 1) = diagonal n + X * upper n ∧
      upper (n + 1) = (X + 1) * diagonal n + upper n := by
  constructor <;>
    simp [diagonal, upper, pow_succ, A, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/- This simultaneous recurrence keeps exactly the degree separation needed
   by the obstruction, without floor arithmetic or a binomial expansion. -/
private theorem power_row_degrees (n : ℕ) :
    diagonal (n + 1) ≠ 0 ∧ upper (n + 1) ≠ 0 ∧
      ((upper (n + 1)).natDegree = (diagonal (n + 1)).natDegree + 1 ∨
       (diagonal (n + 1)).natDegree = (upper (n + 1)).natDegree + 1) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, Or.inl ?_⟩
      · simp [diagonal, A]
      · simpa [upper, A] using xadd1_ne_nat
      · simp [diagonal, upper, A]
  | succ n ih =>
      obtain ⟨hd, hu, hdeg⟩ := ih
      have hrec := row_succ (n + 1)
      have hd' : diagonal (n + 1 + 1) ≠ 0 := by
        rw [hrec.1]
        exact add_ne_zero_nat _ _ hd
      have hu' : upper (n + 1 + 1) ≠ 0 := by
        rw [hrec.2]
        exact add_ne_zero_nat _ _ (mul_ne_zero xadd1_ne_nat hd)
      have hdd : (diagonal (n + 1 + 1)).natDegree =
          max (diagonal (n + 1)).natDegree (1 + (upper (n + 1)).natDegree) := by
        rw [hrec.1, natDegree_add_nat, natDegree_mul X_ne_zero hu, natDegree_X]
      have hud : (upper (n + 1 + 1)).natDegree =
          max (1 + (diagonal (n + 1)).natDegree) (upper (n + 1)).natDegree := by
        rw [hrec.2, natDegree_add_nat, natDegree_mul xadd1_ne_nat hd]
        simp
      refine ⟨hd', hu', ?_⟩
      rcases hdeg with hdeg | hdeg
      · right
        omega
      · left
        omega

/-- No lag, including lag zero, has the four coupled shift-equivalence witnesses
for Baker's pair over the coefficientwise nonnegative polynomial semiring. -/
theorem no_lag (n : ℕ) :
    ¬ ∃ R S : Matrix (Fin 2) (Fin 2) ℕ[X],
      A * R = R * B ∧ B * S = S * A ∧ R * S = A ^ n ∧ S * R = B ^ n := by
  rintro ⟨R, S, hR, hS, hRS, _hSR⟩
  let a := R 0 0
  let c := R 1 0
  let h := S 1 1
  let g := S 1 0
  have hRF : R = rForm a c := r_form R hR
  have hSF : S = sForm h g := s_form S hS
  rw [hRF, hSF] at hRS
  have hmap := congrArg matrixToQ hRS
  rw [map_mul, map_pow] at hmap
  have hdet := congrArg Matrix.det hmap
  rw [Matrix.det_mul, Matrix.det_pow, det_A, det_rForm, det_sForm] at hdet
  have hdivR : normForm (toQ a) (toQ c) ∣ detPolynomial ^ n :=
    ⟨normForm (toQ h) (toQ g), hdet.symm⟩
  have hdivS : normForm (toQ h) (toQ g) ∣ detPolynomial ^ n :=
    ⟨normForm (toQ a) (toQ c), by rw [mul_comm]; exact hdet.symm⟩
  have hr := prime_power_divisor_degree hdivR
  have hs := prime_power_divisor_degree hdivS
  have hr' := normForm_even_degree (toQ a) (toQ c) hr.1 hr.2
  have hs' := normForm_even_degree (toQ h) (toQ g) hs.1 hs.2
  have ha : a ≠ 0 := by
    intro hz
    apply hr'.1
    simp [hz]
  have hc : c ≠ 0 := by
    intro hz
    apply hr'.2.1
    simp [hz]
  have hh : h ≠ 0 := by
    intro hz
    apply hs'.1
    simp [hz]
  have hg : g ≠ 0 := by
    intro hz
    apply hs'.2.1
    simp [hz]
  have hac : a.natDegree = c.natDegree := by
    simpa only [toQ_natDegree] using hr'.2.2
  have hhg : h.natDegree = g.natDegree := by
    simpa only [toQ_natDegree] using hs'.2.2
  have hprod := product_row_degrees a c h g ha hc hh hg hac hhg
  cases n with
  | zero =>
      apply hprod.2
      simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => M 0 1) hRS
  | succ n =>
      have hd := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => (M 0 0).natDegree) hRS
      have hu := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℕ[X] => (M 0 1).natDegree) hRS
      have heq := hd.symm.trans (hprod.1.trans hu)
      change (diagonal (n + 1)).natDegree = (upper (n + 1)).natDegree at heq
      obtain ⟨_, _, hdeg⟩ := power_row_degrees n
      rcases hdeg with hdeg | hdeg <;> omega

/-- Every finite exchange chain is excluded, with no restriction on the
rectangular intermediate dimensions or on the chain length. -/
theorem no_exchange_chain (L : ℕ) : ¬ ExchangeChain ℕ[X] A B L := by
  intro chain
  exact no_lag L (exchange_chain_lag chain)

#print axioms no_lag
#print axioms no_exchange_chain

end D5.S3.ConceptDynamics.Coding.BakerPolynomialObstruction
