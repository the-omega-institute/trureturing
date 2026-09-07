/- GID: D5/S0/Certificates/ShankarQStieltjesRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/ShankarQStieltjesRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=gid:D5/S0/Certificates/ShankarQStieltjesRefutation.closed_form_not_stieltjes
   digest: An exact negative shifted moment form refutes the Shankar Q Stieltjes claim. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.ShankarQStieltjesRefutation

open MeasureTheory
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Integer lower indices implement the source's negative-index zero convention. -/
private def binom (m : Nat) (j : Int) : Int :=
  if j < 0 then 0 else (Nat.choose m j.toNat : Int)

private def ballotE (r b : Nat) : Int :=
  binom (r + b - 1) ((b : Int) - 1) - binom (r + b - 1) ((b : Int) - 2)

private def ballotH (k b c : Nat) : Int :=
  binom (2 * k - b - c) ((k : Int) - b) -
    binom (2 * k - b - c) ((k : Int) - b - 1)

/-- Theorem 7.1 of arXiv:2608.30002v2, explicitly as a closed form.
The paper's word-count identification is not formalized or assumed in Lean. -/
def closedFormQ (k : Nat) : Int :=
  if k = 0 then 1 else (catalan k : Int) +
    ∑ b ∈ Finset.Icc 1 (k - 1), ∑ c ∈ Finset.range (b + 1),
      ballotH k b c * ∑ r ∈ Finset.Icc b (k - 1),
        ballotE r b * binom (k - 1 - r + c) (c : Int)

/-- Exact coefficients in ascending polynomial degree. -/
def certificate : Fin 11 → Int := ![
  101118710150832431671196796252649512231806,
  -662677669268533938101716987475663620965666,
  1548486277071801438600832338542573144101640,
  -1800082554673557385076101398989780036003293,
  1196307300703816610151657807611194412954834,
  -487410702796750216586043273691945221737851,
  125698717484820716392581080465507901682426,
  -20562809439083017274073234871446233006372,
  2065883321354005872852404249559173330738,
  -116172686339782400824354774056669210149,
  2797672051379430758385367063062351871]

-- This vector is a proved evaluation cache, never the definition of Q.
private def checkedValues : Fin 24 → Int := ![
  1,1,5,33,234,1706,12618,94157,706878,5330403,
  40332881,306023196,2327290506,17734226120,135376087792,
  1035065812309,7925664456804,60771825678389,466587436417569,
  3586731522598141,27604168028694252,212685629040409758,
  1640473066548280308,12666272996480868428]

private theorem values_verified : ∀ n : Fin 24, closedFormQ n = checkedValues n := by
  unfold closedFormQ ballotH ballotE binom
  simp only [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose_eq_fast_choose]
  decide +kernel

/-- Kernel-checked evaluation of the source formula on the exact certificate. -/
theorem certificate_value :
    (∑ i : Fin 11, ∑ j : Fin 11,
      certificate i * certificate j * closedFormQ (i.val + j.val + 3)) =
      -7376954157543403276318358565675383034355744240767681002284188705571519096491185 := by
  have h (i j : Fin 11) :
      closedFormQ (i.val + j.val + 3) = checkedValues ⟨i.val + j.val + 3, by omega⟩ :=
    values_verified ⟨i.val + j.val + 3, by omega⟩
  simp_rw [h]
  decide +kernel

theorem certificate_negative :
    (∑ i : Fin 11, ∑ j : Fin 11,
      certificate i * certificate j * closedFormQ (i.val + j.val + 3)) < 0 := by
  rw [certificate_value]
  norm_num

private theorem polynomial_square_expansion (n s : Nat) (d : Fin n → Real) (t : Real) :
    t ^ s * (∑ i, d i * t ^ i.val) ^ 2 =
      ∑ i, ∑ j, d i * d j * t ^ (i.val + j.val + s) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pow_add]
  ring

/-- Finite moments justify integration of the polynomial square term by term. -/
theorem moment_quadratic_nonnegative
    (μ : Measure Real) (support : ∀ᵐ t ∂μ, 0 ≤ t)
    (moments : ∀ n : Nat, Integrable (fun t : Real => t ^ n) μ)
    (n s : Nat) (d : Fin n → Real) :
    0 ≤ ∑ i, ∑ j, d i * d j * (∫ t, t ^ (i.val + j.val + s) ∂μ) := by
  have hi (i j : Fin n) :
      Integrable (fun t : Real => d i * d j * t ^ (i.val + j.val + s)) μ :=
    (moments _).const_mul _
  have hsum :
      (∫ t, t ^ s * (∑ i, d i * t ^ i.val) ^ 2 ∂μ) =
        ∑ i, ∑ j, d i * d j * (∫ t, t ^ (i.val + j.val + s) ∂μ) := by
    simp_rw [polynomial_square_expansion]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    congr 1
    funext i
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    simp_rw [integral_const_mul]
  rw [← hsum]
  apply integral_nonneg_of_ae
  filter_upwards [support] with t ht
  exact mul_nonneg (pow_nonneg ht _) (sq_nonneg _)

/-- No positive Borel measure on the nonnegative half-line has these moments.
This settles the closed-form Q claim; the separate B conjecture is not addressed. -/
theorem closed_form_not_stieltjes :
    ¬ ∃ μ : Measure Real,
      (∀ᵐ t ∂μ, 0 ≤ t) ∧
      (∀ n : Nat, Integrable (fun t : Real => t ^ n) μ) ∧
      (∀ n : Nat, (∫ t, t ^ n ∂μ) = (closedFormQ n : Real)) := by
  rintro ⟨μ, hs, hm, hv⟩
  have hp := moment_quadratic_nonnegative μ hs hm 11 3 (fun i => (certificate i : Real))
  simp_rw [hv] at hp
  have hn : (∑ i : Fin 11, ∑ j : Fin 11,
      (certificate i : Real) * (certificate j : Real) *
        (closedFormQ (i.val + j.val + 3) : Real)) < 0 := by
    exact_mod_cast certificate_negative
  exact (not_lt_of_ge hp) hn

example : Nonempty (Measure Real) := ⟨Measure.dirac 1⟩
example : Nonempty Real := ⟨0⟩
example : Nonempty (Fin 11) := ⟨0⟩
example : ∃ μ : Measure Real,
    (∀ᵐ t ∂μ, 0 ≤ t) ∧
    (∀ n : Nat, Integrable (fun t : Real => t ^ n) μ) ∧
    (∀ n : Nat, (∫ t, t ^ n ∂μ) = 1) := by
  refine ⟨Measure.dirac 1, ?_, ?_, ?_⟩
  · simp [ae_dirac_eq]
  · intro n
    exact integrable_dirac (by simp)
  · intro n
    simp

example : closedFormQ 0 = 1 ∧ closedFormQ 1 = 1 := by decide +kernel
example (r : Nat) : ballotE r 1 = 1 := by simp [ballotE, binom]
example (k : Nat) :
    (catalan k : Real) = (Nat.choose (2 * k) k : Real) / (k + 1) := by
  apply (eq_div_iff (by positivity : (k : Real) + 1 ≠ 0)).mpr
  norm_cast
  simpa [mul_comm, Nat.centralBinom] using succ_mul_catalan_eq_centralBinom k

example (k b c r : Nat) (hk : 1 ≤ k)
    (hb : b ∈ Finset.Icc 1 (k - 1)) (hc : c < b + 1)
    (hr : r ∈ Finset.Icc b (k - 1)) :
    1 ≤ r + b ∧ b + c ≤ 2 * k ∧ r ≤ k - 1 := by
  simp only [Finset.mem_Icc] at hb hr
  omega

#print axioms certificate_value
#print axioms certificate_negative
#print axioms moment_quadratic_nonnegative
#print axioms closed_form_not_stieltjes

end D5.S0.Certificates.ShankarQStieltjesRefutation
