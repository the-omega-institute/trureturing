/- GID: D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample
   generality: I
   mirror-B: D5/B/S3/Factorization/FactorDensityHighlyCompositeCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:bcd6ccc04843e1ea8eec6f311a87f1c58d908c0e79e292a6cddb653eda8101ae
   digest: A kernel certificate refutes Switkay's expanded factor-density coincidence claim. -/

import D5.S3.Arith.PrimitiveRoot.SievePrimeFactors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.IntervalCases

namespace D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample
open D5.S3.Arith.PrimitiveRoot.SievePrimeFactors

/-- The number of positive divisors of `n`. -/
def tau (n : Nat) : Nat := n.divisors.card

/-- Switkay's expanded factor-density score `tau(n) / log(n + 1)`. -/
noncomputable def g (n : Nat) : Real := (tau n : Real) / Real.log (n + 1)

/-- The expanded factor-density record predicate. -/
def FD (n : Nat) : Prop :=
  forall m : Nat, 1 <= m -> m < n -> g m < g n

/-- The highly composite record predicate. -/
def HC (n : Nat) : Prop :=
  forall m : Nat, 1 <= m -> m < n -> tau m < tau n

/-- The highly composite counterexample candidate. -/
def N : Nat := 73329656400

/-- The smaller factor-density witness. -/
def M : Nat := 64250746560

/-- The first eleven primes used by the distinct-prime-factor bound. -/
def primes11 : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- The first ten primes used by the exhaustive exponent-profile checker. -/
def primes10 : List Nat := primes11.take 10

/-- A pruned Boolean checker for divisor-count bounds on positive exponent profiles. -/
def profileCheck : List Nat -> Nat -> Nat -> Bool
  | [], _, t => decide (t <= 3584)
  | p :: ps, v, t =>
      decide (t <= 3584) &&
        ((List.range' 1 36).takeWhile fun e =>
          decide (v * p ^ e < 73329656400)).all fun e =>
            profileCheck ps (v * p ^ e) (t * (e + 1))

private def profileValue : List Nat -> List Nat -> Nat
  | _, [] => 1
  | [], _ :: _ => 0
  | p :: ps, e :: es => p ^ e * profileValue ps es

private def profileTau (es : List Nat) : Nat := (es.map fun e => e + 1).prod

private inductive Fits : List Nat -> List Nat -> Prop
  | nil (bases : List Nat) : Fits bases []
  | cons {p e : Nat} {bases es : List Nat} : Fits bases es -> Fits (p :: bases) (e :: es)

private inductive PrefixLE : List Nat -> List Nat -> Prop
  | nil (bases : List Nat) : PrefixLE bases []
  | cons {p q : Nat} {bases qs : List Nat} :
      p <= q -> PrefixLE bases qs -> PrefixLE (p :: bases) (q :: qs)

namespace PrefixLE

private theorem fits {bases qs : List Nat} (h : PrefixLE bases qs) : Fits bases qs := by
  induction h with
  | nil => exact Fits.nil _
  | cons _ _ ih => exact Fits.cons ih

private theorem prod_le {bases qs : List Nat} (h : PrefixLE bases qs)
    (hlen : bases.length = qs.length) : bases.prod <= qs.prod := by
  induction h with
  | nil =>
      simp only [List.length_nil] at hlen
      simp [List.eq_nil_of_length_eq_zero hlen]
  | @cons p q bases qs hpq _ ih =>
      have hlen' : bases.length = qs.length := Nat.add_right_cancel hlen
      simpa using Nat.mul_le_mul hpq (ih hlen')

private theorem fits_map {bases qs : List Nat} (h : PrefixLE bases qs) (f : Nat -> Nat) :
    Fits bases (qs.map f) := by
  induction h with
  | nil => exact Fits.nil _
  | cons _ _ ih => exact Fits.cons ih

private theorem profileValue_map_le {bases qs : List Nat} (h : PrefixLE bases qs)
    (f : Nat -> Nat) :
    profileValue bases (qs.map f) <= (qs.map fun q => q ^ f q).prod := by
  induction h with
  | nil => simp [profileValue]
  | cons hpq _ ih =>
      simp only [List.map_cons, profileValue, List.prod_cons]
      exact Nat.mul_le_mul (pow_le_pow_left' hpq _) ih

end PrefixLE

private theorem prefixLE_of_get {bases qs : List Nat} (hlen : qs.length <= bases.length)
    (hget : forall i : Fin qs.length, bases.get (Fin.castLE hlen i) <= qs.get i) :
    PrefixLE bases qs := by
  induction qs generalizing bases with
  | nil => exact PrefixLE.nil _
  | cons q qs ih =>
      cases bases with
      | nil => simp at hlen
      | cons p bases =>
          have hlen' : qs.length <= bases.length := Nat.le_of_succ_le_succ hlen
          apply PrefixLE.cons
          · simpa using hget (0 : Fin (q :: qs).length)
          · exact ih hlen' (fun i => by simpa using hget i.succ)

private theorem profileValue_pos {bases es : List Nat} (hfit : Fits bases es)
    (hbases : forall p, p ∈ bases -> 0 < p) : 0 < profileValue bases es := by
  induction hfit with
  | nil => simp [profileValue]
  | @cons p _ bases _ _ ih =>
      simp only [profileValue]
      exact Nat.mul_pos (Nat.pow_pos (hbases p (by simp)))
        (ih fun q hq => hbases q (by simp [hq]))

private theorem exponent_mem_takeWhile {v p start fuel e : Nat}
    (hp : 0 < p) (hstart : start <= e) (hend : e < start + fuel)
    (hvalue : v * p ^ e < 73329656400) :
    e ∈ (List.range' start fuel).takeWhile
      (fun j => decide (v * p ^ j < 73329656400)) := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      have hcur : v * p ^ start < 73329656400 := by
        exact lt_of_le_of_lt (Nat.mul_le_mul_left v (Nat.pow_le_pow_right hp hstart)) hvalue
      rw [List.range'_succ]
      simp only [hcur, decide_true, List.takeWhile_cons_of_pos, List.mem_cons]
      rcases eq_or_lt_of_le hstart with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr (ih (start := start + 1) (by omega) (by omega))

private theorem profileCheck_bound {bases : List Nat} {v t : Nat}
    (h : profileCheck bases v t = true) : t <= 3584 := by
  by_contra ht
  have hfalse : profileCheck bases v t = false := by
    cases bases <;> simp [profileCheck, ht]
  rw [hfalse] at h
  exact Bool.noConfusion h

private theorem profileCheck_sound {bases es : List Nat} {v t : Nat}
    (hfit : Fits bases es)
    (hbases : forall p, p ∈ bases -> 0 < p)
    (hexps : forall e, e ∈ es -> 1 <= e /\ e <= 36)
    (hvalue : v * profileValue bases es < 73329656400)
    (hcheck : profileCheck bases v t = true) :
    t * profileTau es <= 3584 := by
  induction hfit generalizing v t with
  | nil =>
      simpa [profileTau] using profileCheck_bound hcheck
  | @cons p e bases es hfit ih =>
      have he := hexps e (by simp)
      have hrestpos : 0 < profileValue bases es :=
        profileValue_pos hfit fun q hq => hbases q (by simp [hq])
      have hstep : v * p ^ e < 73329656400 := by
        apply lt_of_le_of_lt _ hvalue
        simp only [profileValue]
        exact Nat.mul_le_mul_left v (Nat.le_mul_of_pos_right _ hrestpos)
      have hemem : e ∈ (List.range' 1 36).takeWhile
          (fun j => decide (v * p ^ j < 73329656400)) :=
        exponent_mem_takeWhile (hbases p (by simp)) he.1 (by omega) hstep
      have hnext : profileCheck bases (v * p ^ e) (t * (e + 1)) = true := by
        rw [profileCheck] at hcheck
        have hall : ((List.range' 1 36).takeWhile fun j =>
            decide (v * p ^ j < 73329656400)).all (fun j =>
              profileCheck bases (v * p ^ j) (t * (j + 1))) = true := by
          cases ha : decide (t <= 3584) <;>
            cases hb : ((List.range' 1 36).takeWhile fun j =>
              decide (v * p ^ j < 73329656400)).all (fun j =>
                profileCheck bases (v * p ^ j) (t * (j + 1))) <;>
            simp [ha, hb] at hcheck ⊢
        exact (List.all_eq_true.mp hall) e hemem
      have hrec := ih
        (fun q hq => hbases q (by simp [hq]))
        (fun j hj => hexps j (by simp [hj]))
        (by simpa [profileValue, mul_assoc] using hvalue)
        hnext
      simpa [profileTau, mul_assoc] using hrec

private theorem nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h := Nat.nth_count (p := Nat.Prime) (by decide : Nat.Prime 23)
  norm_num [Nat.count] at h
  exact h

private theorem nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h := Nat.nth_count (p := Nat.Prime) (by decide : Nat.Prime 29)
  norm_num [Nat.count] at h
  exact h

private theorem nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h := Nat.nth_count (p := Nat.Prime) (by decide : Nat.Prime 31)
  norm_num [Nat.count] at h
  exact h

private theorem primes11_get_nth (i : Nat) (hi : i < primes11.length) :
    primes11[i] = Nat.nth Nat.Prime i := by
  norm_num [primes11] at hi
  interval_cases i <;>
    simp [primes11, nth_prime_five, nth_prime_six, nth_prime_seven,
      nth_prime_eight, nth_prime_nine, nth_prime_ten]

private theorem primes10_get_nth (i : Nat) (hi : i < primes10.length) :
    primes10[i] = Nat.nth Nat.Prime i := by
  have hi' : i < primes11.length := by
    norm_num [primes10, primes11] at hi ⊢
    omega
  simpa [primes10] using primes11_get_nth i hi'

private theorem primes10_pos : forall p, p ∈ primes10 -> 0 < p := by decide

private theorem primeFactors_card_le_ten {n : Nat} (hnpos : 0 < n)
    (hnlt : n < 73329656400) :
    n.primeFactors.card <= 10 := by
  let qs := n.primeFactors.sort (fun a b => a <= b)
  have hlen : qs.length = n.primeFactors.card := by simp [qs]
  have hsorted : qs.SortedLT := by simpa [qs] using n.primeFactors.sortedLT_sort
  have hprime : forall q, q ∈ qs -> Nat.Prime q := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors
      ((Finset.mem_sort (fun a b : Nat => a <= b)).mp (by simpa [qs] using hq))
  by_contra hncard
  have hlen11 : 11 <= qs.length := by omega
  have htakelen : (qs.take 11).length = 11 := by
    rw [List.length_take]
    exact Nat.min_eq_left hlen11
  have hprefix : PrefixLE primes11 (qs.take 11) := by
    refine prefixLE_of_get (by simp [htakelen, primes11]) ?_
    intro i
    have hib : i.val < primes11.length := by
      norm_num [primes11]
      omega
    change primes11.get ⟨i.val, hib⟩ <= (qs.take 11).get i
    rw [show primes11.get ⟨i.val, hib⟩ = Nat.nth Nat.Prime i.val by
      simpa using primes11_get_nth i.val hib]
    simpa using nth_prime_le_get hsorted hprime i.val (by omega)
  have hprodle := hprefix.prod_le (by simp [htakelen, primes11])
  have hprimeprod : primes11.prod = 200560490130 := by norm_num [primes11]
  have htake_dvd_qs : (qs.take 11).prod ∣ qs.prod := by
    refine ⟨(qs.drop 11).prod, ?_⟩
    exact (List.prod_take_mul_prod_drop qs 11).symm
  have hqsprod : qs.prod = ∏ p ∈ n.primeFactors, p := by
    calc
      qs.prod = n.primeFactors.toList.prod :=
        (Finset.sort_perm_toList n.primeFactors (fun a b : Nat => a <= b)).prod_eq
      _ = ∏ p ∈ n.primeFactors, p := Finset.prod_toList n.primeFactors
  have htake_dvd_n : (qs.take 11).prod ∣ n := by
    apply htake_dvd_qs.trans
    rw [hqsprod]
    exact Nat.prod_primeFactors_dvd n
  have htaken : (qs.take 11).prod <= n := Nat.le_of_dvd hnpos htake_dvd_n
  rw [hprimeprod] at hprodle
  omega

private theorem tau_le_bound_of_lt {n : Nat} (hnpos : 0 < n) (hnlt : n < 73329656400)
    (hcertificate : profileCheck primes10 1 1 = true) : tau n <= 3584 := by
  let qs := n.primeFactors.sort (fun a b => a <= b)
  let es := qs.map (n.factorization ·)
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hlenqs : qs.length <= primes10.length := by
    simpa [qs, primes10, primes11] using primeFactors_card_le_ten hnpos hnlt
  have hsorted : qs.SortedLT := by simpa [qs] using n.primeFactors.sortedLT_sort
  have hprime : forall q, q ∈ qs -> Nat.Prime q := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors
      ((Finset.mem_sort (fun a b : Nat => a <= b)).mp (by simpa [qs] using hq))
  have hprefix : PrefixLE primes10 qs := by
    apply prefixLE_of_get hlenqs
    intro i
    change primes10[i.val] <= qs[i.val]
    rw [primes10_get_nth i.val (by omega)]
    exact nth_prime_le_get hsorted hprime i.val i.isLt
  have hexps : forall e, e ∈ es -> 1 <= e /\ e <= 36 := by
    intro e he
    rw [List.mem_map] at he
    rcases he with ⟨q, hq, rfl⟩
    have hqpf : q ∈ n.primeFactors :=
      (Finset.mem_sort (fun a b : Nat => a <= b)).mp (by simpa [qs] using hq)
    have hp := Nat.prime_of_mem_primeFactors hqpf
    have hdvd := Nat.dvd_of_mem_primeFactors hqpf
    constructor
    · exact hp.factorization_pos_of_dvd hn hdvd
    · by_contra hle
      have h37 : 37 <= n.factorization q := by omega
      have hpowdvd : q ^ 37 ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 h37
      have hpowle : q ^ 37 <= n := Nat.le_of_dvd hnpos hpowdvd
      have htwo : 2 ^ 37 <= q ^ 37 := pow_le_pow_left' hp.two_le 37
      norm_num at htwo
      omega
  have hactual : (qs.map fun q => q ^ n.factorization q).prod = n := by
    calc
      (qs.map fun q => q ^ n.factorization q).prod =
          (n.primeFactors.toList.map fun q => q ^ n.factorization q).prod :=
        ((Finset.sort_perm_toList n.primeFactors (fun a b : Nat => a <= b)).map _).prod_eq
      _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Finset.prod_map_toList n.primeFactors _
      _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm
  have hvaluele : profileValue primes10 es <= n := by
    dsimp [es]
    exact (hprefix.profileValue_map_le n.factorization).trans_eq hactual
  have hprofile : profileTau es <= 3584 := by
    simpa using profileCheck_sound (hprefix.fits_map n.factorization) primes10_pos hexps
      (lt_of_le_of_lt (by simpa using hvaluele) hnlt) hcertificate
  have htau : profileTau es = tau n := by
    rw [profileTau]
    dsimp [es]
    simp only [List.map_map]
    calc
      (qs.map fun q => n.factorization q + 1).prod =
          (n.primeFactors.toList.map fun q => n.factorization q + 1).prod :=
        ((Finset.sort_perm_toList n.primeFactors (fun a b : Nat => a <= b)).map _).prod_eq
      _ = ∏ p ∈ n.primeFactors, (n.factorization p + 1) :=
        Finset.prod_map_toList n.primeFactors _
      _ = tau n := by simpa [tau] using (Nat.card_divisors hn).symm
  rwa [htau] at hprofile

/-- The exact prime factorization of the counterexample candidate. -/
theorem N_factorization :
    N = 2 ^ 4 * 3 ^ 4 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
  norm_num [N]

/-- The exact prime factorization of the smaller comparison witness. -/
theorem M_factorization :
    M = 2 ^ 6 * 3 ^ 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 := by
  norm_num [M]

/-- The counterexample candidate has exactly 3600 positive divisors. -/
theorem tau_N : tau N = 3600 := by
  rw [N_factorization]
  simp only [tau]
  repeat' rw [Nat.Coprime.card_divisors_mul (by decide)]
  decide

/-- The smaller comparison witness has exactly 3584 positive divisors. -/
theorem tau_M : tau M = 3584 := by
  rw [M_factorization]
  simp only [tau]
  repeat' rw [Nat.Coprime.card_divisors_mul (by decide)]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The exhaustive kernel reduction visits all 22,091 reachable prefix profiles.
/-- Kernel evaluation of all 22,091 reachable positive-exponent prefix profiles. -/
theorem profile_certificate : profileCheck primes10 1 1 = true := by
  decide

/-- Every positive predecessor of `N` has at most 3584 positive divisors. -/
theorem tau_lt_N_bound : forall m, 0 < m -> m < N -> tau m <= 3584 := by
  intro m hmpos hmlt
  exact tau_le_bound_of_lt hmpos (by simpa [N] using hmlt) profile_certificate

/-- The candidate `N` is highly composite. -/
theorem hc_N : HC N := by
  intro m hmpos hmlt
  have hmle := tau_lt_N_bound m hmpos hmlt
  rw [tau_N]
  omega

/-- The integer inequality that transports to the strict comparison of factor-density scores. -/
theorem power_witness :
    (64250746561 : Nat) ^ 225 < (73329656401 : Nat) ^ 224 := by
  norm_num

/-- The counterexample candidate has smaller factor density than the comparison witness. -/
theorem g_N_lt_g_M : g N < g M := by
  have hlogM : (0 : Real) < Real.log 64250746561 := by positivity
  have hlogN : (0 : Real) < Real.log 73329656401 := by positivity
  have hp : (64250746561 : Real) ^ 225 < (73329656401 : Real) ^ 224 := by
    exact_mod_cast power_witness
  have hl := Real.log_lt_log
    (by positivity : (0 : Real) < (64250746561 : Real) ^ 225) hp
  have hweighted :
      (225 : Real) * Real.log 64250746561 <
        (224 : Real) * Real.log 73329656401 := by
    simpa [Real.log_pow] using hl
  rw [g, tau_N, g, tau_M]
  norm_num only [N, M, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  rw [div_lt_div_iff₀ hlogN hlogM]
  nlinarith [hweighted]

/-- The candidate `N` is not an expanded factor-density record. -/
theorem not_fd_N : ¬ FD N := by
  intro h
  have hMN : M < N := by norm_num [M, N]
  have hgreater := h M (by norm_num [M]) hMN
  exact (not_lt_of_ge g_N_lt_g_M.le) hgreater

/-- The candidate `N` is not the exceptional value 45360. -/
theorem N_ne : N ≠ 45360 := by norm_num [N]

/-- The explicit highly composite number `73329656400` is neither the exceptional
number `45360` nor a record for Switkay's expanded factor-density score. -/
theorem factor_density_highly_composite_counterexample :
    HC N ∧ N ≠ 45360 ∧ ¬ FD N := by
  exact ⟨hc_N, N_ne, not_fd_N⟩

/-- Switkay's proposed expanded factor-density/highly-composite coincidence is false. -/
theorem switkay_expanded_claim_false :
    ¬ (forall n : Nat, 1 <= n -> (FD n <-> (HC n /\ n ≠ 45360))) := by
  intro hclaim
  have hcounter := factor_density_highly_composite_counterexample
  have hequiv := hclaim N (by norm_num [N])
  exact hcounter.2.2 (hequiv.mpr ⟨hcounter.1, hcounter.2.1⟩)

example : tau 12 = 6 := by decide
example : ∃ n : Nat, 1 <= n /\ n < N := ⟨1, by norm_num [N]⟩
example : profileCheck [] 1 3584 = true := by decide
example : M < N := by norm_num [M, N]

#print axioms N_factorization
#print axioms M_factorization
#print axioms tau_N
#print axioms tau_M
#print axioms profile_certificate
#print axioms tau_lt_N_bound
#print axioms hc_N
#print axioms power_witness
#print axioms g_N_lt_g_M
#print axioms not_fd_N
#print axioms N_ne
#print axioms factor_density_highly_composite_counterexample
#print axioms switkay_expanded_claim_false

end D5.S3.Factorization.FactorDensityHighlyCompositeCounterexample
