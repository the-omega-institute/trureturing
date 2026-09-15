/- GID: D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility
   mirror-E: none(waiver:unbounded-prime-valuation-proof)
   anchors: []
   utility: none
   digest: The Chebyshev factorial ratio is divisible by 5n+1, including the exceptional primes. -/

import D5.S3.Arith.FactorialRatio.BalaChebyshevThreeDivisibility

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.FactorialRatio.BalaChebyshevFiveDivisibility

private def defect (n q : Nat) : Int :=
  ((30*n/q : Nat) : Int) + ((n/q : Nat) : Int) - ((15*n/q : Nat) : Int) -
    ((10*n/q : Nat) : Int) - ((6*n/q : Nat) : Int)

/-- The new modulus-dependent fact is the unit contribution at divisors of 5n+1.
The small moduli 2,3,4 are deliberately excluded from that stronger assertion. -/
theorem local_five (n q : Nat) (hq : 0 < q) :
    0 ≤ defect n q ∧ (6 ≤ q → q ∣ 5*n+1 → defect n q = 1) := by
  let r := n % q
  have hr : r < q := Nat.mod_lt n hq
  have split (c : Nat) : c*n/q = c*(n/q)+c*r/q := by
    calc
      c*n/q = (q*(c*(n/q))+c*r)/q := by
        congr 1
        calc
          c*n = c*(q*(n/q)+r) := congrArg (fun x => c*x) (Nat.div_add_mod n q).symm
          _ = q*(c*(n/q))+c*r := by ring
      _ = c*(n/q)+c*r/q := by rw [Nat.mul_add_div hq]
  have red : defect n q = defect r q := by
    unfold defect
    rw [split 30, split 15, split 10, split 6, Nat.div_eq_of_lt hr]
    push_cast
    ring
  have half : 15*r/q = (30*r/q)/2 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*r = (15*r)*2 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 2)]
  have third : 10*r/q = (30*r/q)/3 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*r = (10*r)*3 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 3)]
  have fifth : 6*r/q = (30*r/q)/5 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*r = (6*r)*5 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 5)]
  have bound : 30*r/q < 30 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  constructor
  · rw [red]
    unfold defect
    rw [Nat.div_eq_of_lt hr, half, third, fifth]
    omega
  · intro hsize hdiv
    have hrd : q ∣ 5*r+1 := by
      apply Nat.dvd_of_mod_eq_zero
      have hm := Nat.mod_eq_zero_of_dvd hdiv
      simpa [r, Nat.add_mod, Nat.mul_mod] using hm
    obtain ⟨t, ht⟩ := hrd
    have ht0 : 0 < t := by
      by_contra hn
      have hz : t = 0 := by omega
      simp [hz] at ht
    have ht5 : t < 5 := by
      by_contra hn
      have hh := Nat.mul_le_mul_left q (show 5 ≤ t by omega)
      nlinarith
    rw [red]
    interval_cases t
    · have h30 : 30*r/q = 5 := (Nat.div_eq_iff hq).mpr (by omega)
      have h15 : 15*r/q = 2 := (Nat.div_eq_iff hq).mpr (by omega)
      have h10 : 10*r/q = 1 := (Nat.div_eq_iff hq).mpr (by omega)
      have h6 : 6*r/q = 1 := (Nat.div_eq_iff hq).mpr (by omega)
      norm_num [defect, h30, h15, h10, h6, Nat.div_eq_of_lt hr]
    · have h30 : 30*r/q = 11 := (Nat.div_eq_iff hq).mpr (by omega)
      have h15 : 15*r/q = 5 := (Nat.div_eq_iff hq).mpr (by omega)
      have h10 : 10*r/q = 3 := (Nat.div_eq_iff hq).mpr (by omega)
      have h6 : 6*r/q = 2 := (Nat.div_eq_iff hq).mpr (by omega)
      norm_num [defect, h30, h15, h10, h6, Nat.div_eq_of_lt hr]
    · have h30 : 30*r/q = 17 := (Nat.div_eq_iff hq).mpr (by omega)
      have h15 : 15*r/q = 8 := (Nat.div_eq_iff hq).mpr (by omega)
      have h10 : 10*r/q = 5 := (Nat.div_eq_iff hq).mpr (by omega)
      have h6 : 6*r/q = 3 := (Nat.div_eq_iff hq).mpr (by omega)
      norm_num [defect, h30, h15, h10, h6, Nat.div_eq_of_lt hr]
    · have h30 : 30*r/q = 23 := (Nat.div_eq_iff hq).mpr (by omega)
      have h15 : 15*r/q = 11 := (Nat.div_eq_iff hq).mpr (by omega)
      have h10 : 10*r/q = 7 := (Nat.div_eq_iff hq).mpr (by omega)
      have h6 : 6*r/q = 4 := (Nat.div_eq_iff hq).mpr (by omega)
      norm_num [defect, h30, h15, h10, h6, Nat.div_eq_of_lt hr]

/-- A top-scale contribution compensates for the missing modulus-three term.
It lies strictly above every prime power dividing 5n+1. -/
theorem top_scale_unit (n q : Nat) (hn : 0 < n)
    (hl : 10*n < q) (hu : q ≤ 30*n) : defect n q = 1 := by
  have hq : 0 < q := by omega
  have hnq : n < q := by omega
  have h6q : 6*n < q := by omega
  have half : 15*n/q = (30*n/q)/2 := by
    symm
    rw [Nat.div_div_eq_div_mul, show 30*n = (15*n)*2 by ring,
      Nat.mul_div_mul_right _ _ (by decide : 0 < 2)]
  have hklo : 1 ≤ 30*n/q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
  have hkhi : 30*n/q < 3 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
  unfold defect
  rw [Nat.div_eq_of_lt hnq, Nat.div_eq_of_lt hl,
    Nat.div_eq_of_lt h6q, half]
  omega

/-- Bala's distinct August 2025 conjecture A211417: A(n)/(5n+1) is integral.
The division-free statement uses the exact factorial ratio and includes n=0. -/
theorem bala_five_integrality (n : Nat) :
    (5*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial ∣
      (30*n).factorial*n.factorial := by
  classical
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hL : (30*n).factorial*n.factorial ≠ 0 := by positivity
  have hD : (15*n).factorial*(10*n).factorial*(6*n).factorial ≠ 0 := by positivity
  have hR : (5*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial ≠ 0 := by positivity
  have hbase : (15*n).factorial*(10*n).factorial*(6*n).factorial ∣
      (30*n).factorial*n.factorial := by
    have hb := BalaChebyshevThreeDivisibility.bala_three_integrality n
    have hid :
        (3*n+1)*(15*n).factorial*(10*n).factorial*(6*n).factorial =
        (3*n+1)*((15*n).factorial*(10*n).factorial*(6*n).factorial) := by ring
    rw [hid] at hb
    exact (dvd_mul_left _ _).trans hb
  apply (Nat.factorization_prime_le_iff_dvd hR hL).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [padicValNat.mul (by positivity : (5*n+1)*(15*n).factorial*(10*n).factorial ≠ 0)
      (Nat.factorial_ne_zero (6*n)),
    padicValNat.mul (by positivity : (5*n+1)*(15*n).factorial ≠ 0) (Nat.factorial_ne_zero (10*n)),
    padicValNat.mul (by omega : 5*n+1 ≠ 0) (Nat.factorial_ne_zero (15*n)),
    padicValNat.mul (Nat.factorial_ne_zero (30*n)) (Nat.factorial_ne_zero n)]
  by_cases hpd : p ∣ 5*n+1
  swap
  · have hv := (Nat.factorization_prime_le_iff_dvd hD hL).mpr hbase p hp
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      padicValNat.mul (by positivity) (Nat.factorial_ne_zero (6*n)),
      padicValNat.mul (Nat.factorial_ne_zero (15*n)) (Nat.factorial_ne_zero (10*n)),
      padicValNat.mul (Nat.factorial_ne_zero (30*n)) (Nat.factorial_ne_zero n)] at hv
    rw [padicValNat.eq_zero_of_not_dvd hpd]
    omega
  have vf (m : Nat) (hm : m ≤ 30*n+1) :
      padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 (30*n+2), m/p^j :=
    padicValNat_factorial (lt_of_le_of_lt (p.log_le_self m) (by omega))
  have total :
      (padicValNat p (30*n).factorial : Int)+(padicValNat p n.factorial : Int)-
      (padicValNat p (15*n).factorial : Int)-(padicValNat p (10*n).factorial : Int)-
      (padicValNat p (6*n).factorial : Int) =
      ∑ j ∈ Finset.Ico 1 (30*n+2), defect n (p^j) := by
    rw [vf (30*n) (by omega), vf n (by omega), vf (15*n) (by omega),
      vf (10*n) (by omega), vf (6*n) (by omega)]
    simp only [Nat.cast_sum, defect, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hp2 : p = 2
  · subst p
    have hd : ¬2 ∣ 3*n := by omega
    have hchoose := Nat.choose_mul_factorial_mul_factorial (show 5*n ≤ 8*n by omega)
    rw [show 8*n-5*n = 3*n by omega] at hchoose
    have hc := congrArg (padicValNat 2) hchoose
    rw [padicValNat.mul
      (mul_ne_zero (Nat.choose_ne_zero (n := 8*n) (k := 5*n) (by omega))
        (Nat.factorial_ne_zero (5*n))) (Nat.factorial_ne_zero (3*n)),
      padicValNat.mul (Nat.choose_ne_zero (n := 8*n) (k := 5*n) (by omega))
        (Nat.factorial_ne_zero (5*n))] at hc
    have step := Nat.choose_succ_right_eq (8*n) (5*n)
    rw [show 8*n-5*n = 3*n by omega] at step
    have hs := congrArg (padicValNat 2) step
    rw [padicValNat.mul (Nat.choose_ne_zero (n := 8*n) (k := 5*n+1) (by omega))
        (by omega : 5*n+1 ≠ 0),
      padicValNat.mul (Nat.choose_ne_zero (n := 8*n) (k := 5*n) (by omega))
        (by omega : 3*n ≠ 0), padicValNat.eq_zero_of_not_dvd hd] at hs
    have f15 := padicValNat_factorial_mul (p := 2) (15*n)
    have f5 := padicValNat_factorial_mul (p := 2) (5*n)
    have f3 := padicValNat_factorial_mul (p := 2) (3*n)
    have f4 := padicValNat_factorial_mul (p := 2) (4*n)
    have f2 := padicValNat_factorial_mul (p := 2) (2*n)
    have f1 := padicValNat_factorial_mul (p := 2) n
    norm_num [← Nat.mul_assoc] at f15 f5 f3 f4 f2 f1
    omega
  by_cases hp3 : p = 3
  · subst p
    let v := padicValNat 3 (5*n+1)
    have hv : 1 ≤ v := one_le_padicValNat_of_dvd (by omega) hpd
    let k := Nat.log 3 (10*n)+1
    have hk0 : 1 ≤ k := by dsimp [k]; omega
    have hktop : k < 30*n+2 := by
      have hh := Nat.log_le_self 3 (10*n)
      dsimp [k]
      omega
    have qlo : 10*n < (3:Nat)^k := by
      apply (Nat.log_lt_iff_lt_pow (by decide : 1 < 3) (by omega : 10*n ≠ 0)).mp
      dsimp [k]
      omega
    have qhi : (3:Nat)^k ≤ 30*n := by
      have hh := Nat.pow_log_le_self 3 (by omega : 10*n ≠ 0)
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have vk : v < k := by
      have hd : (3:Nat)^v ∣ 5*n+1 := pow_padicValNat_dvd
      have hb := Nat.le_of_dvd (by omega : 0 < 5*n+1) hd
      by_contra hh
      have hkv : k ≤ v := by omega
      have hpw : (3:Nat)^k ≤ 3^v := Nat.pow_le_pow_right (by norm_num) hkv
      omega
    have hknot : k ∉ Finset.Ico 2 (v+1) := by
      simp only [Finset.mem_Ico]
      omega
    have units : ∀ j ∈ insert k (Finset.Ico 2 (v+1)), defect n ((3:Nat)^j) = 1 := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact top_scale_unit n (3^k) hn qlo qhi
      · obtain ⟨hj2, hjv⟩ := Finset.mem_Ico.mp hj
        have hsize : 6 ≤ (3:Nat)^j := by
          have hh : (3:Nat)^2 ≤ 3^j := Nat.pow_le_pow_right (by norm_num) hj2
          norm_num at hh
          omega
        have hd : (3:Nat)^j ∣ 5*n+1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (by dsimp [v] at hjv; omega)
        exact (local_five n (3^j) (pow_pos (by decide) j)).2 hsize hd
    have low : (v : Int) ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), defect n ((3:Nat)^j) := by
      calc
        (v : Int) = ∑ j ∈ insert k (Finset.Ico 2 (v+1)), (1 : Int) := by
          rw [Finset.sum_insert hknot]
          simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          omega
        _ = ∑ j ∈ insert k (Finset.Ico 2 (v+1)), defect n ((3:Nat)^j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (units j hj).symm
        _ ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), defect n ((3:Nat)^j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            simp only [Finset.mem_insert, Finset.mem_Ico] at hj ⊢
            omega
          · intro j _ _
            exact (local_five n (3^j) (pow_pos (by decide) j)).1
    dsimp [v] at low
    omega
  by_cases hp5 : p = 5
  · subst p
    omega
  have hp7 : 7 ≤ p := by
    by_contra h
    interval_cases p <;> norm_num at hp <;> omega
  let v := padicValNat p (5*n+1)
  have vb : v ≤ 30*n+1 := by
    exact (padicValNat_le_nat_log (5*n+1)).trans ((p.log_le_self _).trans (by omega))
  have low : (v : Int) ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), defect n (p^j) := by
    calc
      (v : Int) = ∑ j ∈ Finset.Ico 1 (v+1), (1 : Int) := by simp
      _ ≤ ∑ j ∈ Finset.Ico 1 (v+1), defect n (p^j) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj0, hjv⟩ := Finset.mem_Ico.mp hj
        have hd : p^j ∣ 5*n+1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (by dsimp [v] at hjv; omega)
        have hsize : 6 ≤ p^j := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          have hk : 1 ≤ p^k := Nat.succ_le_iff.mpr (pow_pos hp.pos k)
          rw [pow_succ]
          nlinarith
        rw [(local_five n (p^j) (pow_pos hp.pos j)).2 hsize hd]
      _ ≤ ∑ j ∈ Finset.Ico 1 (30*n+2), defect n (p^j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        · intro j _ _
          exact (local_five n (p^j) (pow_pos hp.pos j)).1
  dsimp [v] at low
  omega

#print axioms bala_five_integrality

end D5.S3.Arith.FactorialRatio.BalaChebyshevFiveDivisibility
