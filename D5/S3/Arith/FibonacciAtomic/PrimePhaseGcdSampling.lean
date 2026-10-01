/- GID: D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp prime Fibonacci phase identification has fixed bounded natural counterexamples at arbitrarily late positive times. -/

import D5.S3.Arith.FibonacciAtomic.TimeSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling

open D5.S3.Arith.FibonacciAtomic.TimeSampling

def localGcd (p : ℕ) (n z : ℤ) (k : ℕ) : ℕ :=
  Nat.gcd (Int.natAbs (Nat.fib (k - 1) * n + Nat.fib k * z)) p

def sourceGcd (H a b k : ℕ) : ℕ :=
  Nat.gcd (Nat.fib (k + 3) * a + Nat.fib (k + 4) * b) H

def primitive (p : ℕ) (n z : ℤ) : Prop :=
  ¬p ∣ n.natAbs ∨ ¬p ∣ z.natAbs

theorem prime_phase_gcd_sampling {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) :
    let r := zeroRank p
    let A := S.image (fun k => k % r)
    let T := if r = p + 1 then r - 1 else r
    ((∀ n z n' z' : ℤ,
      (∀ k ∈ S, localGcd p n z k = localGcd p n' z' k) →
      ∀ k, 0 < k → localGcd p n z k = localGcd p n' z' k) ↔ T ≤ A.card) ∧
    ((∀ a b a' b' : ℕ,
      (∀ k ∈ S, sourceGcd p a b k = sourceGcd p a' b' k) →
      ∀ k, 0 < k → sourceGcd p a b k = sourceGcd p a' b' k) ↔ T ≤ A.card) ∧
    (A.card < T → ∀ Q, 0 < Q →
      let H := Q * p
      ∃ n z n' z' : ℤ, ∃ a b a' b' : ℕ,
        primitive p n z ∧ primitive p n' z' ∧
        a < H ∧ b < H ∧ a' < H ∧ b' < H ∧
        (∀ k, 0 < k → sourceGcd H a b k = Q * localGcd p n z k ∧
          sourceGcd H a' b' k = Q * localGcd p n' z' k) ∧
        (∀ k ∈ S, localGcd p n z k = localGcd p n' z' k ∧
          sourceGcd H a b k = sourceGcd H a' b' k) ∧
        ∀ B, ∃ t, B < t ∧ 0 < t ∧ t ∉ S ∧
          localGcd p n z t = p ∧ localGcd p n' z' t = 1 ∧
          sourceGcd H a b t = H ∧ sourceGcd H a' b' t = Q ∧
          sourceGcd H a' b' t = H / p) := by
  classical
  let r := zeroRank p
  let A := S.image (fun k => k % r)
  let T := if r = p + 1 then r - 1 else r
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hlimit : recoveryLimit p = zeroRank p := by
    have hprimes : {q : ℕ | q.Prime ∧ q ∣ p} = {p} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (Nat.prime_dvd_prime_iff_eq h.1 hp).mp h.2,
        fun h => h.symm ▸ ⟨hp, dvd_refl p⟩⟩
    simp [recoveryLimit, hprimes]
  have hmaximum := pairwise_recovery_maximum p hp.two_le
  rw [hlimit] at hmaximum
  have hrankpos : 0 < zeroRank p := by
    have hsingle : PairwiseRecovery p {0} := by
      intro s hs t ht hst
      simp only [Finset.mem_singleton] at hs ht
      omega
    have h := hmaximum.2 {0} hsingle
    simp only [Finset.card_singleton] at h
    omega
  have hrankmem : 0 < zeroRank p ∧ p ∣ Nat.fib (zeroRank p) :=
    Nat.sInf_mem (Nat.nonempty_of_pos_sInf hrankpos)
  have hrankmin (j : ℕ) (hj : 0 < j) (hz : p ∣ Nat.fib j) : zeroRank p ≤ j :=
    Nat.sInf_le ⟨hj, hz⟩
  have hranklower : 3 ≤ zeroRank p := by
    have h := hrankmem.2
    by_contra hsmall
    have hcases : zeroRank p = 1 ∨ zeroRank p = 2 := by omega
    rcases hcases with hone | htwo
    · rw [hone] at h
      exact hp.not_dvd_one (by simpa using h)
    · rw [htwo] at h
      exact hp.not_dvd_one (by simpa using h)
  have hrankupper : zeroRank p ≤ p + 1 := by
    by_cases hp5 : p = 5
    · subst p
      have h := hrankmin 5 (by decide) (by norm_num)
      omega
    · have hd := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound hp hp5
        hrankmem.1 hrankmem.2 hrankmin
      split_ifs at hd with heps
      · exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hd).trans (by omega)
      · exact Nat.le_of_dvd (by omega) hd
  have hr : 0 < r := hrankpos
  have hzero : p ∣ Nat.fib r := hrankmem.2
  have hmin : ∀ j, 0 < j → p ∣ Nat.fib j → r ≤ j := hrankmin
  have hpair (i j : Fin r) (hne : i ≠ j) :
      Function.Injective (fun x : ZMod p × ZMod p => (readout p i x, readout p j x)) := by
    have hneq : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hneq with hij | hji
    · exact hmaximum.1 i (Finset.mem_range.mpr i.isLt) j
        (Finset.mem_range.mpr j.isLt) hij
    · intro x y h
      exact hmaximum.1 j (Finset.mem_range.mpr j.isLt) i
        (Finset.mem_range.mpr i.isLt) hji (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  have htwozero (x : ZMod p × ZMod p) (i j : Fin r) (hne : i ≠ j)
      (hi : readout p i x = 0) (hj : readout p j x = 0) : x = (0, 0) := by
    apply hpair i j hne
    change (readout p i x, readout p j x) = (readout p i (0, 0), readout p j (0, 0))
    rw [hi, hj]
    simp [readout]
  let kernel (j : Fin r) : ZMod p × ZMod p :=
    ((Nat.fib (j.val + 1) : ZMod p), -(Nat.fib j.val : ZMod p))
  have hkernel_zero (j : Fin r) : readout p j (kernel j) = 0 := by
    dsimp [kernel, readout]
    ring
  have hkernel_ne (j : Fin r) : kernel j ≠ (0, 0) := by
    intro h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    have hd1 : p ∣ Nat.fib (j.val + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hfirst
    have hd0 : p ∣ Nat.fib j.val := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa [kernel] using hsecond
    have hg := Nat.dvd_gcd hd0 hd1
    rw [(Nat.fib_coprime_fib_succ j.val).gcd_eq_one] at hg
    exact hp.not_dvd_one hg
  have hkernel_exact (i j : Fin r) : readout p i (kernel j) = 0 ↔ i = j := by
    constructor
    · intro hi
      by_contra hne
      exact hkernel_ne j (htwozero (kernel j) i j hne hi (hkernel_zero j))
    · intro hij
      rw [hij]
      exact hkernel_zero j
  have hden (j : Fin (r - 1)) : (Nat.fib (j.val + 1) : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hbound := hmin (j.val + 1) (by omega) hd
    have hj := j.isLt
    omega
  let slope (j : Fin (r - 1)) : ZMod p :=
    -(Nat.fib j.val : ZMod p) / (Nat.fib (j.val + 1) : ZMod p)
  have hslope_zero (j : Fin (r - 1)) : readout p j.val (1, slope j) = 0 := by
    dsimp [readout, slope]
    field_simp [hden j]
    ring
  have hslope_inj : Function.Injective slope := by
    intro i j hij
    by_contra hne
    let ii : Fin r := ⟨i.val, by have hi := i.isLt; omega⟩
    let jj : Fin r := ⟨j.val, by have hj := j.isLt; omega⟩
    have hneq : ii ≠ jj := by
      intro h
      apply hne
      apply Fin.ext
      exact congrArg (fun q : Fin r => q.val) h
    have hz := htwozero (1, slope i) ii jj hneq (hslope_zero i)
      (by rw [hij]; exact hslope_zero j)
    have bad := congrArg Prod.fst hz
    exact one_ne_zero bad
  have hlast (d : ZMod p) : readout p (r - 1) (1, d) ≠ 0 := by
    have hf : (Nat.fib r : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hzero
    have hprev : (Nat.fib (r - 1) : ZMod p) ≠ 0 := by
      intro hz
      have hbound := hmin (r - 1) (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
      omega
    simpa [readout, show r - 1 + 1 = r by omega, hf] using hprev
  have hnohit (hproper : r < p + 1) : ∃ x : ZMod p × ZMod p,
      x ≠ (0, 0) ∧ ∀ j : Fin r, readout p j x ≠ 0 := by
    have hc : (Finset.univ.image slope).card < (Finset.univ : Finset (ZMod p)).card := by
      rw [Finset.card_image_of_injective _ hslope_inj]
      simp only [Finset.card_univ, Fintype.card_fin, ZMod.card]
      omega
    obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    refine ⟨(1, d), fun h => one_ne_zero (congrArg Prod.fst h), ?_⟩
    intro j hz
    by_cases hj : j.val = r - 1
    · exact hlast d (hj ▸ hz)
    · let jj : Fin (r - 1) := ⟨j.val, by have hjlt := j.isLt; omega⟩
      have heq : slope jj = d := by
        dsimp [readout] at hz
        dsimp [slope, jj]
        apply (div_eq_iff (hden jj)).mpr
        linear_combination -hz
      exact hd (Finset.mem_image.mpr ⟨jj, Finset.mem_univ _, heq⟩)
  have hfullhit (hfull : r = p + 1) (x : ZMod p × ZMod p) (hx : x ≠ (0, 0)) :
      ∃ j : Fin r, readout p j x = 0 := by
    by_cases hx1 : x.1 = 0
    · refine ⟨⟨r - 1, by omega⟩, ?_⟩
      simp [readout, hx1, show r - 1 + 1 = r by omega,
        (ZMod.natCast_eq_zero_iff _ _).mpr hzero]
    · have hs : Function.Surjective slope := by
        exact ((Fintype.bijective_iff_injective_and_card slope).mpr
          ⟨hslope_inj, by simp [hfull, ZMod.card]⟩).surjective
      obtain ⟨j, hj⟩ := hs (x.2 / x.1)
      refine ⟨⟨j.val, by have hjlt := j.isLt; omega⟩, ?_⟩
      have hz := hslope_zero j
      rw [hj] at hz
      dsimp [readout] at hz ⊢
      have hmul := congrArg (fun y : ZMod p => x.1 * y) hz
      field_simp [hx1] at hmul
      linear_combination hmul
  have hshift_of_zero (k : ℕ) (hk : 0 < k) (n z : ℤ) :
      localGcd p n z (k + r) = localGcd p n z k := by
    have hcop : Nat.Coprime (Nat.fib (r - 1)) (Nat.fib r) := by
      have hidx : r - 1 + 1 = r := by omega
      have h := Nat.fib_coprime_fib_succ (r - 1)
      rw [hidx] at h
      exact h
    have hcop' : Nat.Coprime (Nat.fib (r - 1)) p :=
      Nat.Coprime.of_dvd_right hzero hcop
    have hunit : IsUnit (Nat.fib (r - 1) : ZMod p) :=
      (ZMod.isUnit_iff_coprime _ _).2 hcop'
    have hread (j : ℕ) (hj : 0 < j) :
        readout p (j - 1) ((n : ZMod p), (z : ZMod p)) = 0 ↔
          p ∣ Int.natAbs (Nat.fib (j - 1) * n + Nat.fib j * z) := by
      have hzmod : readout p (j - 1) ((n : ZMod p), (z : ZMod p)) =
          (((Nat.fib (j - 1) : ℤ) * n + (Nat.fib j : ℤ) * z : ℤ) : ZMod p) := by
        simp only [readout, Int.cast_add, Int.cast_mul, Int.cast_natCast]
        rw [show j - 1 + 1 = j by omega]
      rw [hzmod, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
    have hperiod (j : ℕ) (hj : 0 < j) :
        (p ∣ Int.natAbs (Nat.fib (j + r - 1) * n + Nat.fib (j + r) * z)) ↔
          p ∣ Int.natAbs (Nat.fib (j - 1) * n + Nat.fib j * z) := by
      have hfirst := Nat.fib_add (j - 1) (r - 1)
      have hsecond := Nat.fib_add (j - 1) r
      have hshift :
          readout p (j - 1 + r) ((n : ZMod p), (z : ZMod p)) =
            (Nat.fib (r - 1) : ZMod p) * readout p (j - 1)
              ((n : ZMod p), (z : ZMod p)) := by
        change (Nat.fib (j - 1 + r) : ZMod p) * (n : ZMod p) +
            Nat.fib (j - 1 + r + 1) * (z : ZMod p) = _
        have hindex : j - 1 + (r - 1) + 1 + 1 = j - 1 + r + 1 := by omega
        rw [show j - 1 + r = j - 1 + (r - 1) + 1 by omega, hfirst,
          hindex, hsecond]
        simp only [Nat.cast_add, Nat.cast_mul]
        have hfib : (Nat.fib r : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).2 hzero
        have hsucc := Nat.fib_add_two (n := r - 1)
        rw [show r - 1 + 2 = r + 1 by omega] at hsucc
        rw [hsucc, hfib]
        have hpred : r - 1 + 1 = r := by omega
        rw [hpred, hfib]
        push_cast
        simp only [readout]
        simp [hfib]
        ring
      have hu (y : ZMod p) :
          (Nat.fib (r - 1) : ZMod p) * y = 0 ↔ y = 0 := by
        constructor
        · intro h
          exact hunit.mul_left_cancel (by simpa using h)
        · intro h
          simpa [h]
      constructor
      · intro h
        have hz1 := (hread (j + r) (by omega)).mpr h
        rw [show j + r - 1 = j - 1 + r by omega, hshift] at hz1
        have hz2 : readout p (j - 1) ((n : ZMod p), (z : ZMod p)) = 0 :=
          (hu _).mp hz1
        exact (hread j hj).mp hz2
      · intro h
        have hz2 := (hread j hj).mpr h
        have hz1 : readout p (j - 1 + r) ((n : ZMod p), (z : ZMod p)) = 0 := by
          rw [hshift]
          exact (hu _).mpr hz2
        have hz3 : readout p (j + r - 1) ((n : ZMod p), (z : ZMod p)) = 0 := by
          simpa [show j + r - 1 = j - 1 + r by omega] using hz1
        exact (hread (j + r) (by omega)).mp hz3
    have hgcd (a b : ℕ) (hab : p ∣ a ↔ p ∣ b) : Nat.gcd a p = Nat.gcd b p := by
      by_cases ha : p ∣ a
      · have hb : p ∣ b := hab.mp ha
        rw [Nat.gcd_eq_right_iff_dvd.mpr ha, Nat.gcd_eq_right_iff_dvd.mpr hb]
      · have hb : ¬p ∣ b := by intro hb; exact ha (hab.mpr hb)
        have hga : Nat.gcd a p = 1 := by
          rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right _ _) with h1 | h2
          · exact h1
          · exfalso
            exact ha ((Nat.gcd_eq_right_iff_dvd).mp h2)
        have hgb : Nat.gcd b p = 1 := by
          rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right _ _) with h1 | h2
          · exact h1
          · exfalso
            exact hb ((Nat.gcd_eq_right_iff_dvd).mp h2)
        rw [hga, hgb]
    unfold localGcd
    exact hgcd _ _ (hperiod k hk)
  have hsource (Q : ℕ) (hQ : 0 < Q) (n z : ℤ) : ∃ a b : ℕ,
      a < Q * p ∧ b < Q * p ∧
        ∀ k, 0 < k → sourceGcd (Q * p) a b k = Q * localGcd p n z k := by
    let u : ZMod p := 5 * (n : ZMod p) - 3 * (z : ZMod p)
    let v : ZMod p := -3 * (n : ZMod p) + 2 * (z : ZMod p)
    letI : NeZero p := ⟨Nat.ne_of_gt hp.pos⟩
    let a : ℕ := Q * u.val
    let b : ℕ := Q * v.val
    have hu_lt : u.val < p := ZMod.val_lt u
    have hv_lt : v.val < p := ZMod.val_lt v
    have ha : a < Q * p := by
      dsimp [a]
      exact Nat.mul_lt_mul_of_pos_left hu_lt hQ
    have hb : b < Q * p := by
      dsimp [b]
      exact Nat.mul_lt_mul_of_pos_left hv_lt hQ
    refine ⟨a, b, ha, hb, ?_⟩
    intro k hk
    have f3 : Nat.fib (k + 3) = 2 * Nat.fib (k - 1) + 3 * Nat.fib k := by
      have h0 := Nat.fib_add_two (n := k - 1)
      rw [show k - 1 + 2 = k + 1 by omega,
        show k - 1 + 1 = k by omega] at h0
      have h1 := Nat.fib_add_two (n := k)
      have h2 := Nat.fib_add_two (n := k + 1)
      rw [show k + 1 + 2 = k + 3 by omega] at h2
      rw [h2, h1, h0]
      omega
    have f4 : Nat.fib (k + 4) = 3 * Nat.fib (k - 1) + 5 * Nat.fib k := by
      have h0 := Nat.fib_add_two (n := k - 1)
      rw [show k - 1 + 2 = k + 1 by omega,
        show k - 1 + 1 = k by omega] at h0
      have h1 := Nat.fib_add_two (n := k)
      have h2 := Nat.fib_add_two (n := k + 1)
      rw [show k + 1 + 2 = k + 3 by omega] at h2
      have h3 := Nat.fib_add_two (n := k + 2)
      rw [show k + 2 + 2 = k + 4 by omega] at h3
      rw [h3, h2, h1, h0]
      omega
    have hstate :
        (Nat.fib (k + 3) : ZMod p) * u + (Nat.fib (k + 4) : ZMod p) * v =
          readout p (k - 1) ((n : ZMod p), (z : ZMod p)) := by
      simp only [f3, f4, u, v, readout]
      push_cast
      rw [show k - 1 + 1 = k by omega]
      ring
    have hval :
        ((Nat.fib (k + 3) * u.val + Nat.fib (k + 4) * v.val : ℕ) : ZMod p) =
          readout p (k - 1) ((n : ZMod p), (z : ZMod p)) := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val]
      simpa only [ZMod.cast_id] using hstate
    have hread :
        readout p (k - 1) ((n : ZMod p), (z : ZMod p)) = 0 ↔
          p ∣ Int.natAbs (Nat.fib (k - 1) * n + Nat.fib k * z) := by
      have hzmod : readout p (k - 1) ((n : ZMod p), (z : ZMod p)) =
          (((Nat.fib (k - 1) : ℤ) * n + (Nat.fib k : ℤ) * z : ℤ) : ZMod p) := by
        simp only [readout, Int.cast_add, Int.cast_mul, Int.cast_natCast]
        rw [show k - 1 + 1 = k by omega]
      rw [hzmod, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
    have hmod :
        p ∣ Nat.fib (k + 3) * u.val + Nat.fib (k + 4) * v.val ↔
          p ∣ Int.natAbs (Nat.fib (k - 1) * n + Nat.fib k * z) := by
      constructor
      · intro h
        have hz := (ZMod.natCast_eq_zero_iff _ _).2 h
        rw [hval] at hz
        exact hread.mp hz
      · intro h
        have hz := hread.mpr h
        exact (ZMod.natCast_eq_zero_iff _ _).1 (hval.symm ▸ hz)
    have hsource_value :
        Nat.fib (k + 3) * a + Nat.fib (k + 4) * b =
          Q * (Nat.fib (k + 3) * u.val + Nat.fib (k + 4) * v.val) := by
      dsimp [a, b]
      ring
    have hgcd (w : ℕ) : Nat.gcd (Q * w) (Q * p) = Q * Nat.gcd w p :=
      Nat.gcd_mul_left Q w p
    rw [sourceGcd, hsource_value, hgcd]
    unfold localGcd
    have hprime_gcd (m : ℕ) : Nat.gcd m p = p ↔ p ∣ m := by
      exact Nat.gcd_eq_right_iff_dvd
    have hprime_one (m : ℕ) (hnot : ¬p ∣ m) : Nat.gcd m p = 1 := by
      rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right _ _) with h1 | h2
      · exact h1
      · exfalso
        exact hnot ((Nat.gcd_eq_right_iff_dvd).mp h2)
    by_cases hdiv : p ∣ Nat.fib (k + 3) * u.val + Nat.fib (k + 4) * v.val
    · rw [(hprime_gcd _).2 hdiv, (hprime_gcd _).2 (hmod.mp hdiv)]
    · have hnot : ¬p ∣ Int.natAbs (Nat.fib (k - 1) * n + Nat.fib k * z) :=
        fun h => hdiv (hmod.mpr h)
      rw [hprime_one _ hdiv, hprime_one _ hnot]
  have hshift (n z : ℤ) (j m : ℕ) (hj : 0 < j) :
      localGcd p n z (j + m * r) = localGcd p n z j := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]
      rw [hshift_of_zero _ (by omega) n z]
      exact ih
  let phase (k : ℕ) : Fin r := ⟨(k - 1) % r, Nat.mod_lt _ hr⟩
  let C := S.image phase
  let profile (x : ZMod p × ZMod p) (j : Fin r) : ℕ :=
    if readout p j x = 0 then p else 1
  have hvalue (n z : ℤ) (j : Fin r) :
      localGcd p n z (j.val + 1) = profile ((n : ZMod p), (z : ZMod p)) j := by
    have hz : readout p j ((n : ZMod p), (z : ZMod p)) = 0 ↔
        p ∣ Int.natAbs (Nat.fib j.val * n + Nat.fib (j.val + 1) * z) := by
      have heq : readout p j ((n : ZMod p), (z : ZMod p)) =
          (((Nat.fib j.val : ℤ) * n + Nat.fib (j.val + 1) * z : ℤ) : ZMod p) := by
        simp [readout]
      rw [heq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
    dsimp [profile, localGcd]
    split_ifs with hzero
    · exact Nat.gcd_eq_right_iff_dvd.mpr (hz.mp hzero)
    · rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right
          (Int.natAbs (Nat.fib j.val * n + Nat.fib (j.val + 1) * z)) p) with hone | heq
      · exact hone
      · exact (hzero (hz.mpr (Nat.gcd_eq_right_iff_dvd.mp heq))).elim
  have hblock (n z : ℤ) (k : ℕ) (hk : 0 < k) :
      localGcd p n z k = profile ((n : ZMod p), (z : ZMod p)) (phase k) := by
    have hdecomp := Nat.mod_add_div (k - 1) r
    have heq : k = ((k - 1) % r + 1) + (k - 1) / r * r := by
      rw [Nat.mul_comm] at hdecomp
      omega
    calc
      localGcd p n z k = localGcd p n z
          (((k - 1) % r + 1) + (k - 1) / r * r) := congrArg (localGcd p n z) heq
      _ = localGcd p n z ((k - 1) % r + 1) := hshift n z _ _ (by omega)
      _ = profile ((n : ZMod p), (z : ZMod p)) (phase k) := hvalue n z (phase k)
  have hprofile (x y : ZMod p × ZMod p) (j : Fin r) :
      profile x j = profile y j ↔ (readout p j x = 0 ↔ readout p j y = 0) := by
    by_cases hx : readout p j x = 0 <;> by_cases hy : readout p j y = 0 <;>
      simp [profile, hx, hy, hp.ne_one, Ne.symm hp.ne_one]
  have hphase_card : C.card = A.card := by
    have himage : A = C.image (fun j : Fin r => (j.val + 1) % r) := by
      have hmod (k : ℕ) (hk : 0 < k) : ((k - 1) % r + 1) % r = k % r := by
        have h := Nat.add_mod (k - 1) 1 r
        rw [show k - 1 + 1 = k by omega] at h
        simpa only [Nat.add_mod, Nat.mod_mod] using h.symm
      ext j
      simp only [A, C, Finset.mem_image]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨phase k, ⟨k, hk, rfl⟩, hmod k (hS k hk)⟩
      · rintro ⟨jj, ⟨k, hk, rfl⟩, heq⟩
        exact ⟨k, hk, (hmod k (hS k hk)).symm.trans heq⟩
    have hinj : Function.Injective (fun j : Fin r => (j.val + 1) % r) := by
      intro i j hij
      have hm := Nat.ModEq.add_right_cancel' 1 hij
      change i.val % r = j.val % r at hm
      apply Fin.ext
      simpa only [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm
    rw [himage, Finset.card_image_of_injective _ hinj]
  have hdet (hT : T ≤ C.card) (x y : ZMod p × ZMod p)
      (hobs : ∀ j ∈ C, profile x j = profile y j) : ∀ j, profile x j = profile y j := by
    by_cases hfull : r = p + 1
    · have hlarge : r - 1 ≤ C.card := by simpa [T, hfull] using hT
      have hsmallzero (u v : ZMod p × ZMod p) (hu : u = (0, 0))
          (hv : v ≠ (0, 0)) (huv : ∀ j ∈ C, profile u j = profile v j) : False := by
        obtain ⟨jj, hjj⟩ := hfullhit hfull v hv
        have hsub : C ⊆ {jj} := by
          intro j hj
          have hz : readout p j v = 0 := (hprofile u v j).mp (huv j hj) |>.mp
            (by simp [hu, readout])
          have heq : j = jj := by
            by_contra hne
            exact hv (htwozero v j jj hne hz hjj)
          simpa using heq
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hc
        omega
      by_cases hx : x = (0, 0)
      · by_cases hy : y = (0, 0)
        · simp [hx, hy]
        · exact (hsmallzero x y hx hy hobs).elim
      by_cases hy : y = (0, 0)
      · exact (hsmallzero y x hy hx (fun j hj => (hobs j hj).symm)).elim
      obtain ⟨ii, hii⟩ := hfullhit hfull x hx
      obtain ⟨jj, hjj⟩ := hfullhit hfull y hy
      by_cases hij : ii = jj
      · intro j
        apply (hprofile x y j).mpr
        have huniq (u : ZMod p × ZMod p) (hu : u ≠ (0, 0))
            (hh : readout p ii u = 0) : readout p j u = 0 ↔ j = ii := by
          constructor
          · intro hz
            by_contra hne
            exact hu (htwozero u j ii hne hz hh)
          · rintro rfl
            exact hh
        exact (huniq x hx hii).trans (huniq y hy (hij.symm ▸ hjj)).symm
      · have hi : ii ∉ C := by
          intro hi
          have hz := (hprofile x y ii).mp (hobs ii hi) |>.mp hii
          exact hy (htwozero y ii jj hij hz hjj)
        have hj : jj ∉ C := by
          intro hj
          have hz := (hprofile x y jj).mp (hobs jj hj) |>.mpr hjj
          exact hx (htwozero x jj ii (Ne.symm hij) hz hii)
        have hc := Finset.card_le_card (Finset.subset_univ (insert ii (insert jj C)))
        have hi' : ii ∉ insert jj C := by simp [hi, hij]
        rw [Finset.card_insert_of_notMem hi', Finset.card_insert_of_notMem hj,
          Finset.card_univ, Fintype.card_fin] at hc
        omega
    · have hc : C = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simpa [T, hfull] using hT
      intro j
      exact hobs j (hc ▸ Finset.mem_univ j)
  have hcollision (hins : C.card < T) : ∃ x y : ZMod p × ZMod p,
      x ≠ (0, 0) ∧ y ≠ (0, 0) ∧
      (∀ j ∈ C, profile x j = profile y j) ∧
      ∃ j : Fin r, readout p j x = 0 ∧ readout p j y ≠ 0 := by
    have hTr : T ≤ r := by dsimp [T]; split_ifs <;> omega
    have hc : C.card < (Finset.univ : Finset (Fin r)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨jj, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    by_cases hfull : r = p + 1
    · have hc' : (insert jj C).card < (Finset.univ : Finset (Fin r)).card := by
        rw [Finset.card_insert_of_notMem hj, Finset.card_univ, Fintype.card_fin]
        have hT : T = r - 1 := by simp [T, hfull]
        omega
      obtain ⟨ii, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc'
      have hij : jj ≠ ii := by
        intro heq
        exact hi (Finset.mem_insert.mpr (Or.inl heq.symm))
      have hiC : ii ∉ C := fun h => hi (Finset.mem_insert_of_mem h)
      refine ⟨kernel jj, kernel ii, hkernel_ne jj, hkernel_ne ii, ?_,
        jj, hkernel_zero jj, ?_⟩
      · intro j hjC
        have hne1 : readout p j (kernel jj) ≠ 0 := fun h =>
          hj ((hkernel_exact j jj).mp h ▸ hjC)
        have hne2 : readout p j (kernel ii) ≠ 0 := fun h =>
          hiC ((hkernel_exact j ii).mp h ▸ hjC)
        simp [profile, hne1, hne2]
      · exact fun h => hij ((hkernel_exact jj ii).mp h)
    · obtain ⟨y, hy, hnever⟩ := hnohit (by omega)
      refine ⟨kernel jj, y, hkernel_ne jj, hy, ?_, jj, hkernel_zero jj, hnever jj⟩
      intro j hjC
      have hne : readout p j (kernel jj) ≠ 0 := fun h =>
        hj ((hkernel_exact j jj).mp h ▸ hjC)
      simp [profile, hne, hnever j]
  have hlift (x : ZMod p × ZMod p) :
      (((x.1.val : ℤ) : ZMod p), ((x.2.val : ℤ) : ZMod p)) = x := by
    ext <;> simp
  have hprimitive (x : ZMod p × ZMod p) (hx : x ≠ (0, 0)) :
      primitive p (x.1.val : ℤ) (x.2.val : ℤ) := by
    by_contra hbad
    simp only [primitive, not_or, not_not, Int.natAbs_natCast] at hbad
    apply hx
    apply Prod.ext
    · have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hbad.1
      simpa using hz
    · have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hbad.2
      simpa using hz
  have hwitness (hins : A.card < T) (Q : ℕ) (hQ : 0 < Q) :
      ∃ n z n' z' : ℤ, ∃ a b a' b' : ℕ,
        primitive p n z ∧ primitive p n' z' ∧
        a < Q * p ∧ b < Q * p ∧ a' < Q * p ∧ b' < Q * p ∧
        (∀ k, 0 < k → sourceGcd (Q * p) a b k = Q * localGcd p n z k ∧
          sourceGcd (Q * p) a' b' k = Q * localGcd p n' z' k) ∧
        (∀ k ∈ S, localGcd p n z k = localGcd p n' z' k ∧
          sourceGcd (Q * p) a b k = sourceGcd (Q * p) a' b' k) ∧
        ∀ B, ∃ t, B < t ∧ 0 < t ∧ t ∉ S ∧
          localGcd p n z t = p ∧ localGcd p n' z' t = 1 ∧
          sourceGcd (Q * p) a b t = Q * p ∧ sourceGcd (Q * p) a' b' t = Q ∧
          sourceGcd (Q * p) a' b' t = Q * p / p := by
    obtain ⟨x, y, hx, hy, hobs, jj, hxj, hyj⟩ := hcollision (hphase_card ▸ hins)
    let n : ℤ := x.1.val
    let z : ℤ := x.2.val
    let n' : ℤ := y.1.val
    let z' : ℤ := y.2.val
    have hxy (k : ℕ) (hk : k ∈ S) : localGcd p n z k = localGcd p n' z' k := by
      rw [hblock n z k (hS k hk), hblock n' z' k (hS k hk)]
      change profile (((x.1.val : ℤ) : ZMod p), ((x.2.val : ℤ) : ZMod p)) (phase k) =
        profile (((y.1.val : ℤ) : ZMod p), ((y.2.val : ℤ) : ZMod p)) (phase k)
      rw [hlift x, hlift y]
      exact hobs (phase k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    obtain ⟨a, b, ha, hb, hab⟩ := hsource Q hQ n z
    obtain ⟨a', b', ha', hb', hab'⟩ := hsource Q hQ n' z'
    refine ⟨n, z, n', z', a, b, a', b', hprimitive x hx, hprimitive y hy,
      ha, hb, ha', hb', fun k hk => ⟨hab k hk, hab' k hk⟩, ?_, ?_⟩
    · intro k hk
      exact ⟨hxy k hk, by rw [hab k (hS k hk), hab' k (hS k hk), hxy k hk]⟩
    · intro B
      let t := jj.val + 1 + (B + 1) * r
      have hB : B < t := by
        have hmul := Nat.le_mul_of_pos_right (B + 1) hr
        dsimp [t]
        omega
      have ht : 0 < t := by omega
      have hphase : phase t = jj := by
        apply Fin.ext
        change (t - 1) % r = jj.val
        have heq : t - 1 = jj.val + (B + 1) * r := by dsimp [t]; omega
        rw [heq]
        simp [Nat.add_mod, Nat.mod_eq_of_lt jj.isLt]
      have hlocal : localGcd p n z t = p ∧ localGcd p n' z' t = 1 := by
        rw [hblock n z t ht, hblock n' z' t ht, hphase]
        change profile (((x.1.val : ℤ) : ZMod p), ((x.2.val : ℤ) : ZMod p)) jj = p ∧
          profile (((y.1.val : ℤ) : ZMod p), ((y.2.val : ℤ) : ZMod p)) jj = 1
        rw [hlift x, hlift y]
        simp [profile, hxj, hyj]
      have hnot : t ∉ S := by
        intro hmem
        have heq := hxy t hmem
        rw [hlocal.1, hlocal.2] at heq
        exact hp.ne_one heq
      refine ⟨t, hB, ht, hnot, hlocal.1, hlocal.2, ?_, ?_, ?_⟩
      · rw [hab t ht, hlocal.1]
      · rw [hab' t ht, hlocal.2, Nat.mul_one]
      · rw [hab' t ht, hlocal.2, Nat.mul_one, Nat.mul_div_cancel Q hp.pos]
  have hsufficient (hT : T ≤ A.card) (n z n' z' : ℤ)
      (hobs : ∀ k ∈ S, localGcd p n z k = localGcd p n' z' k)
      (k : ℕ) (hk : 0 < k) : localGcd p n z k = localGcd p n' z' k := by
    rw [hblock n z k hk, hblock n' z' k hk]
    apply hdet (hphase_card ▸ hT)
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    rw [← hblock n z s (hS s hs), ← hblock n' z' s (hS s hs)]
    exact hobs s hs
  have hforward (a b k : ℕ) (hk : 0 < k) : sourceGcd p a b k =
      localGcd p (2 * (a : ℤ) + 3 * b) (3 * (a : ℤ) + 5 * b) k := by
    have f3 := Nat.fib_add (k - 1) 3
    have f4 := Nat.fib_add (k - 1) 4
    rw [show k - 1 + 3 + 1 = k + 3 by omega,
      show k - 1 + 1 = k by omega] at f3
    rw [show k - 1 + 4 + 1 = k + 4 by omega,
      show k - 1 + 1 = k by omega] at f4
    norm_num at f3 f4
    have heq : (Nat.fib (k - 1) : ℤ) * (2 * (a : ℤ) + 3 * b) +
        (Nat.fib k : ℤ) * (3 * (a : ℤ) + 5 * b) =
          ((Nat.fib (k + 3) * a + Nat.fib (k + 4) * b : ℕ) : ℤ) := by
      rw [f3, f4]
      push_cast
      ring
    simp only [sourceGcd, localGcd, heq, Int.natAbs_natCast]
  change (_ ↔ T ≤ A.card) ∧ (_ ↔ T ≤ A.card) ∧ _
  refine ⟨⟨?_, hsufficient⟩, ⟨?_, ?_⟩, hwitness⟩
  · intro hrecover
    by_contra hbad
    obtain ⟨n, z, n', z', a, b, a', b', _, _, _, _, _, _, _, hobs, hlate⟩ :=
      hwitness (by omega) 1 (by omega)
    obtain ⟨t, _, ht, _, hfirst, hsecond, _⟩ := hlate 0
    have heq := hrecover n z n' z' (fun k hk => (hobs k hk).1) t ht
    rw [hfirst, hsecond] at heq
    exact hp.ne_one heq
  · intro hrecover
    by_contra hbad
    obtain ⟨n, z, n', z', a, b, a', b', _, _, _, _, _, _, _, hobs, hlate⟩ :=
      hwitness (by omega) 1 (by omega)
    obtain ⟨t, _, ht, _, _, _, hfirst, hsecond, _⟩ := hlate 0
    have heq := hrecover a b a' b' (fun k hk => by simpa using (hobs k hk).2) t ht
    simp only [Nat.one_mul] at hfirst hsecond
    rw [hfirst, hsecond] at heq
    exact hp.ne_one heq
  · intro hT a b a' b' hobs k hk
    rw [hforward a b k hk, hforward a' b' k hk]
    apply hsufficient hT _ _ _ _ ?_ k hk
    intro s hs
    rw [← hforward a b s (hS s hs), ← hforward a' b' s (hS s hs)]
    exact hobs s hs

end D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
