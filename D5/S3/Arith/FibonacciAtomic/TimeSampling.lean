/- GID: D5/S3/Arith/FibonacciAtomic/TimeSampling
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TimeSampling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The least prime Fibonacci zero rank is the sharp pairwise recovery capacity. -/

import D5.S3.Arith.FibonacciRank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.TimeSampling

/-- The second coordinate after the indicated number of Fibonacci steps. -/
def readout (n t : ℕ) (x : ZMod n × ZMod n) : ZMod n :=
  Nat.fib t * x.1 + Nat.fib (t + 1) * x.2

/-- Every two distinct labeled observations recover the entire source state. -/
def PairwiseRecovery (n : ℕ) (T : Finset ℕ) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, s < t →
    Function.Injective (fun x : ZMod n × ZMod n => (readout n s x, readout n t x))

/-- Least positive Fibonacci zero index; the infimum is zero if there is no such index. -/
noncomputable def zeroRank (p : ℕ) : ℕ := sInf {d : ℕ | 0 < d ∧ p ∣ Nat.fib d}

/-- The least zero rank among the prime divisors of a modulus. -/
noncomputable def recoveryLimit (n : ℕ) : ℕ :=
  sInf (zeroRank '' {p : ℕ | p.Prime ∧ p ∣ n})

/-- The exact maximum is attained by consecutive time labels, for every nontrivial modulus. -/
theorem pairwise_recovery_maximum (n : ℕ) (hn : 2 ≤ n) :
    PairwiseRecovery n (Finset.range (recoveryLimit n)) ∧
      ∀ T : Finset ℕ, PairwiseRecovery n T → T.card ≤ recoveryLimit n := by
  classical
  have hn0 : n ≠ 0 := by omega
  let : NeZero n := ⟨hn0⟩
  have ranks : ∀ p : ℕ, p.Prime →
      0 < zeroRank p ∧ p ∣ Nat.fib (zeroRank p) ∧
        ∀ d, 0 < d → p ∣ Nat.fib d → zeroRank p ≤ d := by
    intro p hp
    let : NeZero p := ⟨hp.ne_zero⟩
    let U : ZMod p × ZMod p → ZMod p × ZMod p := fun x => (x.2, x.1 + x.2)
    have hi : Function.Injective U := by
      intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp [U] at h₁ h₂
      exact Prod.ext (add_right_cancel (h₁ ▸ h₂)) h₁
    let C : ℕ × ℕ → ZMod p × ZMod p := fun x => (x.1, x.2)
    have hc : Function.Semiconj C (fun x : ℕ × ℕ => (x.2, x.1 + x.2)) U := by
      intro x
      simp [C, U]
    obtain ⟨d, hd, hreturn⟩ := hi.mem_periodicPts (0, 1)
    have hz : (Nat.fib d : ZMod p) = 0 := by
      have h := congrArg Prod.fst (hc.iterate_right d (0, 1))
      simpa [Nat.fib, C, hreturn.eq] using h
    have hex : Set.Nonempty {d : ℕ | 0 < d ∧ p ∣ Nat.fib d} :=
      ⟨d, hd, (ZMod.natCast_eq_zero_iff _ _).mp hz⟩
    have hm := Nat.sInf_mem hex
    exact ⟨hm.1, hm.2, fun d hd hz => Nat.sInf_le ⟨hd, hz⟩⟩
  have hprime : Set.Nonempty {p : ℕ | p.Prime ∧ p ∣ n} :=
    ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
  obtain ⟨p, ⟨hp, hpn⟩, hpr⟩ := Nat.sInf_mem (hprime.image zeroRank)
  have hlim : ∀ q : ℕ, q.Prime → q ∣ n → recoveryLimit n ≤ zeroRank q := by
    intro q hq hqn
    exact Nat.sInf_le ⟨q, ⟨hq, hqn⟩, rfl⟩
  have hpRank := ranks p hp
  have hpos : 0 < recoveryLimit n := by
    change 0 < sInf (zeroRank '' {p : ℕ | p.Prime ∧ p ∣ n})
    rw [← hpr]
    exact hpRank.1
  let U : ZMod n × ZMod n → ZMod n × ZMod n := fun x => (x.2, x.1 + x.2)
  have hU : Function.Bijective U := by
    constructor
    · intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp [U] at h₁ h₂
      exact Prod.ext (add_right_cancel (h₁ ▸ h₂)) h₁
    · intro x
      exact ⟨(x.2 - x.1, x.1), by simp [U]⟩
  have hstep (t : ℕ) (x : ZMod n × ZMod n) :
      readout n (t + 1) x = readout n t (U x) := by
    simp only [readout, U, Nat.fib_add_two, Nat.cast_add]
    ring
  have hiter (t : ℕ) (x : ZMod n × ZMod n) :
      readout n t x = (U^[t] x).2 := by
    induction t generalizing x with
    | zero => simp [readout]
    | succ t ih =>
      rw [hstep, ih, Function.iterate_succ_apply]
  have hshift (s d : ℕ) (x : ZMod n × ZMod n) :
      readout n (s + d) x = readout n d (U^[s] x) := by
    rw [hiter, hiter, Nat.add_comm s d, Function.iterate_add_apply]
  have hpair (s t : ℕ) (hst : s ≤ t) :
      Function.Injective (fun x : ZMod n × ZMod n =>
        (readout n s x, readout n t x)) ↔ n.Coprime (Nat.fib (t - s)) := by
    let Q : ZMod n × ZMod n → ZMod n × ZMod n := fun x =>
      (x.2, (Nat.fib (t - s) : ZMod n) * x.1 + Nat.fib (t - s + 1) * x.2)
    have hcoords (x : ZMod n × ZMod n) :
        (readout n s x, readout n t x) = Q (U^[s] x) := by
      have hs := hshift s (t - s) x
      rw [Nat.add_sub_of_le hst] at hs
      apply Prod.ext
      · exact hiter s x
      · exact hs
    have htri : Function.Injective Q ↔ IsUnit (Nat.fib (t - s) : ZMod n) := by
      constructor
      · intro h
        have hm : Function.Injective (fun a : ZMod n => (Nat.fib (t - s) : ZMod n) * a) := by
          intro a b hab
          have hab' : Q (a, 0) = Q (b, 0) := by simpa [Q] using hab
          exact congrArg Prod.fst (h hab')
        exact IsLeftRegular.isUnit_of_finite hm
      · intro h x y hxy
        have h₁ : x.2 = y.2 := congrArg Prod.fst hxy
        have h₂ := congrArg Prod.snd hxy
        dsimp [Q] at h₂
        rw [h₁] at h₂
        exact Prod.ext (h.mul_left_cancel (add_right_cancel h₂)) h₁
    rw [Nat.coprime_comm, ← ZMod.isUnit_iff_coprime]
    rw [← htri]
    constructor
    · intro h x y hxy
      obtain ⟨a, rfl⟩ := hU.surjective.iterate s x
      obtain ⟨b, rfl⟩ := hU.surjective.iterate s y
      exact congrArg (U^[s]) (h (by simpa only [hcoords] using hxy))
    · intro h x y hxy
      exact hU.injective.iterate s (h (by simpa only [hcoords] using hxy))
  constructor
  · intro s hs t ht hst
    apply (hpair s t hst.le).mpr
    by_contra hbad
    obtain ⟨q, hq, hqn, hqf⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
    have hsmall : t - s < recoveryLimit n := by
      have ht' := Finset.mem_range.mp ht
      omega
    have hzero := (ranks q hq).2.2 (t - s) (by omega) hqf
    exact (not_lt_of_ge ((hlim q hq hqn).trans hzero)) hsmall
  · intro T hT
    have hinj : Set.InjOn (fun t : ℕ => t % zeroRank p) (T : Set ℕ) := by
      intro s hs t ht heq
      by_contra hne
      have hbad (a b : ℕ) (ha : a ∈ T) (hb : b ∈ T) (hab : a < b)
          (hmod : a % zeroRank p = b % zeroRank p) : False := by
        have hd : zeroRank p ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hmod
        have hf : p ∣ Nat.fib (b - a) :=
          (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
            hpRank.1 hpRank.2.1 hpRank.2.2).mpr hd
        exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpn hf
          ((hpair a b hab.le).mp (hT a ha b hb hab))
      rcases lt_or_gt_of_ne hne with hst | hts
      · exact hbad s t hs ht hst heq
      · exact hbad t s ht hs hts heq.symm
    have hc : T.card ≤ (Finset.range (zeroRank p)).card :=
      Finset.card_le_card_of_injOn (fun t : ℕ => t % zeroRank p)
        (fun t _ => Finset.mem_range.mpr (Nat.mod_lt t hpRank.1)) hinj
    change T.card ≤ sInf (zeroRank '' {p : ℕ | p.Prime ∧ p ∣ n})
    simpa only [Finset.card_range, hpr] using hc

end D5.S3.Arith.FibonacciAtomic.TimeSampling
