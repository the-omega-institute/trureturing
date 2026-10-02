/- GID: D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimeGcdHorizon
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp prime gcd horizons for signed states, attained on bounded nonnegative sources. -/

import D5.S3.Arith.FibonacciAtomic.TimeSampling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon

open D5.S3.Arith.FibonacciAtomic.TimeSampling

/-- The actual recurrence observation of a nonnegative source. -/
def observation (k a b : ℕ) : ℕ := Nat.fib (k + 3) * a + Nat.fib (k + 4) * b

/-- The signed recurrence with initial state (n,z), including its time-zero value n. -/
def signedObservation (k : ℕ) (n z : ℤ) : ℤ :=
  if k = 0 then n else (Nat.fib (k - 1) : ℤ) * n + (Nat.fib k : ℤ) * z

/-- The prime horizon, including the full projective orbit case. -/
noncomputable def horizon (p : ℕ) : ℕ :=
  if zeroRank p = p + 1 then zeroRank p - 1 else zeroRank p

/-- The prefix determines every positive-time prime gcd for signed initial states
and actual nonnegative sources, with bounded actual sources attaining the horizon. -/
theorem sharp_prime_gcd_horizon (p : ℕ) (hp : p.Prime) :
    (∀ n z n' z' : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
        Nat.gcd (signedObservation k n z).natAbs p =
          Nat.gcd (signedObservation k n' z').natAbs p) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (signedObservation k n z).natAbs p =
          Nat.gcd (signedObservation k n' z').natAbs p) ∧
    (∀ a b c d : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
    (∃ a b c d : ℕ, a < p ∧ b < p ∧ c < p ∧ d < p ∧
      (∀ k : ℕ, 1 ≤ k → k < horizon p →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
      Nat.gcd (observation (horizon p) a b) p ≠
        Nat.gcd (observation (horizon p) c d) p) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let r := zeroRank p
  let B := horizon p
  let U : ZMod p × ZMod p → ZMod p × ZMod p := fun x => (x.2, x.1 + x.2)
  have hU : Function.Bijective U := by
    constructor
    · intro x z h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp [U] at h₁ h₂
      exact Prod.ext (add_right_cancel (h₁ ▸ h₂)) h₁
    · intro x
      exact ⟨(x.2 - x.1, x.1), by simp [U]⟩
  have hex : Set.Nonempty {t : ℕ | 0 < t ∧ p ∣ Nat.fib t} := by
    let C : ℕ × ℕ → ZMod p × ZMod p := fun x => (x.1, x.2)
    have hc : Function.Semiconj C (fun x : ℕ × ℕ => (x.2, x.1 + x.2)) U := by
      intro x
      simp [C, U]
    obtain ⟨t, ht, hreturn⟩ := hU.1.mem_periodicPts (0, 1)
    have hz : (Nat.fib t : ZMod p) = 0 := by
      have h := congrArg Prod.fst (hc.iterate_right t (0, 1))
      simpa [Nat.fib, C, hreturn.eq] using h
    exact ⟨t, ht, (ZMod.natCast_eq_zero_iff _ _).mp hz⟩
  have hr := Nat.sInf_mem hex
  have hrpos : 0 < r := hr.1
  have hrzero : p ∣ Nat.fib r := hr.2
  have hrmin : ∀ t, 0 < t → p ∣ Nat.fib t → r ≤ t :=
    fun t ht hz => Nat.sInf_le ⟨ht, hz⟩
  have hrthree : 3 ≤ r := by
    by_contra h
    have : r = 1 ∨ r = 2 := by omega
    have hbad : p ∣ 1 := by
      rcases this with h | h <;> simpa only [h, Nat.fib_one, Nat.fib_two] using hrzero
    exact hp.ne_one (Nat.dvd_one.mp hbad)
  have hentry (t : ℕ) : (Nat.fib t : ZMod p) = 0 ↔ r ∣ t := by
    rw [ZMod.natCast_eq_zero_iff]
    exact D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin
  let Q := readout p
  have hstep (t : ℕ) (x : ZMod p × ZMod p) : Q (t + 1) x = Q t (U x) := by
    simp only [Q, readout, U, Nat.fib_add_two, Nat.cast_add]
    ring
  have hiter (t : ℕ) (x : ZMod p × ZMod p) : Q t x = (U^[t] x).2 := by
    induction t generalizing x with
    | zero => simp [Q, readout]
    | succ t ih => rw [hstep, ih, Function.iterate_succ_apply]
  have hshift (s t : ℕ) (x : ZMod p × ZMod p) : Q (s + t) x = Q t (U^[s] x) := by
    rw [hiter, hiter, Nat.add_comm s t, Function.iterate_add_apply]
  have hzeropair (s t : ℕ) (x : ZMod p × ZMod p) (hst : s ≤ t)
      (hx : x ≠ 0) (hs : Q s x = 0) : Q t x = 0 ↔ r ∣ t - s := by
    have hu0 : U^[s] (0 : ZMod p × ZMod p) = 0 := by
      clear hst hs
      induction s with
      | zero => rfl
      | succ s ih => rw [Function.iterate_succ_apply', ih]; simp [U]
    have hz : U^[s] x ≠ 0 := by
      intro h
      exact hx ((hU.1.iterate s) (h.trans hu0.symm))
    have hs' : (U^[s] x).2 = 0 := (hiter s x).symm.trans hs
    have hfst : (U^[s] x).1 ≠ 0 := by
      intro h
      exact hz (Prod.ext h hs')
    have htshift := hshift s (t - s) x
    rw [Nat.add_sub_of_le hst] at htshift
    rw [htshift]
    simp only [Q, readout, hs', mul_zero, add_zero, mul_eq_zero, hfst, or_false]
    exact hentry (t - s)
  let K : ℕ → ZMod p × ZMod p := fun t => (Nat.fib (t + 1), -(Nat.fib t : ZMod p))
  have hK (t : ℕ) : K t ≠ 0 := by
    intro h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    have hfa : p ∣ Nat.fib (t + 1) := (ZMod.natCast_eq_zero_iff _ _).mp ha
    have hfb : p ∣ Nat.fib t := (ZMod.natCast_eq_zero_iff _ _).mp (neg_eq_zero.mp hb)
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hfb hfa (Nat.fib_coprime_fib_succ t)
  have hKzero (t : ℕ) : Q t (K t) = 0 := by
    dsimp [Q, readout, K]
    ring
  let direction : ZMod p × ZMod p → Option (ZMod p) :=
    fun x => if x.2 = 0 then none else some (x.1 / x.2)
  have hdirection (x z : ZMod p × ZMod p) (hx : x ≠ 0) (hz : z ≠ 0) :
      direction x = direction z ↔ x.1 * z.2 = z.1 * x.2 := by
    by_cases hb : x.2 = 0 <;> by_cases hd : z.2 = 0
    · simp [direction, hb, hd]
    · have ha : x.1 ≠ 0 := fun h => hx (Prod.ext h hb)
      simp [direction, hb, hd, ha]
    · have hc : z.1 ≠ 0 := fun h => hz (Prod.ext h hd)
      simp [direction, hb, hd, hc]
    · simp [direction, hb, hd, div_eq_div_iff hb hd]
  have hline (t : ℕ) (x : ZMod p × ZMod p) (hx : x ≠ 0) :
      direction x = direction (K t) ↔ Q t x = 0 := by
    rw [hdirection x (K t) hx (hK t)]
    dsimp [K, Q, readout]
    constructor <;> intro h <;> linear_combination -h
  let phases : Fin r → Option (ZMod p) := fun t => direction (K t.val)
  have hinj : Function.Injective phases := by
    intro s t h
    apply Fin.ext
    by_contra hne
    have hbad (s t : Fin r) (hlt : s.val < t.val) (heq : phases s = phases t) : False := by
      have hs : Q s.val (K t.val) = 0 := (hline s.val _ (hK t.val)).mp heq.symm
      have hd := (hzeropair s.val t.val (K t.val) hlt.le (hK t.val) hs).mp (hKzero t.val)
      have hle := Nat.le_of_dvd (by omega : 0 < t.val - s.val) hd
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hbad s t hlt h
    · exact hbad t s hgt h.symm
  have hcard : Fintype.card (Option (ZMod p)) = p + 1 := by simp
  have hrbound : r ≤ p + 1 := by
    have h := Fintype.card_le_of_injective phases hinj
    simpa [hcard] using h
  have hB : B = if r = p + 1 then r - 1 else r := rfl
  have hBtwo : 2 ≤ B := by split_ifs at hB <;> omega
  have hBr : B ≤ r := by split_ifs at hB <;> omega
  have hfull (h : r = p + 1) : Function.Surjective phases :=
    ((Fintype.bijective_iff_injective_and_card phases).mpr
      ⟨hinj, by simpa [hcard] using h⟩).2
  have hperiod (t : ℕ) (x : ZMod p × ZMod p) : Q (t + r) x = 0 ↔ Q t x = 0 := by
    have hfr : (Nat.fib r : ZMod p) = 0 := (hentry r).mpr (dvd_refl r)
    have hfr1 : (Nat.fib (r + 1) : ZMod p) ≠ 0 := by
      intro h
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hrzero
        ((ZMod.natCast_eq_zero_iff _ _).mp h) (Nat.fib_coprime_fib_succ r)
    rw [hshift]
    simp only [Q, readout, hfr, zero_mul, zero_add, mul_eq_zero, hfr1, false_or]
    rw [← hiter]
    rfl
  have hmod (t : ℕ) (x : ZMod p × ZMod p) : Q t x = 0 ↔ Q (t % r) x = 0 := by
    have hmul (s j : ℕ) : Q (s + r * j) x = 0 ↔ Q s x = 0 := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, hperiod, ih]
    have h := hmul (t % r) (t / r)
    rwa [Nat.mod_add_div] at h
  have hsmall (s t : ℕ) (hs : s < r) (ht : t < r) : Q s (K t) = 0 ↔ s = t := by
    rw [← hline s (K t) (hK t)]
    constructor
    · intro h
      exact congrArg Fin.val (hinj (show phases ⟨s, hs⟩ = phases ⟨t, ht⟩ from h.symm))
    · rintro rfl
      rfl
  have hsame (x z : ZMod p × ZMod p) (hx : x ≠ 0) (hz : z ≠ 0)
      (h : direction x = direction z) (t : ℕ) : Q t x = 0 ↔ Q t z = 0 := by
    rw [← hline t x hx, ← hline t z hz, h]
  have hupper (x z : ZMod p × ZMod p)
      (h : ∀ t : ℕ, t < B → (Q t x = 0 ↔ Q t z = 0)) :
      ∀ t : ℕ, Q t x = 0 ↔ Q t z = 0 := by
    have hdetect (x z : ZMod p × ZMod p) (hx : x = 0)
        (h : ∀ t : ℕ, t < B → (Q t x = 0 ↔ Q t z = 0)) : z = 0 := by
      have h₀ := (h 0 (by omega)).mp (by simp [hx, Q, readout])
      have h₁ := (h 1 (by omega)).mp (by simp [hx, Q, readout])
      have hb : z.2 = 0 := by simpa [Q, readout] using h₀
      exact Prod.ext (by simpa [Q, readout, hb] using h₁) hb
    by_cases hx : x = 0
    · have hz := hdetect x z hx h
      simp [hx, hz]
    by_cases hz : z = 0
    · exact (hx (hdetect z x hz (fun t ht => (h t ht).symm))).elim
    by_cases hhit : ∃ t : ℕ, t < B ∧ Q t x = 0
    · obtain ⟨t, ht, htx⟩ := hhit
      have htz := (h t ht).mp htx
      have heq := ((hline t x hx).mpr htx).trans ((hline t z hz).mpr htz).symm
      exact hsame x z hx hz heq
    · have hnx (t : ℕ) (ht : t < B) : Q t x ≠ 0 := fun hz => hhit ⟨t, ht, hz⟩
      have hnz (t : ℕ) (ht : t < B) : Q t z ≠ 0 := fun hz => hnx t ht ((h t ht).mpr hz)
      by_cases hfullrank : r = p + 1
      · obtain ⟨s, hs⟩ := hfull hfullrank (direction x)
        obtain ⟨t, ht⟩ := hfull hfullrank (direction z)
        have hsB : B ≤ s.val := by
          by_contra hlt
          exact hnx s.val (by omega) ((hline s.val x hx).mp hs.symm)
        have htB : B ≤ t.val := by
          by_contra hlt
          exact hnz t.val (by omega) ((hline t.val z hz).mp ht.symm)
        have hst : s = t := by apply Fin.ext; rw [hfullrank] at hB; simp at hB; omega
        exact hsame x z hx hz (hs.symm.trans (hst ▸ ht))
      · have hBeq : B = r := by simpa [hfullrank] using hB
        intro t
        have hlt : t % r < B := by rw [hBeq]; exact Nat.mod_lt t hrpos
        rw [hmod t x, hmod t z]
        exact iff_of_false (hnx _ hlt) (hnz _ hlt)
  have hlower : ∃ x z : ZMod p × ZMod p,
      (∀ t : ℕ, t + 1 < B → (Q t x = 0 ↔ Q t z = 0)) ∧
      ¬ (Q (B - 1) x = 0 ↔ Q (B - 1) z = 0) := by
    by_cases hfullrank : r = p + 1
    · have hBeq : B = r - 1 := by rw [if_pos hfullrank] at hB; exact hB
      refine ⟨K (B - 1), K (r - 1), ?_, ?_⟩
      · intro t ht
        rw [hsmall t (B - 1) (by omega) (by omega),
          hsmall t (r - 1) (by omega) (by omega)]
        exact iff_of_false (by omega) (by omega)
      · rw [hsmall (B - 1) (B - 1) (by omega) (by omega),
          hsmall (B - 1) (r - 1) (by omega) (by omega)]
        simp only [true_iff]
        omega
    · have hBeq : B = r := by simpa [hfullrank] using hB
      have hns : ¬ Function.Surjective phases := by
        intro h
        have hle := Fintype.card_le_of_surjective phases h
        simp only [hcard, Fintype.card_fin] at hle
        omega
      obtain ⟨q, hq⟩ := not_forall.mp hns
      have hreps : ∀ q : Option (ZMod p), ∃ z : ZMod p × ZMod p,
          z ≠ 0 ∧ direction z = q := by
        intro q
        cases q with
        | none => exact ⟨(1, 0), by simp, by simp [direction]⟩
        | some a => exact ⟨(a, 1), by simp, by simp [direction]⟩
      obtain ⟨z, hz, hdir⟩ := hreps q
      have hnz (t : ℕ) : Q t z ≠ 0 := by
        intro h
        have hm := (hmod t z).mp h
        have heq := (hline (t % r) z hz).mpr hm
        exact hq ⟨⟨t % r, Nat.mod_lt t hrpos⟩, heq.symm.trans hdir⟩
      refine ⟨K (r - 1), z, ?_, ?_⟩
      · intro t ht
        rw [hsmall t (r - 1) (by omega) (by omega)]
        exact iff_of_false (by omega) (hnz t)
      · rw [hBeq]
        exact fun h => hnz (r - 1) (h.mp (hKzero (r - 1)))
  let source : ℕ → ℕ → ZMod p × ZMod p :=
    fun a b => (2 * a + 3 * b, 3 * a + 5 * b)
  have hactual (k a b : ℕ) (hk : 1 ≤ k) :
      Q (k - 1) (source a b) = (observation k a b : ZMod p) := by
    have hC : U^[4] ((a : ZMod p), (b : ZMod p)) = source a b := by
      simp [Function.iterate_succ_apply', U, source]
      constructor <;> ring
    rw [← hC, ← hshift]
    have heq : 4 + (k - 1) = k + 3 := by omega
    rw [heq]
    simp [Q, readout, observation, Nat.add_assoc]
  have hgcd (a b : ℕ) : Nat.gcd a p = Nat.gcd b p ↔
      ((a : ZMod p) = 0 ↔ (b : ZMod p) = 0) := by
    have hg (a : ℕ) : Nat.gcd a p = if p ∣ a then p else 1 := by
      by_cases h : p ∣ a
      · simp [h, Nat.gcd_eq_right h]
      · simp [h, ((hp.coprime_iff_not_dvd).mpr h).symm.gcd_eq_one]
    rw [hg, hg, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
    by_cases ha : p ∣ a <;> by_cases hb : p ∣ b <;> simp [ha, hb, hp.ne_one, hp.ne_one.symm]
  have hintzero (a : ℤ) : (a.natAbs : ZMod p) = 0 ↔ (a : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff, CharP.intCast_eq_zero_iff (ZMod p) p,
      Int.natCast_dvd]
  have hsignedgcd (a b : ℤ) : Nat.gcd a.natAbs p = Nat.gcd b.natAbs p ↔
      ((a : ZMod p) = 0 ↔ (b : ZMod p) = 0) := by
    rw [hgcd, hintzero, hintzero]
  have hsigned (k : ℕ) (n z : ℤ) (hk : 1 ≤ k) :
      Q (k - 1) ((n : ZMod p), (z : ZMod p)) =
        (signedObservation k n z : ZMod p) := by
    simp [Q, readout, signedObservation, show k ≠ 0 by omega,
      Nat.sub_add_cancel hk]
  have hrealize (x : ZMod p × ZMod p) : ∃ a b : ℕ,
      a < p ∧ b < p ∧ source a b = x := by
    let a : ZMod p := 5 * x.1 - 3 * x.2
    let b : ZMod p := -3 * x.1 + 2 * x.2
    refine ⟨a.val, b.val, ZMod.val_lt a, ZMod.val_lt b, ?_⟩
    simp only [source, ZMod.natCast_zmod_val]
    dsimp [a, b]
    apply Prod.ext <;> dsimp <;> ring
  constructor
  · intro n z n' z' h k hk
    apply (hsignedgcd _ _).mpr
    rw [← hsigned k n z hk, ← hsigned k n' z' hk]
    apply hupper
    intro t ht
    have hh := (hsignedgcd _ _).mp (h (t + 1) (by omega) (by omega))
    simpa only [← hsigned (t + 1) n z (by omega),
      ← hsigned (t + 1) n' z' (by omega), Nat.add_sub_cancel] using hh
  constructor
  · intro a b c d h k hk
    apply (hgcd _ _).mpr
    rw [← hactual k a b hk, ← hactual k c d hk]
    apply hupper
    intro t ht
    have hh := (hgcd _ _).mp (h (t + 1) (by omega) (by omega))
    simpa only [← hactual (t + 1) a b (by omega),
      ← hactual (t + 1) c d (by omega), Nat.add_sub_cancel] using hh
  · obtain ⟨x, z, hprefix, hlast⟩ := hlower
    obtain ⟨a, b, ha, hb, hab⟩ := hrealize x
    obtain ⟨c, d, hc, hd, hcd⟩ := hrealize z
    refine ⟨a, b, c, d, ha, hb, hc, hd, ?_, ?_⟩
    · intro k hk hkb
      apply (hgcd _ _).mpr
      rw [← hactual k a b hk, ← hactual k c d hk, hab, hcd]
      exact hprefix (k - 1) (by omega)
    · intro h
      apply hlast
      have hh := (hgcd _ _).mp h
      rw [← hactual B a b (by omega), ← hactual B c d (by omega), hab, hcd] at hh
      exact hh

#print axioms sharp_prime_gcd_horizon

end D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
