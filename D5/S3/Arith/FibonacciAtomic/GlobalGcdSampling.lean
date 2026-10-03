/- GID: D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GlobalGcdSampling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Affine child decoding identifies gcd futures and preserves bounded collisions. -/
import D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
import D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Algebra.GCDMonoid.Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
open D5.S3.Arith.FibonacciAtomic.TimeSampling
open D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity observe residue)
def signedValue (k : ℕ) (x : ℤ × ℤ) : ℤ :=
  Nat.fib (k - 1) * x.1 + Nat.fib k * x.2
def Primitive (p : ℕ) (x : ℤ × ℤ) : Prop :=
  ¬ (p : ℤ) ∣ x.1 ∨ ¬ (p : ℤ) ∣ x.2
def gcdValue (H k : ℕ) (x : ℤ × ℤ) : ℕ :=
  Nat.gcd (signedValue k x).natAbs H
def actualGcd (H k : ℕ) (v : ℕ × ℕ) : ℕ :=
  Nat.gcd (quantity (step^[k] v)) H
def cappedContent (p e : ℕ) (x : ℤ × ℤ) : ℕ :=
  Nat.gcd (Nat.gcd x.1.natAbs x.2.natAbs) (p ^ e)
noncomputable def rootBase (p e t : ℕ) (x : ℤ × ℤ) : ZMod p :=
  (Nat.fib (zeroRank (p ^ (e - 1)) - 1) : ZMod p) *
    ((signedValue (t + 1) x / (p : ℤ) ^ (e - 1) : ℤ) : ZMod p)
noncomputable def rootSlope (p e t : ℕ) (x : ℤ × ℤ) : ZMod p :=
  (Nat.fib (zeroRank (p ^ (e - 1))) / p ^ (e - 1) : ℕ) *
    (signedValue (t + 2) x : ZMod p)
noncomputable def queryChildren (p e t : ℕ) (S : Finset ℕ) : Finset (ZMod p) := by
  classical
  exact ((Finset.range p).image fun j : ℕ => (j : ZMod p)).filter fun a => ∃ k ∈ S,
    (k - 1) % zeroRank (p ^ e) =
      (t + a.val * zeroRank (p ^ (e - 1))) % zeroRank (p ^ e)
noncomputable def D (p e : ℕ) (S : Finset ℕ) : Prop :=
  if e = 1 then
    (if zeroRank p = p + 1 then zeroRank p - 1 else zeroRank p) ≤
      (S.image (fun k => k % zeroRank p)).card
  else if zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) then
    ∀ t < zeroRank (p ^ e), ∃ k ∈ S, (k - 1) % zeroRank (p ^ e) = t
  else ∀ t < zeroRank (p ^ (e - 1)), p - 1 ≤ (queryChildren p e t S).card
def Identifies {A : Type} (read : ℕ → A → ℕ) (S : Finset ℕ) : Prop :=
  ∀ x y : A, (∀ k ∈ S, read k x = read k y) →
    ∀ k : ℕ, 0 < k → read k x = read k y
def IdentifiesOn {A : Type} (domain : A → Prop) (read : ℕ → A → ℕ)
    (S : Finset ℕ) : Prop :=
  ∀ x y : A, domain x → domain y → (∀ k ∈ S, read k x = read k y) →
    ∀ k : ℕ, 0 < k → read k x = read k y
theorem sparse_gcd_sampling :
  let collisionLaw (p : ℕ) : Prop :=
    ∀ e : ℕ, 1 ≤ e → ∀ S : Finset ℕ, (∀ k ∈ S, 0 < k) → ¬ D p e S →
    ∃ x y : ℤ × ℤ, Primitive p x ∧ Primitive p y ∧
      (∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) ∧
      ∀ Q : ℕ, 0 < Q → ∃ v w : ℕ × ℕ, v.1 < Q * p ^ e ∧ v.2 < Q * p ^ e ∧
        w.1 < Q * p ^ e ∧ w.2 < Q * p ^ e ∧
        (¬ p ∣ Q → Primitive p ((v.1 : ℤ), (v.2 : ℤ)) ∧
          Primitive p ((w.1 : ℤ), (w.2 : ℤ))) ∧
        (∀ k : ℕ, 0 < k → actualGcd (Q * p ^ e) k v =
        Q * gcdValue (p ^ e) k x ∧ actualGcd (Q * p ^ e) k w = Q * gcdValue (p ^ e) k y) ∧
        (∀ k ∈ S, actualGcd (Q * p ^ e) k v = actualGcd (Q * p ^ e) k w) ∧
        ∀ B : ℕ, ∃ k : ℕ, B < k ∧ 0 < k ∧ k ∉ S ∧ gcdValue (p ^ e) k x = p ^ e ∧
          gcdValue (p ^ e) k y = p ^ (e - 1) ∧ actualGcd (Q * p ^ e) k v = Q * p ^ e ∧
          actualGcd (Q * p ^ e) k w = Q * p ^ (e - 1);
  let localLaw (p : ℕ) : Prop :=
    collisionLaw p ∧
    (∀ e : ℕ, 1 ≤ e → ∀ S : Finset ℕ, ∀ hS : S.Nonempty, (∀ k ∈ S, 0 < k) →
      (∃ s ∈ S, ∃ t ∈ S, s % zeroRank p ≠ t % zeroRank p) → ∀ x : ℤ × ℤ,
        (S.image (fun k => gcdValue (p ^ e) k x)).min' (hS.image _) = cappedContent p e x) ∧
    (∀ e : ℕ, 2 ≤ e → ∀ S : Finset ℕ, D p e S → ∀ j : ℕ, 1 ≤ j → j < e →
      ∀ a b : ZMod (zeroRank (p ^ j)), ∃ k ∈ S,
        ((k - 1 : ℕ) : ZMod (zeroRank (p ^ j))) + a = b) ∧
    (∀ e : ℕ, 1 ≤ e → ∀ S : Finset ℕ, (∀ k ∈ S, 0 < k) → List.TFAE
      [D p e S, D p e S ∧ ∀ j : ℕ, 1 ≤ j → j < e → D p j S,
        IdentifiesOn (Primitive p) (gcdValue (p ^ e)) S,
        Identifies (gcdValue (p ^ e)) S, Identifies (actualGcd (p ^ e)) S,
        IdentifiesOn (fun v : ℕ × ℕ => Primitive p ((v.1 : ℤ), (v.2 : ℤ)))
          (actualGcd (p ^ e)) S]) ∧
    (∀ e : ℕ, 1 ≤ e → ∀ S : Finset ℕ, (∀ k ∈ S, 0 < k) → ¬ D p e S →
      ∀ H : ℕ, 0 < H → p ^ e ∣ H → ¬ p ^ (e + 1) ∣ H → ¬ p ∣ H / p ^ e ∧
      ∃ v w : ℕ × ℕ, v.1 < H ∧ v.2 < H ∧
        w.1 < H ∧ w.2 < H ∧ (∀ k ∈ S, actualGcd H k v = actualGcd H k w) ∧
        ∀ B : ℕ, ∃ k : ℕ, B < k ∧ 0 < k ∧ k ∉ S ∧
          actualGcd H k v = H ∧ actualGcd H k w = H / p) ∧
    (∀ e : ℕ, 1 ≤ e → ∀ S : Finset ℕ, (∀ k ∈ S, 0 < k) → D p e S →
      ∃ hS : S.Nonempty, (∃ s ∈ S, ∃ t ∈ S, s % zeroRank p ≠ t % zeroRank p) ∧
        ∀ x : ℤ × ℤ, (S.image (fun k => gcdValue (p ^ e) k x)).min' (hS.image _) =
          cappedContent p e x);
    (∀ p : ℕ, p.Prime → localLaw p ∧
      (∀ e : ℕ, 2 ≤ e → ∀ t : ℕ, ∀ x : ℤ × ℤ,
      (p : ℤ) ^ (e - 1) ∣ signedValue (t + 1) x → ∀ j : ℕ,
      ((p : ℤ) ^ e ∣ signedValue (t + 1 + j * zeroRank (p ^ (e - 1))) x ↔
        rootBase p e t x + (j : ZMod p) * rootSlope p e t x = 0))) ∧
    (∀ H : ℕ, 0 < H → ∀ S : Finset ℕ, (∀ k ∈ S, 0 < k) →
      (Identifies (actualGcd H) S ↔ ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e →
        p ^ e ∣ H → ¬ p ^ (e + 1) ∣ H → D p e S)) ∧
    (∀ k : ℕ, ∀ v : ℕ × ℕ, actualGcd 1 k v = 1) ∧
    (∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e → ∀ S : Finset ℕ,
      (∀ k ∈ S, 0 < k) → D p e S → ∃ hS : S.Nonempty,
      ∀ v : ℕ × ℕ, (S.image (fun k => actualGcd (p ^ e) k v)).min' (hS.image _) =
        Nat.gcd (Nat.gcd v.1 v.2) (p ^ e)) := by
  intro collisionLaw localLaw
  classical
  let U {A : Type} [Add A] (x : A × A) : A × A := (x.2, x.1 + x.2)
  have hbij {A : Type} [AddCommGroup A] : Function.Bijective (U (A := A)) := by
    exact ((Equiv.prodComm A A).trans
      (Equiv.prodShear (Equiv.refl A) (fun a => Equiv.addRight a))).bijective
  have hiter {A : Type} [CommSemiring A] (t : ℕ) (x : A × A) :
      (U^[t] x).2 = (Nat.fib t : A) * x.1 + (Nat.fib (t + 1) : A) * x.2 := by
    induction t generalizing x with
    | zero => simp [U]
    | succ t ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [U, Nat.fib_add_two, Nat.cast_add]
      ring
  have hfirst {A : Type} [CommSemiring A] (t : ℕ) (ht : 0 < t) (x : A × A) :
      (U^[t] x).1 = (Nat.fib (t - 1) : A) * x.1 + (Nat.fib t : A) * x.2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [Function.iterate_succ_apply', show (s + 1) - 1 = s by omega]
    exact hiter s x
  have hmatrix {A : Type} [CommSemiring A] (r : ℕ) (hr : 0 < r) (x : A × A) :
      U^[r] x = (Nat.fib (r - 1) * x.1 + Nat.fib r * x.2,
        Nat.fib (r - 1) * x.2 + Nat.fib r * (x.1 + x.2)) := by
    apply Prod.ext (hfirst r hr x)
    rw [hiter, Nat.fib_add_one hr.ne']
    push_cast
    ring
  have hbridge := GraftAffineClosure.result.2 1 (by omega) (0, 0)
  have htime := hbridge.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsource (k : ℕ) (v : ℕ × ℕ) :
      quantity (step^[k] v) = Nat.fib (k + 3) * v.1 + Nat.fib (k + 4) * v.2 := by
    have hh := htime k v
    rw [(hbridge.2.2.2.2.2.2.2.2.2.2.2.1 v).1,
      ← Function.iterate_add_apply] at hh
    exact hh.symm.trans (hfirst (k + 4) (by omega) v)
  have hnatural (k : ℕ) (v : ℕ × ℕ) (hk : 0 < k) :
      (quantity (A := ℕ) (step^[k] v) : ℤ) = signedValue k ((observe v).1, (observe v).2) := by
    simpa [signedValue] using congrArg (Nat.cast : ℕ → ℤ)
      ((hfirst k hk (observe v)).symm.trans (htime k v)).symm
  have hactual (H k : ℕ) (v : ℕ × ℕ) (hk : 0 < k) :
      actualGcd H k v = gcdValue H k ((observe v).1, (observe v).2) := by
    simp only [gcdValue, ← hnatural k v hk, Int.natAbs_natCast, actualGcd]
  have hscale (Q k : ℕ) (v : ℕ × ℕ) :
      quantity (step^[k] (Q * v.1, Q * v.2)) = Q * quantity (step^[k] v) := by
    rw [hsource, hsource]
    ring
  have hext (H a b : ℕ) (hH : 0 < H) (ha : a ∣ H) (hb : b ∣ H)
      (hreads : ∀ p : ℕ, p.Prime →
        Nat.gcd a (p ^ H.factorization p) = Nat.gcd b (p ^ H.factorization p)) : a = b := by
    apply Nat.dvd_antisymm
    all_goals
      apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
      intro p j hp hj
      have hjP := (hp.pow_dvd_iff_dvd_ordProj hH.ne').mp
        (dvd_trans hj (by assumption))
      have hiff := Nat.gcd_left_eq_iff.mp (hreads p hp) (p ^ j) hjP
      first | exact hiff.mp hj | exact hiff.mpr hj
  have hlocal (p : ℕ) (hp : p.Prime) : localLaw p ∧
      (∀ e : ℕ, 2 ≤ e → ∀ t : ℕ, ∀ x : ℤ × ℤ,
      (p : ℤ) ^ (e - 1) ∣ signedValue (t + 1) x → ∀ j : ℕ,
      ((p : ℤ) ^ e ∣ signedValue (t + 1 + j * zeroRank (p ^ (e - 1))) x ↔
        rootBase p e t x + (j : ZMod p) * rootSlope p e t x = 0)) := by
    have hp2 := hp.two_le
    letI : NeZero p := ⟨hp.ne_zero⟩
    let castState (m : ℕ) (z : ℤ × ℤ) : ZMod m × ZMod m := (z.1, z.2)
    have hcastState (m : ℕ) : Function.Semiconj (castState m) (U (A := ℤ)) U := fun z => by
      simp [castState, U]
    have hvalue (m k : ℕ) (x : ℤ × ℤ) :
        (signedValue (k + 1) x : ZMod m) = (U^[k] (castState m x)).2 := by
      simpa [signedValue, castState] using (hiter k (castState m x)).symm
    have hrank (e : ℕ) (he : 1 ≤ e) :
        3 ≤ zeroRank (p ^ e) ∧ p ^ e ∣ Nat.fib (zeroRank (p ^ e)) ∧
        ∀ k : ℕ, p ^ e ∣ Nat.fib k ↔ zeroRank (p ^ e) ∣ k := by
      have hm := (PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p 2 hp le_rfl).1 e
      have hbound : Nat.fib 2 < Nat.fib (zeroRank (p ^ e)) := by
        simpa using lt_of_lt_of_le (hp.one_lt.trans_le (Nat.le_self_pow (by omega) p))
          (Nat.le_of_dvd (Nat.fib_pos.mpr hm.1) hm.2.1)
      have hsmall := Nat.succ_le_of_lt ((Nat.fib_lt_fib (m := 2) le_rfl).mp hbound)
      exact ⟨hsmall, hm.2.1,
        fun k => D5.S3.Arith.FibonacciRank.fibonacci_entry_point hm.1 hm.2.1 hm.2.2⟩
    have hperiod (d : ℕ) (hd : 1 ≤ d) (k j : ℕ) (x : ZMod (p ^ d) × ZMod (p ^ d)) :
        (U^[k + j * zeroRank (p ^ d)] x).2 =
          (Nat.fib (zeroRank (p ^ d) - 1) : ZMod (p ^ d)) ^ j * (U^[k] x).2 := by
      let r := zeroRank (p ^ d)
      have hr := hrank d hd
      have hrpos : 0 < r := by dsimp [r]; omega
      have hf : (Nat.fib r : ZMod (p ^ d)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hr.2.1
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_comm (k + j * r) r,
          Function.iterate_add_apply, hmatrix r hrpos]
        simp only [Prod.snd, hf, zero_mul, add_zero]
        rw [ih, pow_succ]
        ring
    have hrankUnit (d m : ℕ) (hd : 1 ≤ d) :
        IsUnit (Nat.fib (zeroRank (p ^ d) - 1) : ZMod (p ^ m)) := by
      have hr := hrank d hd
      have hcop : (Nat.fib (zeroRank (p ^ d) - 1)).Coprime
          (Nat.fib (zeroRank (p ^ d))) := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ zeroRank (p ^ d))] using
          Nat.fib_coprime_fib_succ (zeroRank (p ^ d) - 1)
      apply (ZMod.isUnit_iff_coprime _ _).mpr
      exact (hcop.of_dvd_right (dvd_trans (dvd_pow_self p (by omega)) hr.2.1)).pow_right m
    have htransport (d : ℕ) (hd : 1 ≤ d) (s t : ℕ) (x : ℤ × ℤ)
        (hst : s % zeroRank (p ^ d) = t % zeroRank (p ^ d)) :
        (p : ℤ) ^ d ∣ signedValue (s + 1) x ↔
          (p : ℤ) ^ d ∣ signedValue (t + 1) x := by
      let r := zeroRank (p ^ d)
      let z : ZMod (p ^ d) × ZMod (p ^ d) := (x.1, x.2)
      have hreduce (k : ℕ) :
          (signedValue (k + 1) x : ZMod (p ^ d)) = 0 ↔ (U^[k % r] z).2 = 0 := by
        rw [hvalue (p ^ d), ← Nat.mod_add_div k r]
        rw [Nat.mul_comm r (k / r), hperiod d hd,
          (hrankUnit d d hd).pow (k / r) |>.mul_right_eq_zero]
        simp [Nat.add_mod, castState, z]
      rw [show (p : ℤ) ^ d = (p ^ d : ℕ) by simp,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
        hreduce, hreduce, hst]
    have hphase (d : ℕ) (hd : 1 ≤ d) (t k : ℕ) (x : ℤ × ℤ)
        (hu : IsUnit ((U^[t] ((x.1, x.2) : ZMod (p ^ d) × ZMod (p ^ d))).1))
        (hz : (signedValue (t + 1) x : ZMod (p ^ d)) = 0) :
        (p : ℤ) ^ d ∣ signedValue (k + 1) x ↔
          k % zeroRank (p ^ d) = t % zeroRank (p ^ d) := by
      let r := zeroRank (p ^ d)
      let z : ZMod (p ^ d) × ZMod (p ^ d) := (x.1, x.2)
      let N := k + t * r
      have hr := hrank d hd
      have hrpos : 0 < r := by dsimp [r]; omega
      have htN : t ≤ N := (Nat.le_mul_of_pos_right t hrpos).trans (Nat.le_add_left _ _)
      have hNk : N % r = k % r := by simp [N, Nat.add_mod]
      rw [← htransport d hd N k x hNk]
      rw [show (p : ℤ) ^ d = (p ^ d : ℕ) by simp,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd, hvalue (p ^ d),
        ← Nat.sub_add_cancel htN, Function.iterate_add_apply, hiter]
      have hz' : (U^[t] z).2 = 0 := by rw [← hvalue (p ^ d)]; exact hz
      rw [hz', mul_zero, add_zero, hu.mul_left_eq_zero, ZMod.natCast_eq_zero_iff,
        hr.2.2, ← Nat.modEq_iff_dvd' htN]
      change t % r = N % r ↔ k % r = t % r
      rw [hNk]
      exact eq_comm
    have hsourceLift (e : ℕ) (he : 1 ≤ e) (Q : ℕ) (hQ : 0 < Q) (x : ℤ × ℤ) :
        ∃ v : ℕ × ℕ, v.1 < Q * p ^ e ∧ v.2 < Q * p ^ e ∧
          (Primitive p x → ¬ p ∣ Q → Primitive p ((v.1 : ℤ), (v.2 : ℤ))) ∧
          ∀ k : ℕ, 0 < k → actualGcd (Q * p ^ e) k v = Q * gcdValue (p ^ e) k x := by
      let P := p ^ e
      have hP : 0 < P := pow_pos hp.pos _
      let z : ZMod P × ZMod P := (x.1, x.2)
      let w : ZMod P × ZMod P := (5 * z.1 - 3 * z.2, -3 * z.1 + 2 * z.2)
      obtain ⟨_, _, _, _, _, _, _, _, _, hbounded, _, _, _, _, _, _, hinverse, _⟩ :=
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2 P hP (0, 0)
      obtain ⟨A, hA1, hA2, hA⟩ := hbounded w
      have hobs : observe (residue P A) = z := by rw [hA]; exact hinverse z
      let v : ℕ × ℕ := (Q * A.1, Q * A.2)
      refine ⟨v, Nat.mul_lt_mul_of_pos_left hA1 hQ, Nat.mul_lt_mul_of_pos_left hA2 hQ, ?_, ?_⟩
      · intro hx hnQ
        by_contra hv
        have hvNat : p ∣ Q * A.1 ∧ p ∣ Q * A.2 := by
          simpa only [Primitive, v, not_or, not_not, Int.natCast_dvd_natCast] using hv
        have hzero : residue p A = (0, 0) := Prod.ext
          ((ZMod.natCast_eq_zero_iff _ _).mpr ((hp.dvd_mul.mp hvNat.1).resolve_left hnQ))
          ((ZMod.natCast_eq_zero_iff _ _).mpr ((hp.dvd_mul.mp hvNat.2).resolve_left hnQ))
        let lower : ZMod P →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)
        have hred : observe (residue p A) = ((x.1 : ZMod p), (x.2 : ZMod p)) := by
          simpa [observe, quantity, step, residue, z, map_ofNat] using
            congrArg (Prod.map lower lower) hobs
        rw [hzero] at hred
        have hcoords := Prod.ext_iff.mp hred.symm
        simp only [observe, quantity, step, Prod.fst, Prod.snd, mul_zero,
          add_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hcoords
        exact hx.elim (fun h => h hcoords.1) (fun h => h hcoords.2)
      · intro k hk
        have hread : (quantity (A := ℕ) (step^[k] A) : ZMod P) = (signedValue k x : ZMod P) := by
          rw [← Int.cast_natCast, hnatural k A hk]
          simpa [signedValue, observe, quantity, step, residue, z] using
            congrArg (fun u : ZMod P × ZMod P =>
              (Nat.fib (k - 1) : ZMod P) * u.1 + Nat.fib k * u.2) hobs
        have hcong : Int.ModEq P (quantity (A := ℕ) (step^[k] A)) (signedValue k x) :=
          (ZMod.intCast_eq_intCast_iff _ _ P).mp (by simpa using hread)
        have hgcd : Nat.gcd (quantity (step^[k] A)) P = gcdValue P k x := by
          have hh := congrArg (fun value : ℤ => Int.gcd value P) hcong
          rw [Int.gcd_emod, Int.gcd_emod] at hh
          simpa [Int.gcd_def, gcdValue] using hh
        rw [actualGcd, hscale, Nat.gcd_mul_left, hgcd]
    have hprimitiveReturned (t : ℕ) (x : ℤ × ℤ) (hx : (U^[t] x).1 = 1) :
        Primitive p x := by
      by_contra hn
      obtain ⟨hn1, hn2⟩ : (p : ℤ) ∣ x.1 ∧ (p : ℤ) ∣ x.2 := by
        simpa only [Primitive, not_or, not_not] using hn
      have hh : (p : ℤ) ∣ (U^[t] x).1 := by
        by_cases ht : t = 0
        · simpa [ht] using hn1
        · rw [hfirst t (by omega)]
          exact dvd_add (dvd_mul_of_dvd_right hn1 _) (dvd_mul_of_dvd_right hn2 _)
      rw [hx] at hh
      exact hp.not_dvd_one (by exact_mod_cast hh)
    have hkernel (t : ℕ) (b : ℤ) : ∃ x : ℤ × ℤ, Primitive p x ∧
        signedValue (t + 1) x = b ∧ ∀ d : ℕ, 1 ≤ d → (p : ℤ) ^ d ∣ b → ∀ k : ℕ,
          ((p : ℤ) ^ d ∣ signedValue (k + 1) x ↔
            k % zeroRank (p ^ d) = t % zeroRank (p ^ d)) := by
      obtain ⟨x, hx⟩ := (hbij (A := ℤ)).surjective.iterate t (1, b)
      have hz : signedValue (t + 1) x = b := by
        simpa [signedValue, hiter] using congrArg Prod.snd hx
      refine ⟨x, hprimitiveReturned t x (congrArg Prod.fst hx), hz, fun d hd hb k => ?_⟩
      apply hphase d hd t k x _
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa [hz] using hb))
      rw [← (hcastState (p ^ d)).iterate_right t x, hx]
      simpa [castState] using (isUnit_one : IsUnit (1 : ZMod (p ^ d)))
    have hreadPower (e k : ℕ) (x : ℤ × ℤ) : ∃ d ≤ e, gcdValue (p ^ e) k x = p ^ d :=
      (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right (signedValue k x).natAbs (p ^ e))
    have hgcdThreshold (e d k : ℕ) (x : ℤ × ℤ) (hd : d ≤ e) :
        (p : ℤ) ^ d ∣ signedValue k x ↔ p ^ d ∣ gcdValue (p ^ e) k x := by
      rw [show (p : ℤ) ^ d = (p ^ d : ℕ) by simp, Int.natCast_dvd,
        gcdValue, Nat.dvd_gcd_iff]
      exact (and_iff_left (pow_dvd_pow p hd)).symm
    have hgcdEquality (e k : ℕ) (x y : ℤ × ℤ)
        (hreads : ∀ d : ℕ, d ≤ e →
          ((p : ℤ) ^ d ∣ signedValue k x ↔ (p : ℤ) ^ d ∣ signedValue k y)) :
        gcdValue (p ^ e) k x = gcdValue (p ^ e) k y := by
      refine Nat.gcd_left_eq_iff.mpr fun divisor hdiv => ?_
      obtain ⟨d, hd, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdiv
      simpa only [← Int.natCast_dvd, Nat.cast_pow] using hreads d hd
    have htablePhase (e d : ℕ) (hd : 1 ≤ d) (hde : d ≤ e)
        (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) (x y : ℤ × ℤ)
        (htable : ∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y)
        (s : ℕ) (hs : s ∈ S) (t : ℕ)
        (hphase : (s - 1) % zeroRank (p ^ d) = t % zeroRank (p ^ d)) :
        (p : ℤ) ^ d ∣ signedValue (t + 1) x ↔
          (p : ℤ) ^ d ∣ signedValue (t + 1) y := by
      rw [← htransport d hd (s - 1) t x hphase,
        ← htransport d hd (s - 1) t y hphase, Nat.sub_add_cancel (hS s hs),
        hgcdThreshold e d s x hde, hgcdThreshold e d s y hde, htable s hs]
    have hlatePhase (e : ℕ) (he : 1 ≤ e) (t B : ℕ) :
        ∃ k : ℕ, B < k ∧ (k - 1) % zeroRank (p ^ e) = t % zeroRank (p ^ e) := by
      let r := zeroRank (p ^ e)
      have hrpos : 0 < r := by have hh := hrank e he; dsimp [r]; omega
      refine ⟨t + (B + 1) * r + 1, ?_, ?_⟩
      · have hh := Nat.le_mul_of_pos_right (B + 1) hrpos
        omega
      · simp [r, Nat.add_mod]
    have hcontent (e : ℕ) (he : 1 ≤ e) :
        ∀ S : Finset ℕ, ∀ hS : S.Nonempty, (∀ k ∈ S, 0 < k) →
          (∃ s ∈ S, ∃ t ∈ S, s % zeroRank p ≠ t % zeroRank p) → ∀ x : ℤ × ℤ,
            (S.image (fun k => gcdValue (p ^ e) k x)).min' (hS.image _) = cappedContent p e x := by
      have hdiv (x : ℤ × ℤ) (k : ℕ) : cappedContent p e x ∣ gcdValue (p ^ e) k x := by
        apply Nat.gcd_dvd_gcd_of_dvd_left (p ^ e)
        apply Int.natCast_dvd.mp
        exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left x.1 x.2) _)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right x.1 x.2) _)
      intro S hS hpositive hphases x
      obtain ⟨k, hk, hmin⟩ := Finset.mem_image.mp
        (Finset.min'_mem (S.image (fun k => gcdValue (p ^ e) k x)) (hS.image _))
      obtain ⟨d, hd, hread⟩ := hreadPower e k x
      have hpmin := hmin.symm.trans hread
      have hz (s : ℕ) (hs : s ∈ S) : (U^[s - 1] (castState (p ^ d) x)).2 = 0 := by
        obtain ⟨b, _, hb⟩ := hreadPower e s x
        have hdivread : p ^ d ∣ gcdValue (p ^ e) s x := by
          rw [hb]
          apply (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr
          exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (by
            simpa only [← hpmin, ← hb] using
              Finset.min'_le _ _ (Finset.mem_image_of_mem _ hs))
        rw [← hvalue, Nat.sub_add_cancel (hpositive s hs), ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa using (hgcdThreshold e d s x hd).mpr hdivread
      obtain ⟨s, hs, t, ht, hst⟩ := hphases
      wlog horder : s ≤ t generalizing s t
      · exact this t ht s hs hst.symm (Nat.le_of_not_ge horder)
      have hf : IsUnit (Nat.fib (t - s) : ZMod (p ^ d)) := by
        apply (ZMod.isUnit_iff_coprime _ _).mpr
        apply hp.coprime_pow_of_not_dvd
        intro hh
        apply hst
        simpa only [pow_one, Nat.ModEq] using (Nat.modEq_iff_dvd' horder).mpr
          (((hrank 1 le_rfl).2.2 (t - s)).mp (by simpa using hh))
      have hzs := hz s hs
      have hzt := hz t ht
      have hspos := hpositive s hs
      rw [show t - 1 = (s - 1) + (t - s) by omega,
        Nat.add_comm (s - 1) (t - s), Function.iterate_add_apply, hiter,
        hzs, mul_zero, add_zero, hf.mul_right_eq_zero] at hzt
      have hzero : U^[s - 1] ((0, 0) : ZMod (p ^ d) × ZMod (p ^ d)) = (0, 0) := by
        apply Function.IsFixedPt.iterate
        simp [Function.IsFixedPt, U]
      have hxzero := (hbij (A := ZMod (p ^ d))).injective.iterate (s - 1)
        ((Prod.ext hzt hzs).trans hzero.symm)
      refine hpmin.trans (Nat.dvd_antisymm ?_ ?_)
      · have hcoords := Prod.ext_iff.mp hxzero
        simp only [castState, Prod.fst, Prod.snd,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at hcoords
        exact Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hcoords.1)
          (Int.natCast_dvd.mp hcoords.2)) (pow_dvd_pow p hd)
      · simpa only [hread] using hdiv x k
    have hexit (e k : ℕ) (he : 1 ≤ e) (z : ℤ × ℤ)
        (hz : (p : ℤ) ^ (e - 1) ∣ signedValue k z)
        (hnz : ¬ (p : ℤ) ^ e ∣ signedValue k z) : gcdValue (p ^ e) k z = p ^ (e - 1) := by
      obtain ⟨depth, hdepth, hgcd⟩ := hreadPower e k z
      have hlow := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
        (hgcd ▸ (hgcdThreshold e (e - 1) k z (by omega)).mp hz)
      have hne : depth ≠ e := fun heq =>
        hnz ((hgcdThreshold e e k z le_rfl).mpr (by rw [hgcd, heq]))
      have heq : depth = e - 1 := by omega
      simpa [heq] using hgcd
    have hcollisionRead (e : ℕ) (he : 1 ≤ e) (x y : ℤ × ℤ) (t : ℕ)
        (hlower : ∀ d < e, ∀ k : ℕ, (p : ℤ) ^ d ∣ signedValue (k + 1) x ↔
          (p : ℤ) ^ d ∣ signedValue (k + 1) y)
        (hx : ∀ k : ℕ, (p : ℤ) ^ e ∣ signedValue (k + 1) x ↔
          k % zeroRank (p ^ e) = t % zeroRank (p ^ e))
        (hy : ¬ (p : ℤ) ^ e ∣ signedValue (t + 1) y) :
        (∀ k : ℕ, 0 < k → ¬ (p : ℤ) ^ e ∣ signedValue k x →
          ¬ (p : ℤ) ^ e ∣ signedValue k y →
          gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) ∧
        ∀ B : ℕ, ∃ k : ℕ, B < k ∧ gcdValue (p ^ e) k x = p ^ e ∧
          gcdValue (p ^ e) k y = p ^ (e - 1) := by
      constructor
      · intro k hkpos hnx hny
        apply hgcdEquality e k x y
        intro d hd
        by_cases hde : d = e
        · exact hde ▸ iff_of_false hnx hny
        · simpa only [Nat.sub_add_cancel hkpos] using hlower d (by omega) (k - 1)
      · intro B
        obtain ⟨k, hk, hkt⟩ := hlatePhase e he t B
        have hkpos : 0 < k := by omega
        have hhit : (p : ℤ) ^ e ∣ signedValue k x := by
          simpa only [Nat.sub_add_cancel hkpos] using (hx (k - 1)).mpr hkt
        have hlow : (p : ℤ) ^ (e - 1) ∣ signedValue k y := by
          simpa only [Nat.sub_add_cancel hkpos] using
            (hlower (e - 1) (by omega) (k - 1)).mp
              (by simpa only [Nat.sub_add_cancel hkpos] using
                dvd_trans (pow_dvd_pow (p : ℤ) (by omega : e - 1 ≤ e)) hhit)
        have hmiss : ¬ (p : ℤ) ^ e ∣ signedValue k y := by
          intro hh
          apply hy
          apply (htransport e he (k - 1) t y hkt).mp
          simpa only [Nat.sub_add_cancel hkpos] using hh
        exact ⟨k, hk, Nat.gcd_eq_right (by
          simpa only [← Nat.cast_pow, Int.natCast_dvd] using hhit), hexit e k he y hlow hmiss⟩
    have hstagnation (e : ℕ) (he : 2 ≤ e)
        (hs : zeroRank (p ^ e) = zeroRank (p ^ (e - 1))) (t : ℕ) :
        ∃ x y : ℤ × ℤ, Primitive p x ∧ Primitive p y ∧
          (∀ S : Finset ℕ,
            (∀ k ∈ S, 0 < k ∧ (k - 1) % zeroRank (p ^ e) ≠ t % zeroRank (p ^ e)) →
            ∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) ∧
          ∀ B : ℕ, ∃ k : ℕ, B < k ∧ gcdValue (p ^ e) k x = p ^ e ∧
            gcdValue (p ^ e) k y = p ^ (e - 1) := by
      obtain ⟨x, hx, _, hxphase⟩ := hkernel t 0
      have hxs := fun d hd => hxphase d hd (dvd_zero _)
      let b : ℤ := (p : ℤ) ^ (e - 1)
      obtain ⟨y, hyprim, hyt, hyphase⟩ := hkernel t b
      have hys := fun d (hd : 1 ≤ d) (hde : d < e) =>
        hyphase d hd (pow_dvd_pow (p : ℤ) (by omega : d ≤ e - 1))
      have hnotT : ¬ (p : ℤ) ^ e ∣ signedValue (t + 1) y := by
        simp only [hyt, b, ← Nat.cast_pow, Int.natCast_dvd_natCast,
          Nat.pow_dvd_pow_iff_le_right hp.one_lt]
        omega
      have hlower (d : ℕ) (hd : d < e) (k : ℕ) :
          (p : ℤ) ^ d ∣ signedValue (k + 1) x ↔
            (p : ℤ) ^ d ∣ signedValue (k + 1) y := by
        by_cases hd0 : d = 0
        · simp [hd0]
        · rw [hxs d (by omega) k, hys d (by omega) hd k]
      have hmiss (k : ℕ) : ¬ (p : ℤ) ^ e ∣ signedValue (k + 1) y := by
        intro hk
        have hlow := dvd_trans (pow_dvd_pow (p : ℤ) (by omega : e - 1 ≤ e)) hk
        have hsame := (hys (e - 1) (by omega) (by omega) k).mp hlow
        exact hnotT ((htransport e (by omega) k t y
          (by simpa [hs] using hsame)).mp hk)
      obtain ⟨htable, hlate⟩ := hcollisionRead e (by omega) x y t hlower
        (hxs e (by omega)) (hmiss t)
      refine ⟨x, y, hx, hyprim, ?_, hlate⟩
      intro S hS k hk
      obtain ⟨hkpos, havoid⟩ := hS k hk
      apply htable k hkpos
      · simpa only [Nat.sub_add_cancel hkpos] using
          (fun hh => havoid ((hxs e (by omega) (k - 1)).mp hh))
      · simpa only [Nat.sub_add_cancel hkpos] using hmiss (k - 1)
    have hcoverage (e : ℕ) (he : 2 ≤ e) (S : Finset ℕ) (hD : D p e S)
        (j : ℕ) (hj : 1 ≤ j) (hje : j < e) (a b : ZMod (zeroRank (p ^ j))) :
        ∃ k ∈ S, ((k - 1 : ℕ) : ZMod (zeroRank (p ^ j))) + a = b := by
      let R := zeroRank (p ^ (e - 1))
      have hR := hrank (e - 1) (by omega)
      have htop := hrank e (by omega)
      have hdivTop : R ∣ zeroRank (p ^ e) :=
        (hR.2.2 _).mp (dvd_trans (pow_dvd_pow p (by omega)) htop.2.1)
      have hfull : ∀ t < R, ∃ k ∈ S, (k - 1) % R = t := by
        intro t ht
        by_cases hs : zeroRank (p ^ e) = R
        · have hc : ∀ t < zeroRank (p ^ e),
              ∃ k ∈ S, (k - 1) % zeroRank (p ^ e) = t := by
            simpa [D, show e ≠ 1 by omega, hs, R] using hD
          simpa [hs] using hc t (hs.symm ▸ ht)
        · have hcover : ∀ t < R, p - 1 ≤ (queryChildren p e t S).card := by
            simpa [D, show e ≠ 1 by omega, hs, R] using hD
          have hc := hcover t ht
          obtain ⟨child, hchild⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) hc)
          obtain ⟨_, k, hk, heq⟩ := Finset.mem_filter.mp hchild
          refine ⟨k, hk, ?_⟩
          have hmod := congrArg (fun u => u % R) heq
          rw [Nat.mod_mod_of_dvd _ hdivTop, Nat.mod_mod_of_dvd _ hdivTop] at hmod
          change (k - 1) % R = (t + child.val * R) % R at hmod
          simpa [Nat.add_mod, Nat.mod_eq_of_lt ht] using hmod
      have hdiv : zeroRank (p ^ j) ∣ R :=
        ((hrank j hj).2.2 R).mp (dvd_trans (pow_dvd_pow p (by omega)) hR.2.1)
      have hle : zeroRank (p ^ j) ≤ R := Nat.le_of_dvd (by omega) hdiv
      letI : NeZero (zeroRank (p ^ j)) := ⟨by have hr := hrank j hj; omega⟩
      obtain ⟨k, hk, heq⟩ := hfull (b - a).val ((ZMod.val_lt (b - a)).trans_le hle)
      refine ⟨k, hk, ?_⟩
      have hmod := congrArg (fun u => u % zeroRank (p ^ j)) heq
      rw [Nat.mod_mod_of_dvd _ hdiv] at hmod
      exact eq_sub_iff_add_eq.mp (by
        simpa only [ZMod.natCast_mod, ZMod.natCast_zmod_val] using
          congrArg (fun u : ℕ => (u : ZMod (zeroRank (p ^ j)))) hmod)
    have hgrowthData (e : ℕ) (he : 2 ≤ e) :
        (∀ t : ℕ, ∀ x : ℤ × ℤ, (p : ℤ) ^ (e - 1) ∣ signedValue (t + 1) x →
          ∀ j : ℕ, ((p : ℤ) ^ e ∣ signedValue
            (t + 1 + j * zeroRank (p ^ (e - 1))) x ↔
            rootBase p e t x + (j : ZMod p) * rootSlope p e t x = 0)) ∧
        (zeroRank (p ^ e) = p * zeroRank (p ^ (e - 1)) →
          ∀ t : ℕ, ∀ J : Finset (ZMod p), J.card + 2 ≤ p →
            ∃ x y : ℤ × ℤ, Primitive p x ∧ Primitive p y ∧
              (∀ S : Finset ℕ,
                (∀ k ∈ S, 0 < k ∧ ∀ a : ZMod p, a ∉ J →
                  (k - 1) % zeroRank (p ^ e) ≠
                    (t + a.val * zeroRank (p ^ (e - 1))) % zeroRank (p ^ e)) →
                ∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) ∧
              ∀ B : ℕ, ∃ k : ℕ, B < k ∧ gcdValue (p ^ e) k x = p ^ e ∧
                gcdValue (p ^ e) k y = p ^ (e - 1)) := by
      let R := zeroRank (p ^ (e - 1))
      let P := p ^ e
      let c : ZMod P := Nat.fib (R - 1)
      let f : ZMod P := Nat.fib R
      have hR := hrank (e - 1) (by omega)
      have hRpos : 0 < R := by dsimp [R]; omega
      have hRzero : p ^ (e - 1) ∣ Nat.fib R := hR.2.1
      have hc : IsUnit c := hrankUnit (e - 1) e (by omega)
      have hcinv : c⁻¹ * c = 1 := ZMod.inv_mul_of_unit c hc
      have hfzero : f ^ 2 = 0 := by
        change (Nat.fib R : ZMod P) ^ 2 = 0
        rw [pow_two, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
        have hsq : p ^ (2 * (e - 1)) ∣ Nat.fib R * Nat.fib R := by
          simpa [pow_add, two_mul] using Nat.mul_dvd_mul hRzero hRzero
        exact dvd_trans (pow_dvd_pow p (by omega : e ≤ 2 * (e - 1))) hsq
      have hblock (x : ZMod P × ZMod P) :
          U^[R] x = (c * x.1 + f * x.2, c * x.2 + f * (x.1 + x.2)) := by
        exact hmatrix R hRpos x
      have hblocks (j : ℕ) (x : ZMod P × ZMod P) :
          U^[j * R] x =
            (c ^ j * (x.1 + (j : ZMod P) * c⁻¹ * f * x.2),
             c ^ j * (x.2 + (j : ZMod P) * c⁻¹ * f * (x.1 + x.2))) := by
        induction j with
        | zero => simp
        | succ j ih =>
          rw [Nat.succ_mul, Nat.add_comm (j * R) R, Function.iterate_add_apply, ih, hblock]
          apply Prod.ext <;> simp only [Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one,
            pow_succ] <;> ring_nf <;> simp only [hfzero, mul_zero, add_zero, zero_mul]
          all_goals ring_nf at hcinv ⊢
          all_goals linear_combination (norm := ring) hcinv
          all_goals simp only [hcinv]; ring
      have hnormal (t j : ℕ) (x : ℤ × ℤ) :
          c⁻¹ ^ j * (signedValue (t + 1 + j * R) x : ZMod P) =
            (signedValue (t + 1) x : ZMod P) +
              (j : ZMod P) * c⁻¹ * f * (signedValue (t + 2) x : ZMod P) := by
        let z : ZMod P × ZMod P := (x.1, x.2)
        have hval := fun k => hvalue P k x
        have hnext : (signedValue (t + 2) x : ZMod P) =
            (U^[t] z).1 + (U^[t] z).2 := by
          rw [show t + 2 = (t + 1) + 1 by omega, hval, Function.iterate_succ_apply']
        rw [show t + 1 + j * R = (t + j * R) + 1 by omega, hval, hval, hnext,
          Nat.add_comm t (j * R), Function.iterate_add_apply, hblocks]
        rw [← mul_assoc, ← mul_pow, hcinv, one_pow, one_mul]
      let b : ℤ := (p : ℤ) ^ (e - 1)
      let q : ℕ := Nat.fib R / p ^ (e - 1)
      have hb : b ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      have hfq : b * (q : ℤ) = Nat.fib R := by
        dsimp [b, q]
        exact_mod_cast Nat.mul_div_cancel' hRzero
      have hpow : (p : ℤ) ^ e = b * p := by
        simpa [b, Nat.sub_add_cancel (by omega : 1 ≤ e)] using pow_succ (p : ℤ) (e - 1)
      have hroot (t : ℕ) (x : ℤ × ℤ)
          (hparent : b ∣ signedValue (t + 1) x) (j : ℕ) :
          (p : ℤ) ^ e ∣ signedValue (t + 1 + j * R) x ↔
            rootBase p e t x + (j : ZMod p) * rootSlope p e t x = 0 := by
        have hunit := hc.mul ((IsUnit.of_mul_eq_one c hcinv).pow j)
        have hscaled : (c * c⁻¹ ^ j) *
            (signedValue (t + 1 + j * R) x : ZMod P) =
            c * (signedValue (t + 1) x : ZMod P) +
              (j : ZMod P) * f * (signedValue (t + 2) x : ZMod P) := by
          rw [mul_assoc, hnormal]
          linear_combination (norm := ring)
            (j : ZMod P) * f * (signedValue (t + 2) x : ZMod P) * hcinv
        have hfactor : (Nat.fib (R - 1) : ℤ) * signedValue (t + 1) x +
            j * (Nat.fib R : ℤ) * signedValue (t + 2) x =
            b * ((Nat.fib (R - 1) : ℤ) * (signedValue (t + 1) x / b) +
              j * (q : ℤ) * signedValue (t + 2) x) := by
          conv_lhs => rw [← Int.mul_ediv_cancel' hparent, ← hfq]
          ring
        rw [show (p : ℤ) ^ e = (P : ℤ) by simp [P],
          ← ZMod.intCast_zmod_eq_zero_iff_dvd _ P,
          ← hunit.mul_right_eq_zero, hscaled]
        simp only [c, f, ← Int.cast_natCast (R := ZMod P),
          ← Int.cast_mul, ← Int.cast_add]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, show (P : ℤ) = (p : ℤ) ^ e by simp [P],
          hfactor, hpow, mul_dvd_mul_iff_left hb]
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd _ p]
        simp only [rootBase, rootSlope, R, b, q, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          mul_assoc]
      have hcollision (hg : zeroRank P = p * R) (t : ℕ) (J : Finset (ZMod p))
          (hJ : J.card + 2 ≤ p) : ∃ x y : ℤ × ℤ,
          Primitive p x ∧ Primitive p y ∧
          (∀ S : Finset ℕ,
            (∀ k ∈ S, 0 < k ∧ ∀ a : ZMod p, a ∉ J →
              (k - 1) % zeroRank (p ^ e) ≠ (t + a.val * R) % zeroRank (p ^ e)) →
            ∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) ∧
          ∀ B : ℕ, ∃ k : ℕ, B < k ∧ gcdValue (p ^ e) k x = p ^ e ∧
            gcdValue (p ^ e) k y = p ^ (e - 1) := by
        have hcompl : 1 < Jᶜ.card := by
          rw [Finset.card_compl, ZMod.card p]
          omega
        obtain ⟨a, ha, d, hd, hne⟩ := Finset.one_lt_card.mp hcompl
        have hnotA : a ∉ J := Finset.mem_compl.mp ha
        have hnotD : d ∉ J := Finset.mem_compl.mp hd
        obtain ⟨x, hx, _, hxphase⟩ := hkernel (t + a.val * R) 0
        obtain ⟨y, hy, _, hyphase⟩ := hkernel (t + d.val * R) 0
        have hxs := fun depth hd => hxphase depth hd (dvd_zero _)
        have hys := fun depth hd => hyphase depth hd (dvd_zero _)
        have htopx := hxs e (by omega)
        have htopy := hys e (by omega)
        have hlower (depth : ℕ) (hdepth : depth < e) (k : ℕ) :
            (p : ℤ) ^ depth ∣ signedValue (k + 1) x ↔
              (p : ℤ) ^ depth ∣ signedValue (k + 1) y := by
          by_cases hz : depth = 0
          · simp [hz]
          · have hdiv : zeroRank (p ^ depth) ∣ R :=
              ((hrank depth (by omega)).2.2 R).mp
                (dvd_trans (pow_dvd_pow p (by omega)) hRzero)
            rw [hxs depth (by omega), hys depth (by omega)]
            simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hdiv]
        have hmiss : ¬ (p : ℤ) ^ e ∣ signedValue (t + a.val * R + 1) y := by
          intro hh
          apply hne
          have hsame := (htopy (t + a.val * R)).mp hh
          rw [hg] at hsame
          have hchildren : a.val * R % (p * R) = d.val * R % (p * R) :=
            Nat.ModEq.add_left_cancel' t hsame
          rw [Nat.mul_mod_mul_right, Nat.mul_mod_mul_right,
            Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt d)] at hchildren
          exact ZMod.val_injective p (Nat.eq_of_mul_eq_mul_right hRpos hchildren)
        obtain ⟨hread, hlate⟩ := hcollisionRead e (by omega) x y
          (t + a.val * R) hlower htopx hmiss
        refine ⟨x, y, hx, hy, ?_, hlate⟩
        intro S hS k hk
        obtain ⟨hkpos, havoid⟩ := hS k hk
        apply hread k hkpos
        · rw [← Nat.sub_add_cancel hkpos, htopx]
          exact havoid a hnotA
        · rw [← Nat.sub_add_cancel hkpos, htopy]
          exact havoid d hnotD
      exact ⟨hroot, hcollision⟩
    have hsigned (e : ℕ) (he : 1 ≤ e) (S : Finset ℕ)
        (hS : ∀ k ∈ S, 0 < k) (hD : D p e S) (x y : ℤ × ℤ)
        (htable : ∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) :
        ∀ k : ℕ, 0 < k → gcdValue (p ^ e) k x = gcdValue (p ^ e) k y := by
      by_cases he1 : e = 1
      · subst e
        simp only [pow_one] at htable ⊢
        exact ((prime_phase_gcd_sampling hp S hS).1.mpr hD) x.1 x.2 y.1 y.2 htable
      have he2 : 2 ≤ e := by omega
      have hlow (d : ℕ) (hd : 1 ≤ d) (hde : d < e) (t : ℕ) :
          (p : ℤ) ^ d ∣ signedValue (t + 1) x ↔ (p : ℤ) ^ d ∣ signedValue (t + 1) y := by
        obtain ⟨s, hs, hphase⟩ := hcoverage e he2 S hD d hd hde 0 (t : ZMod _)
        have hsame : (s - 1) % zeroRank (p ^ d) = t % zeroRank (p ^ d) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by simpa using hphase)
        exact htablePhase e d hd (by omega) S hS x y htable s hs t hsame
      intro k hk
      apply hgcdEquality e k x y
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0]
      by_cases hde : d = e
      · subst d
        by_cases hst : zeroRank (p ^ e) = zeroRank (p ^ (e - 1))
        · have hfull : ∀ t < zeroRank (p ^ e), ∃ s ∈ S, (s - 1) % zeroRank (p ^ e) = t := by
            simpa [D, he1, hst] using hD
          obtain ⟨s, hs, hsame⟩ := hfull ((k - 1) % zeroRank (p ^ e))
            (Nat.mod_lt _ (by have hr := hrank e he; omega))
          simpa only [Nat.sub_add_cancel hk] using
            htablePhase e e he le_rfl S hS x y htable s hs (k - 1) hsame
        · let R := zeroRank (p ^ (e - 1))
          let t := (k - 1) % R
          have hRpos : 0 < R := by have hr := hrank (e - 1) (by omega); dsimp [R]; omega
          have ht : t < R := Nat.mod_lt _ hRpos
          have hroot := (hgrowthData e he2).1
          have hparents := hlow (e - 1) (by omega) (by omega) t
          by_cases hparentx : (p : ℤ) ^ (e - 1) ∣ signedValue (t + 1) x
          · have hparenty := hparents.mp hparentx
            let : Fact p.Prime := ⟨hp⟩
            let J := queryChildren p e t S
            have hJ : p - 1 ≤ J.card := by
              suffices hc : ∀ u < R, p - 1 ≤ (queryChildren p e u S).card from hc t ht
              simpa [D, he1, hst, R] using hD
            have hquery (c : ZMod p) (hc : c ∈ J) :
                rootBase p e t x + c * rootSlope p e t x = 0 ↔
                  rootBase p e t y + c * rootSlope p e t y = 0 := by
              obtain ⟨_, s, hs, hsame⟩ := Finset.mem_filter.mp hc
              have heq := htablePhase e e he le_rfl S hS x y htable s hs
                (t + c.val * R) hsame
              rw [Nat.add_right_comm t (c.val * R) 1,
                hroot t x hparentx, hroot t y hparenty, ZMod.natCast_zmod_val] at heq
              exact heq
            have hcoord : k = t + 1 + ((k - 1) / R) * R := by
              have hm := Nat.mod_add_div (k - 1) R
              rw [Nat.mul_comm R] at hm
              dsimp [t]; omega
            rw [hcoord, hroot t x hparentx, hroot t y hparenty]
            have hzero : rootSlope p e t x = 0 ↔ rootSlope p e t y = 0 := by
              have hnext := hlow 1 le_rfl (by omega) (t + 1)
              simp only [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hnext
              simpa only [rootSlope, mul_eq_zero, Nat.add_assoc] using or_congr Iff.rfl hnext
            by_cases hx : rootSlope p e t x = 0
            · obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) hJ)
              simpa only [hx, hzero.mp hx, mul_zero, add_zero] using hquery c hc
            · have hy := fun hh => hx (hzero.mpr hh)
              have hsingle (z : ℤ × ℤ) (hn : rootSlope p e t z ≠ 0) :
                  ∃ a : ZMod p, ∀ c : ZMod p,
                    rootBase p e t z + c * rootSlope p e t z = 0 ↔ c = a := by
                refine ⟨-rootBase p e t z / rootSlope p e t z, fun c => ?_⟩
                field_simp
                constructor <;> intro hh <;> linear_combination hh
              obtain ⟨a, ha⟩ := hsingle x hx
              obtain ⟨b, hb⟩ := hsingle y hy
              have hab : a = b := by
                by_contra hne
                have hnotA : a ∉ J :=
                  fun hh => hne ((hb a).mp ((hquery a hh).mp ((ha a).mpr rfl)))
                have hnotB : b ∉ J := fun hh =>
                  hne ((ha b).mp ((hquery b hh).mpr ((hb b).mpr rfl))).symm
                have hsmall : Jᶜ.card ≤ 1 := by rw [Finset.card_compl, ZMod.card p]; omega
                exact hne (Finset.card_le_one.mp hsmall a (Finset.mem_compl.mpr hnotA)
                  b (Finset.mem_compl.mpr hnotB))
              rw [ha, hb, hab]
          · have hparenty : ¬ (p : ℤ) ^ (e - 1) ∣ signedValue (t + 1) y :=
              fun hh => hparentx (hparents.mpr hh)
            have hsame : (k - 1) % R = t % R := by simp [t, Nat.mod_eq_of_lt ht]
            have hnone (z : ℤ × ℤ) (hz : ¬ (p : ℤ) ^ (e - 1) ∣ signedValue (t + 1) z) :
                ¬ (p : ℤ) ^ e ∣ signedValue k z := by
              intro hh
              apply hz
              apply (htransport (e - 1) (by omega) (k - 1) t z hsame).mp
              rw [Nat.sub_add_cancel hk]
              exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hh
            exact iff_of_false (hnone x hparentx) (hnone y hparenty)
      · simpa only [Nat.sub_add_cancel hk] using hlow d (by omega) (by omega) (k - 1)
    have hfailed (e : ℕ) (he : 1 ≤ e) (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
        (hD : ¬ D p e S) : ∃ x y : ℤ × ℤ, Primitive p x ∧ Primitive p y ∧
          (∀ k ∈ S, gcdValue (p ^ e) k x = gcdValue (p ^ e) k y) ∧
          ∀ B : ℕ, ∃ k : ℕ, B < k ∧ gcdValue (p ^ e) k x = p ^ e ∧
            gcdValue (p ^ e) k y = p ^ (e - 1) := by
      by_cases he1 : e = 1
      · subst e
        simp only [pow_one, Nat.sub_self, pow_zero] at ⊢
        have hcard : (S.image (fun k => k % zeroRank p)).card <
            (if zeroRank p = p + 1 then zeroRank p - 1 else zeroRank p) := by
          simpa [D] using hD
        obtain ⟨n, z, n', z', a, b, a', b', hx, hy, _, _, _, _, _, htable, hlate⟩ :=
          (prime_phase_gcd_sampling hp S hS).2.2 hcard 1 zero_lt_one
        refine ⟨(n, z), (n', z'), ?_, ?_, ?_, ?_⟩
        · simpa only [Primitive, primitive, Int.natCast_dvd] using hx
        · simpa only [Primitive, primitive, Int.natCast_dvd] using hy
        · exact fun k hk => (htable k hk).1
        · intro B
          obtain ⟨k, hk, _, _, hfirst, hsecond, _⟩ := hlate B
          exact ⟨k, hk, hfirst, hsecond⟩
      · have he2 : 2 ≤ e := by omega
        by_cases hs : zeroRank (p ^ e) = zeroRank (p ^ (e - 1))
        · have hmissing : ∃ t, t < zeroRank (p ^ e) ∧
              ∀ k ∈ S, (k - 1) % zeroRank (p ^ e) ≠ t := by
            simpa only [D, if_neg he1, if_pos hs, not_forall, not_exists,
              not_and, exists_prop] using hD
          obtain ⟨t, ht, havoid⟩ := hmissing
          obtain ⟨x, y, hx, hy, htable, hlate⟩ := hstagnation e he2 hs t
          exact ⟨x, y, hx, hy, htable S (fun k hk => ⟨hS k hk,
            by simpa [Nat.mod_eq_of_lt ht] using havoid k hk⟩), hlate⟩
        · have hg := (PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon
            p e hp he2).2.1.resolve_left hs
          have hmissing : ∃ t, t < zeroRank (p ^ (e - 1)) ∧
              ¬ p - 1 ≤ (queryChildren p e t S).card := by
            simpa only [D, if_neg he1, if_neg hs, not_forall, exists_prop] using hD
          obtain ⟨t, _, ht⟩ := hmissing
          have hsmall : (queryChildren p e t S).card + 2 ≤ p := by omega
          obtain ⟨x, y, hx, hy, htable, hlate⟩ :=
            (hgrowthData e he2).2 hg t (queryChildren p e t S) hsmall
          refine ⟨x, y, hx, hy, htable S ?_, hlate⟩
          intro k hk; refine ⟨hS k hk, ?_⟩
          intro a ha heq
          apply ha
          refine Finset.mem_filter.mpr ⟨?_, k, hk, heq⟩
          exact Finset.mem_image.mpr ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), by simp⟩
    have hbounded : collisionLaw p := by
      intro e he S hS hD
      obtain ⟨x, y, hx, hy, htable, hlate⟩ := hfailed e he S hS hD
      refine ⟨x, y, hx, hy, htable, ?_⟩
      intro Q hQ
      obtain ⟨v, hv1, hv2, hvprim, hv⟩ := hsourceLift e he Q hQ x
      obtain ⟨w, hw1, hw2, hwprim, hw⟩ := hsourceLift e he Q hQ y
      refine ⟨v, w, hv1, hv2, hw1, hw2, fun hQp => ⟨hvprim hx hQp, hwprim hy hQp⟩,
        fun k hk => ⟨hv k hk, hw k hk⟩, ?_, ?_⟩
      · intro k hk
        rw [hv k (hS k hk), hw k (hS k hk), htable k hk]
      · intro B
        obtain ⟨k, hk, hgx, hgy⟩ := hlate B
        have hkpos : 0 < k := by omega
        have hne : p ^ e ≠ p ^ (e - 1) :=
          (Nat.pow_lt_pow_right hp.one_lt (by omega : e - 1 < e)).ne.symm
        refine ⟨k, hk, hkpos, ?_, hgx, hgy, by rw [hv k hkpos, hgx], by rw [hw k hkpos, hgy]⟩
        intro hmem
        exact hne (hgx.symm.trans ((htable k hmem).trans hgy))
    have htower (e : ℕ) (he : 1 ≤ e) (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
        (hD : D p e S) (j : ℕ) (hj : 1 ≤ j) (hje : j < e) : D p j S := by
      by_contra hDj
      obtain ⟨x, y, _, _, htable, hlate⟩ := hfailed j hj S hS hDj
      obtain ⟨k, hk, hgx, hgy⟩ := hlate 0
      obtain ⟨s, hs, hphase⟩ := hcoverage e (by omega) S hD j hj hje 0 (k - 1 : ℕ)
      have hsame := (ZMod.natCast_eq_natCast_iff' (s - 1) (k - 1) _).mp
        (by simpa using hphase)
      have hiff : (p : ℤ) ^ j ∣ signedValue k x ↔ (p : ℤ) ^ j ∣ signedValue k y := by
        simpa only [Nat.sub_add_cancel (by omega : 0 < k)] using
          htablePhase j j hj le_rfl S hS x y htable s hs (k - 1) hsame
      have hdiv : p ^ j ∣ p ^ (j - 1) := by
        rw [← hgy]
        exact (hgcdThreshold j j k y le_rfl).mp
          (hiff.mp ((hgcdThreshold j j k x le_rfl).mpr (by rw [hgx])))
      exact (by omega : ¬ j ≤ j - 1) ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdiv)
    refine ⟨?_, fun e he => (hgrowthData e he).1⟩
    refine ⟨hbounded, hcontent, hcoverage, ?_, ?_, ?_⟩
    · intro e he S hS
      have hne : p ^ e ≠ p ^ (e - 1) :=
        (Nat.pow_lt_pow_right hp.one_lt (by omega : e - 1 < e)).ne.symm
      tfae_have 1 → 2 := fun hD => ⟨hD, htower e he S hS hD⟩
      tfae_have 2 → 1 := And.left
      tfae_have 1 → 4 := hsigned e he S hS
      tfae_have 4 → 3 := fun hid x y _ _ => hid x y
      tfae_have 3 → 1 := by
        intro hid
        by_contra hD
        obtain ⟨x, y, hx, hy, htable, hlate⟩ := hfailed e he S hS hD
        obtain ⟨k, hk, hgx, hgy⟩ := hlate 0
        exact hne (hgx.symm.trans ((hid x y hx hy htable k (by omega)).trans hgy))
      tfae_have 1 → 5 := by
        intro hD v w htable k hk
        rw [hactual _ _ _ hk, hactual _ _ _ hk]
        apply hsigned e he S hS hD _ _ (fun s hs => ?_) k hk
        simpa only [hactual _ _ _ (hS s hs)] using htable s hs
      tfae_have 5 → 6 := fun hid v w _ _ => hid v w
      tfae_have 6 → 1 := by
        intro hid
        by_contra hD
        obtain ⟨x, y, _, _, _, hQ⟩ := hbounded e he S hS hD
        obtain ⟨v, w, _, _, _, _, hprim, _, htable, hlate⟩ := hQ 1 zero_lt_one
        obtain ⟨k, _, hk, _, _, _, hv, hw⟩ := hlate 0
        simp only [one_mul] at htable hv hw
        have heq := hid v w (hprim hp.not_dvd_one).1 (hprim hp.not_dvd_one).2
          htable k hk
        exact hne (hv.symm.trans (heq.trans hw))
      tfae_finish
    · intro e he S hS hD H hH hfactor hexact
      let P := p ^ e
      have hP : 0 < P := pow_pos hp.pos _
      let Q := H / P
      have hQpos : 0 < Q := Nat.div_pos (Nat.le_of_dvd hH hfactor) hP
      have hHQ : Q * P = H := Nat.div_mul_cancel hfactor
      have hunit : ¬ p ∣ Q := by
        simpa only [Q, P, Nat.dvd_div_iff_mul_dvd hfactor, ← Nat.pow_succ] using hexact
      obtain ⟨x, y, _, _, _, hQ⟩ := hbounded e he S hS hD
      obtain ⟨v, w, hv1, hv2, hw1, hw2, _, _, htable, hlate⟩ := hQ Q hQpos
      have hPpow : P = p ^ (e - 1) * p := by
        exact (congrArg (p ^ ·) (Nat.sub_add_cancel he)).symm.trans (Nat.pow_succ p _)
      have hdiv : H / p = Q * p ^ (e - 1) := by
        rw [← hHQ, hPpow, ← Nat.mul_assoc, Nat.mul_div_left _ hp.pos]
      refine ⟨hunit, v, w, hHQ ▸ hv1, hHQ ▸ hv2, hHQ ▸ hw1, hHQ ▸ hw2,
        fun k hk => hHQ ▸ htable k hk, ?_⟩
      intro B
      obtain ⟨k, hkB, hkpos, hnot, _, _, hv, hw⟩ := hlate B
      exact ⟨k, hkB, hkpos, hnot, hHQ ▸ hv, hdiv.symm ▸ (hHQ ▸ hw)⟩
    · intro e he S hS hD
      have hfirst : D p 1 S :=
        if he1 : e = 1 then he1 ▸ hD else htower e he S hS hD 1 le_rfl (by omega)
      have hc : 1 < (S.image (fun k => k % zeroRank p)).card := by
        have hr : 3 ≤ zeroRank p := by simpa using (hrank 1 le_rfl).1
        simp only [D, if_true] at hfirst
        split_ifs at hfirst <;> omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
      refine ⟨⟨s, hs⟩, ⟨s, hs, t, ht, hab⟩, ?_⟩
      exact hcontent e he S ⟨s, hs⟩ hS ⟨s, hs, t, ht, hab⟩
  have hcomponent (H P : ℕ) (hdiv : P ∣ H) (k : ℕ) (v : ℕ × ℕ) :
      Nat.gcd (actualGcd H k v) P = actualGcd P k v := by
    simp only [actualGcd, Nat.gcd_assoc, Nat.gcd_eq_right hdiv]
  have hcombine (H : ℕ) (hH : 0 < H) (S : Finset ℕ)
      (hids : ∀ p : ℕ, p.Prime → 1 ≤ H.factorization p →
        Identifies (actualGcd (p ^ H.factorization p)) S) : Identifies (actualGcd H) S := by
    intro v w htable k hk
    apply hext H _ _ hH (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
    intro p hp
    by_cases hz : H.factorization p = 0
    · simp [hz]
    simp only [Nat.gcd_assoc, Nat.gcd_eq_right (Nat.ordProj_dvd H p)]
    apply hids p hp (by omega) v w ?_ k hk
    intro s hs
    simpa only [hcomponent H _ (Nat.ordProj_dvd H p)] using
      congrArg (fun n => Nat.gcd n (p ^ H.factorization p)) (htable s hs)
  have hglobal (H : ℕ) (hH : 0 < H) (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) :
      Identifies (actualGcd H) S ↔ ∀ p : ℕ, p.Prime → ∀ e : ℕ, 1 ≤ e →
        p ^ e ∣ H → ¬ p ^ (e + 1) ∣ H → D p e S := by
    constructor
    · intro hid p hp e he hdiv hexact
      by_contra hD
      obtain ⟨_, v, w, _, _, _, _, htable, hlate⟩ :=
        (hlocal p hp).1.2.2.2.2.1 e he S hS hD H hH hdiv hexact
      obtain ⟨k, _, hk, _, hv, hw⟩ := hlate 0
      have heq := hid v w htable k hk
      exact (Nat.div_lt_self hH hp.one_lt).ne (hw.symm.trans (heq.symm.trans hv))
    · exact fun hD => hcombine H hH S fun p hp he =>
        ((hlocal p hp).1.2.2.2.1 _ he S hS).out 0 4 |>.mp
          (hD p hp _ he (Nat.ordProj_dvd H p) (Nat.pow_succ_factorization_not_dvd hH.ne' hp))
  refine ⟨hlocal, hglobal, by simp [actualGcd], ?_⟩
  intro p hp e he S hS hD
  obtain ⟨hnonempty, _, hminimum⟩ := (hlocal p hp).1.2.2.2.2.2 e he S hS hD
  refine ⟨hnonempty, ?_⟩
  intro v
  have hcontent : cappedContent p e ((observe v).1, (observe v).2) =
      Nat.gcd (Nat.gcd v.1 v.2) (p ^ e) := by
    simpa only [cappedContent, Int.natAbs_natCast, observe, Prod.fst, Prod.snd,
      GraftAffineClosure.graftGcd] using
      (GraftAffineClosure.result.2 (p ^ e) (pow_pos hp.pos e) v).2.2.2.2.1
  have himage : S.image (fun k => actualGcd (p ^ e) k v) =
      S.image (fun k => gcdValue (p ^ e) k ((observe v).1, (observe v).2)) := by
    apply Finset.image_congr
    intro k hk
    exact hactual (p ^ e) k v (hS k hk)
  simpa only [himage] using (hminimum ((observe v).1, (observe v).2)).trans hcontent
end D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
