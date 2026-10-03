/- GID: D5/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-axis codes classify library words and have positive common sources. -/

import D5.S3.Factorization.PrimePowers.AffineGcdBehavior
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior

open AffineGcdBehavior
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution (depth)

/-- The tuple is computed from one actual positive source on the actual prime axes. -/
def globalEncoding (H : Nat) (hH : 2 ≤ H) (A : List ℕ+) (x : ℕ+) :
    (p : H.primeFactors) → LocalCode p.val (H.factorization p.val)
      ((libraryGcd H A).factorization p.val) := by
  have hd : libraryGcd H A ∣ H := by
    induction A with
    | nil => exact dvd_refl H
    | cons c cs ih => exact (Nat.gcd_dvd_right (c : Nat) _).trans ih
  have hH0 : H ≠ 0 := by omega
  have hd0 : libraryGcd H A ≠ 0 := by
    intro hz
    rw [hz] at hd
    exact hH0 (by simpa using hd)
  intro p
  have hp := Nat.prime_of_mem_primeFactors p.property
  exact localEncoding p.val (H.factorization p.val) ((libraryGcd H A).factorization p.val)
    hp (hp.factorization_pos_of_dvd hH0 (Nat.dvd_of_mem_primeFactors p.property))
    ((Nat.factorization_le_iff_dvd hd0 hH0).2 hd p.val)
    ((x : Nat) : ZMod (p.val ^ H.factorization p.val))

/-- Equality of the actual codes is exactly equality of all original-library gcd
and quotient readouts. A separating word uses the same two positive sources;
all local labels are jointly attained by one positive source. -/
theorem global_encoding_complete (H : Nat) (hH : 2 ≤ H) (A : List ℕ+) :
    (∀ x y : ℕ+, globalEncoding H hH A x = globalEncoding H hH A y ↔
      ∀ w : List (Operation A),
        Nat.gcd (runWord (update A) w x).val H =
          Nat.gcd (runWord (update A) w y).val H) ∧
    (∀ x y : ℕ+, globalEncoding H hH A x = globalEncoding H hH A y ↔
      ∀ w : List (Operation A),
        H / Nat.gcd (runWord (update A) w x).val H =
          H / Nat.gcd (runWord (update A) w y).val H) ∧
    (∀ x y : ℕ+, globalEncoding H hH A x ≠ globalEncoding H hH A y →
      ∃ (p : H.primeFactors) (a : ℕ+) (ws : List (Fin A.length)),
        (Nat.gcd (runWord (update A) (Sum.inl a :: ws.map Sum.inr) x).val H).factorization p.val ≠
          (Nat.gcd (runWord (update A) (Sum.inl a :: ws.map Sum.inr) y).val H).factorization p.val) ∧
    Function.Surjective (globalEncoding H hH A) := by
  classical
  let d := libraryGcd H A
  have hH0 : H ≠ 0 := by omega
  letI : NeZero H := ⟨hH0⟩
  have hdH : d ∣ H := by
    change libraryGcd H A ∣ H
    induction A with
    | nil => exact dvd_refl H
    | cons c cs ih => exact (Nat.gcd_dvd_right (c : Nat) _).trans ih
  have hd0 : d ≠ 0 := by
    intro hz
    rw [hz] at hdH
    exact hH0 (by simpa using hdH)
  have axes (p : H.primeFactors) : p.val.Prime ∧ 1 ≤ H.factorization p.val ∧
      d.factorization p.val ≤ H.factorization p.val := by
    have hp := Nat.prime_of_mem_primeFactors p.property
    exact ⟨hp, hp.factorization_pos_of_dvd hH0 (Nat.dvd_of_mem_primeFactors p.property),
      (Nat.factorization_le_iff_dvd hd0 hH0).2 hdH p.val⟩
  have gcd_depth (p : H.primeFactors) (z : ℕ+) :
      (Nat.gcd z.val H).factorization p.val =
        depth p.val (H.factorization p.val) 0
          (z.val : ZMod (p.val ^ H.factorization p.val)) := by
    have hp := (axes p).1
    have hh := (axes p).2.1
    letI : Fact p.val.Prime := ⟨hp⟩
    let h := H.factorization p.val
    have bound := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      p.val h hh).1 0 (z.val : ZMod (p.val ^ h))
    have threshold (j : Nat) (hj : j ≤ h) :
        j ≤ depth p.val h 0 (z.val : ZMod (p.val ^ h)) ↔ j ≤ z.val.factorization p.val := by
      have ht := bound.2 j hj
      rw [ZMod.cast_natCast (pow_dvd_pow p.val hj), ZMod.cast_zero,
        ZMod.natCast_eq_zero_iff] at ht
      exact ht.trans (hp.pow_dvd_iff_le_factorization z.ne_zero)
    have hl := (threshold (min (z.val.factorization p.val) h) (min_le_right _ _)).2
      (min_le_left _ _)
    have hu := (threshold _ bound.1).1 le_rfl
    rw [Nat.factorization_gcd z.ne_zero hH0, Finsupp.inf_apply]
    change min (z.val.factorization p.val) h = _
    exact Nat.le_antisymm hl (le_min hu bound.1)
  -- The cofactor is a unit only on the chosen axis. Other axes may move.
  have lift_translation (p : H.primeFactors) (delta : Int) :
      ∃ b : Nat, ((d * b : Nat) : ZMod (p.val ^ H.factorization p.val)) =
        (((p.val : Int) ^ d.factorization p.val * delta : Int) :
          ZMod (p.val ^ H.factorization p.val)) := by
    let h := H.factorization p.val
    let e := d.factorization p.val
    have hp := (axes p).1
    have heh : e ≤ h := (axes p).2.2
    by_cases he : e = h
    · refine ⟨0, ?_⟩
      simp only [Nat.mul_zero, Nat.cast_zero, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [show d.factorization p.val = h from he]
      have hz : (p.val : ZMod (p.val ^ h)) ^ h = 0 := by
        rw [← Nat.cast_pow]
        exact (ZMod.natCast_eq_zero_iff _ _).2 dvd_rfl
      rw [hz, zero_mul]
    · let M := p.val ^ (h - e)
      letI : NeZero M := ⟨pow_ne_zero _ hp.ne_zero⟩
      let t := d / p.val ^ e
      have hcop : Nat.Coprime t M := (Nat.coprime_ordCompl hp hd0).symm.pow_right (h - e)
      let u := ZMod.unitOfCoprime t hcop
      let b := (((u⁻¹ : Units (ZMod M)) : ZMod M) * (delta : ZMod M)).val
      have hcoord : ((t * b : Nat) : ZMod M) = (delta : ZMod M) := by
        simp only [Nat.cast_mul]
        change (u : ZMod M) * (b : ZMod M) = _
        rw [show (b : ZMod M) = (u⁻¹ : Units (ZMod M)) * (delta : ZMod M) from
          ZMod.natCast_zmod_val _]
        exact Units.mul_inv_cancel_left u (delta : ZMod M)
      have hm := (ZMod.intCast_eq_intCast_iff_dvd_sub (t * b : Nat) delta M).1
        (by simpa only [Int.cast_natCast] using hcoord)
      have hmul := mul_dvd_mul_left ((p.val : Int) ^ e) hm
      have hpow : (p.val : Int) ^ e * (M : Int) = (p.val : Int) ^ h := by
        dsimp [M]
        rw [← pow_add, Nat.add_sub_of_le heh]
      have hdt : p.val ^ e * t = d := Nat.mul_div_cancel' (Nat.ordProj_dvd d p.val)
      have hdti : (p.val : Int) ^ e * (t : Int) = (d : Int) := by exact_mod_cast hdt
      rw [hpow, mul_sub, Nat.cast_mul, ← mul_assoc, hdti] at hmul
      refine ⟨b, ?_⟩
      have hc := (ZMod.intCast_eq_intCast_iff_dvd_sub (d * b : Nat)
        ((p.val : Int) ^ e * delta) (p.val ^ h)).2
        (by simpa only [Nat.cast_pow, Nat.cast_mul] using hmul)
      simpa only [Int.cast_natCast] using hc
  have realize (p : H.primeFactors) (a : ℕ+) (delta : Int) :
      ∃ ws : List (Fin A.length), ∀ x : ℕ+,
        ((runWord (update A) (Sum.inl a :: ws.map Sum.inr) x).val :
          ZMod (p.val ^ H.factorization p.val)) =
        ((((a : Nat) : Int) * (x.val : Int) +
          (p.val : Int) ^ d.factorization p.val * delta : Int) :
          ZMod (p.val ^ H.factorization p.val)) := by
    obtain ⟨b, hb⟩ := lift_translation p delta
    obtain ⟨ws, hw⟩ := affine_action_realization H hH A a (d * b) (dvd_mul_right d b)
    refine ⟨ws, ?_⟩
    intro x
    have hc := congrArg (ZMod.castHom (Nat.ordProj_dvd H p.val)
      (ZMod (p.val ^ H.factorization p.val))) (hw x)
    simp only [map_natCast] at hc
    rw [Nat.cast_add, Nat.cast_mul, hb] at hc
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hc
  have iff_gcd (x y : ℕ+) : globalEncoding H hH A x = globalEncoding H hH A y ↔
      ∀ w : List (Operation A), Nat.gcd (runWord (update A) w x).val H =
        Nat.gcd (runWord (update A) w y).val H := by
    constructor
    · intro hcode w
      obtain ⟨a, t, ha, ht, hw⟩ := affine_word_translation H A w
      apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_right hH0) (Nat.gcd_ne_zero_right hH0)
      intro p
      by_cases hpH : p ∈ H.primeFactors
      · let q : H.primeFactors := ⟨p, hpH⟩
        have hp := (axes q).1
        have hh := (axes q).2.1
        have heh := (axes q).2.2
        have hlocal := congrFun hcode q
        change localEncoding p (H.factorization p) (d.factorization p) hp hh heh
          (x.val : ZMod (p ^ H.factorization p)) =
          localEncoding p (H.factorization p) (d.factorization p) hp hh heh
            (y.val : ZMod (p ^ H.factorization p)) at hlocal
        have hpt : p ^ d.factorization p ∣ t := (Nat.ordProj_dvd d p).trans ht
        have htI : (p : Int) ^ d.factorization p * (t / p ^ d.factorization p : Nat) = t := by
          exact_mod_cast Nat.mul_div_cancel' hpt
        have hresp := (local_encoding_complete p (H.factorization p) (d.factorization p)
          hp hh heh).1 (x.val : Int) (y.val : Int) |>.1 (by
            simpa only [Int.cast_natCast] using hlocal)
        have hr := hresp (⟨a, ha⟩ : ℕ+) (t / p ^ d.factorization p : Nat)
        rw [gcd_depth q, gcd_depth q]
        simpa only [PNat.mk_coe, htI, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          ← Nat.cast_mul, ← Nat.cast_add, hw x, hw y] using hr
      · have hHfact : H.factorization p = 0 := by
          exact Finsupp.notMem_support_iff.1 (by simpa only [Nat.support_factorization] using hpH)
        have hxle := (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_right hH0) hH0).2
          (Nat.gcd_dvd_right (runWord (update A) w x).val H) p
        have hyle := (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_right hH0) hH0).2
          (Nat.gcd_dvd_right (runWord (update A) w y).val H) p
        omega
    · intro hw
      funext p
      have hp := (axes p).1
      have hh := (axes p).2.1
      have heh := (axes p).2.2
      change localEncoding p.val (H.factorization p.val) (d.factorization p.val) hp hh heh
        (x.val : ZMod (p.val ^ H.factorization p.val)) =
        localEncoding p.val (H.factorization p.val) (d.factorization p.val) hp hh heh
          (y.val : ZMod (p.val ^ H.factorization p.val))
      have hc := (local_encoding_complete p.val (H.factorization p.val) (d.factorization p.val)
        hp hh heh).1 (x.val : Int) (y.val : Int) |>.2 (by
          intro a delta
          obtain ⟨ws, hws⟩ := realize p a delta
          have heq := congrArg (fun n : Nat => n.factorization p.val)
            (hw (Sum.inl a :: ws.map Sum.inr))
          rw [gcd_depth p, gcd_depth p, hws x, hws y] at heq
          exact heq)
      simpa only [Int.cast_natCast] using hc
  have quotient_iff (z v : ℕ+) : H / Nat.gcd z.val H = H / Nat.gcd v.val H ↔
      Nat.gcd z.val H = Nat.gcd v.val H := by
    constructor
    · intro heq
      have hz := Nat.mul_div_cancel' (Nat.gcd_dvd_right z.val H)
      have hv := Nat.mul_div_cancel' (Nat.gcd_dvd_right v.val H)
      rw [← heq] at hv
      have hpos : 0 < H / Nat.gcd z.val H := Nat.div_pos
        (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right z.val H))
        (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right hH0))
      exact Nat.eq_of_mul_eq_mul_right hpos (hz.trans hv.symm)
    · intro heq
      rw [heq]
  refine ⟨iff_gcd, ?_, ?_, ?_⟩
  · intro x y
    rw [iff_gcd]
    exact forall_congr' (fun w => (quotient_iff _ _).symm)
  · intro x y hne
    have haxis : ∃ p : H.primeFactors, globalEncoding H hH A x p ≠
        globalEncoding H hH A y p := by
      by_contra hn
      push Not at hn
      exact hne (funext hn)
    obtain ⟨p, hpne⟩ := haxis
    have hp := (axes p).1
    have hh := (axes p).2.1
    have heh := (axes p).2.2
    have hresp : ¬ ∀ (a : ℕ+) (delta : Int),
        depth p.val (H.factorization p.val) 0
          (((a.val : Int) * (x.val : Int) + (p.val : Int) ^ d.factorization p.val * delta : Int) :
            ZMod (p.val ^ H.factorization p.val)) =
        depth p.val (H.factorization p.val) 0
          (((a.val : Int) * (y.val : Int) + (p.val : Int) ^ d.factorization p.val * delta : Int) :
            ZMod (p.val ^ H.factorization p.val)) := by
      intro hr
      apply hpne
      simpa only [globalEncoding, Int.cast_natCast] using
        ((local_encoding_complete p.val (H.factorization p.val) (d.factorization p.val)
          hp hh heh).1 (x.val : Int) (y.val : Int) |>.2 hr)
    push Not at hresp
    obtain ⟨a, delta, hsep⟩ := hresp
    obtain ⟨ws, hws⟩ := realize p a delta
    refine ⟨p, a, ws, ?_⟩
    rw [gcd_depth p, gcd_depth p, hws x, hws y]
    exact hsep
  · intro c
    have local_sources (p : H.primeFactors) : ∃ X : Int,
        localEncoding p.val (H.factorization p.val) (d.factorization p.val)
          (axes p).1 (axes p).2.1 (axes p).2.2
          (X : ZMod (p.val ^ H.factorization p.val)) = c p :=
      (local_encoding_complete p.val (H.factorization p.val) (d.factorization p.val)
        (axes p).1 (axes p).2.1 (axes p).2.2).2 (c p)
    choose X hX using local_sources
    let E := ZMod.equivPi H hH0
    let z : ZMod H := E.symm (fun p => (X p : ZMod (p.val ^ H.factorization p.val)))
    let x : ℕ+ := ⟨z.val + H, by omega⟩
    refine ⟨x, ?_⟩
    funext p
    have hz : E z p = (X p : ZMod (p.val ^ H.factorization p.val)) :=
      congrFun (E.apply_symm_apply _) p
    have hrep := congrFun (congrArg E (ZMod.natCast_zmod_val z)) p
    simp only [map_natCast, Pi.natCast_apply] at hrep
    have hres : (x.val : ZMod (p.val ^ H.factorization p.val)) =
        (X p : ZMod (p.val ^ H.factorization p.val)) := by
      change ((z.val + H : Nat) : ZMod (p.val ^ H.factorization p.val)) = _
      rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd H p.val), add_zero]
      exact hrep.trans hz
    change localEncoding p.val (H.factorization p.val) (d.factorization p.val)
      (axes p).1 (axes p).2.1 (axes p).2.2
      (x.val : ZMod (p.val ^ H.factorization p.val)) = c p
    rw [hres]
    exact hX p

#print axioms globalEncoding
#print axioms global_encoding_complete

end D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior
