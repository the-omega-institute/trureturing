/- GID: D5/S3/Factorization/PrimePowers/AffineGcdBehavior
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/AffineGcdBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed S/D quotient coordinates have exact signed representatives and sufficient affine response laws. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.AffineGcdBehavior

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution (depth)

/-- The common divisor of the target modulus and every permitted addend. -/
def libraryGcd (H : Nat) (A : List ℕ+) : Nat :=
  A.foldr (fun c d => Nat.gcd c d) H

/-- An input is either a positive multiplier or an indexed library addition. -/
abbrev Operation (A : List ℕ+) := Sum ℕ+ (Fin A.length)

/-- The exact action on a positive source. -/
def update (A : List ℕ+) : Operation A → ℕ+ → ℕ+
  | .inl m, x => m * x
  | .inr i, x => x + A.get i

/-- Every finite mixed word, including the empty word, has one integer-affine
action, and its translation is divisible by the gcd of all permitted addends. -/
theorem affine_word_translation (H : Nat) (A : List ℕ+)
    (w : List (Operation A)) :
    ∃ a t : Nat, 0 < a ∧ libraryGcd H A ∣ t ∧
      ∀ x : ℕ+, (runWord (update A) w x).val = a * (x : ℕ) + t := by
  have addend_divides : ∀ (B : List ℕ+) (c : ℕ+),
      c ∈ B → libraryGcd H B ∣ (c : ℕ) := by
    intro B
    induction B with
    | nil =>
        intro c hc
        simp at hc
    | cons b bs ih =>
        intro c hc
        simp only [List.mem_cons] at hc
        simp only [libraryGcd]
        rcases hc with rfl | hc
        · exact Nat.gcd_dvd_left _ _
        · exact (Nat.gcd_dvd_right _ _).trans (ih c hc)
  induction w with
  | nil =>
      refine ⟨1, 0, by omega, dvd_zero _, ?_⟩
      intro x
      simp [runWord]
  | cons op rest ih =>
      obtain ⟨a, t, ha, ht, hrun⟩ := ih
      cases op with
      | inl m =>
          refine ⟨a * (m : ℕ), t, Nat.mul_pos ha m.pos, ht, ?_⟩
          intro x
          simpa [runWord, update, mul_assoc] using hrun (m * x)
      | inr i =>
          have hc := addend_divides A (A.get i) (List.get_mem A i)
          have htrans : libraryGcd H A ∣ a * (A.get i : ℕ) + t := by
            obtain ⟨k, hk⟩ := hc
            obtain ⟨l, hl⟩ := ht
            refine ⟨a * k + l, ?_⟩
            rw [hk, hl]
            rw [Nat.mul_add]
            simp only [Nat.mul_assoc, Nat.mul_comm]
          refine ⟨a, a * (A.get i : ℕ) + t, ha, htrans, ?_⟩
          intro x
          simpa [runWord, update, mul_add, add_assoc] using hrun (x + A.get i)

#print axioms affine_word_translation

/-- Every affine action whose translation is divisible by the library gcd
has one actual word: a positive multiplication followed by original additions. -/
theorem affine_action_realization (H : Nat) (hH : 2 ≤ H) (A : List ℕ+)
    (a : ℕ+) (t : Nat) (ht : libraryGcd H A ∣ t) :
    ∃ ws : List (Fin A.length), ∀ x : ℕ+,
      (((runWord (update A) (Sum.inl a :: ws.map Sum.inr) x).val : Nat) : ZMod H) =
        (((a : Nat) * (x : Nat) + t : Nat) : ZMod H) := by
  haveI : NeZero H := ⟨by omega⟩
  let S : Set (ZMod H) := Set.range (fun i : Fin A.length => ((A.get i : ℕ) : ZMod H))
  let C : AddSubgroup (ZMod H) := AddSubgroup.closure S
  have gcd_mem (B : List ℕ+)
      (hB : ∀ c : ℕ+, c ∈ B → (((c : ℕ) : ZMod H) ∈ C)) :
      ((libraryGcd H B : Nat) : ZMod H) ∈ C := by
    induction B with
    | nil =>
        simp [libraryGcd]
    | cons c bs ih =>
        have hc : (((c : ℕ) : ZMod H) ∈ C) :=
          hB c (List.mem_cons_self ..)
        have htail : ((libraryGcd H bs : Nat) : ZMod H) ∈ C := by
          apply ih
          intro b hb
          exact hB b (List.mem_cons_of_mem _ hb)
        have hbez : (((Nat.gcd (c : Nat) (libraryGcd H bs) : Nat) : ZMod H)) =
            (((c : Nat) : ZMod H) * (Nat.gcdA (c : Nat) (libraryGcd H bs) : ZMod H)) +
            (((libraryGcd H bs : Nat) : ZMod H) *
              (Nat.gcdB (c : Nat) (libraryGcd H bs) : ZMod H)) := by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
            congrArg (fun z : Int => (z : ZMod H))
              (Nat.gcd_eq_gcd_ab (c : Nat) (libraryGcd H bs))
        have hleft : ((c : Nat) : ZMod H) *
            (Nat.gcdA (c : Nat) (libraryGcd H bs) : ZMod H) ∈ C := by
          simpa [zsmul_eq_mul, mul_comm] using
            C.zsmul_mem hc (Nat.gcdA (c : Nat) (libraryGcd H bs))
        have hright : ((libraryGcd H bs : Nat) : ZMod H) *
            (Nat.gcdB (c : Nat) (libraryGcd H bs) : ZMod H) ∈ C := by
          simpa [zsmul_eq_mul, mul_comm] using
            C.zsmul_mem htail (Nat.gcdB (c : Nat) (libraryGcd H bs))
        have hsum := C.add_mem hleft hright
        change (((Nat.gcd (c : Nat) (libraryGcd H bs) : Nat) : ZMod H)) ∈ C
        rw [hbez]
        exact hsum
  have hd : (((libraryGcd H A : Nat) : ZMod H) ∈ C) := by
    apply gcd_mem A
    intro c hc
    exact AddSubgroup.subset_closure ⟨⟨A.idxOf c, by simpa using List.idxOf_lt_length_of_mem hc⟩,
      by simp⟩
  obtain ⟨b, rfl⟩ := ht
  have htarget : (((libraryGcd H A * b : Nat) : ZMod H) ∈ C) := by
    simpa [nsmul_eq_mul, mul_comm] using C.nsmul_mem hd b
  have hmonoid : ((libraryGcd H A * b : Nat) : ZMod H) ∈
      AddSubmonoid.closure S := by
    rw [← AddSubgroup.closure_toAddSubmonoid_of_finite]
    exact htarget
  have hwords : ∀ z : ZMod H, z ∈ AddSubmonoid.closure S →
      ∃ ws : List (Fin A.length),
        (ws.map fun i => ((A.get i : ℕ) : ZMod H)).sum = z := by
    intro z hz
    induction hz using AddSubmonoid.closure_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact ⟨[i], by simp⟩
    | zero => exact ⟨[], by simp⟩
    | add u v _ _ hu hv =>
        obtain ⟨wu, hwu⟩ := hu
        obtain ⟨wv, hwv⟩ := hv
        refine ⟨wu ++ wv, ?_⟩
        simp only [List.map_append, List.sum_append]
        rw [hwu, hwv]
  obtain ⟨ws, hws⟩ := hwords _ hmonoid
  refine ⟨ws, ?_⟩
  intro x
  have hrun (us : List (Fin A.length)) (y : ℕ+) :
      (((runWord (update A) (us.map Sum.inr) y).val : Nat) : ZMod H) =
        ((y : Nat) : ZMod H) +
          (us.map fun i => ((A.get i : ℕ) : ZMod H)).sum := by
    induction us generalizing y with
    | nil => simp [runWord]
    | cons i is ih =>
        simpa [runWord, update, add_assoc] using ih (y + A.get i)
  have haction := hrun ws (a * x)
  rw [hws] at haction
  simpa only [runWord, update, PNat.mul_coe, Nat.cast_add, Nat.cast_mul] using haction

#print axioms affine_action_realization

/-- The low tag records a depth and a unit; the deep tag records an unrestricted
quotient residue. Both coordinates use the modulus `p^(h-e)`. -/
abbrev LocalCode (p h e : Nat) :=
  Sum (Fin e × Units (ZMod (p ^ (h - e)))) (ZMod (p ^ (h - e)))

/-- The code is computed from the actual residue, its zero-aware depth, and
exact division of its canonical natural representative. -/
def localEncoding (p h e : Nat) (hp : p.Prime) (hh : 1 ≤ h) (heh : e ≤ h)
    (x : ZMod (p ^ h)) : LocalCode p h e := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ h) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := depth p h 0 x
  if hr : r < e then
    have threshold (j : Nat) (hj : j ≤ h) :
        j ≤ r ↔ p ^ j ∣ x.val := by
      have hs := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
        p h hh).1 0 x).2 j hj
      have hcast : (ZMod.cast x : ZMod (p ^ j)) = (x.val : ZMod (p ^ j)) := by
        simpa only [ZMod.natCast_zmod_val] using
          (ZMod.cast_natCast (R := ZMod (p ^ j)) (pow_dvd_pow p hj) x.val)
      rw [hcast, ZMod.cast_zero] at hs
      exact hs.trans (ZMod.natCast_eq_zero_iff _ _)
    have hd : p ^ r ∣ x.val := (threshold r (by omega)).1 le_rfl
    have hn : ¬ p ^ (r + 1) ∣ x.val := by
      intro hn
      have := (threshold (r + 1) (by omega)).2 hn
      omega
    have hq : ¬ p ∣ x.val / p ^ r := by
      intro hq
      apply hn
      rw [pow_succ]
      have hm := mul_dvd_mul_left (p ^ r) hq
      simpa only [Nat.mul_div_cancel' hd] using hm
    exact .inl (⟨r, hr⟩,
      ZMod.unitOfCoprime (x.val / p ^ r) (hp.coprime_pow_of_not_dvd hq))
  else
    exact .inr ((x.val / p ^ e : Nat) : ZMod (p ^ (h - e)))

/-- Exact signed quotient coordinates and their sufficient affine response law.
The response statement includes every positive multiplier and signed translation. -/
theorem local_encoding_signed_response (p h e : Nat) (hp : p.Prime)
    (hh : 1 ≤ h) (heh : e ≤ h) :
    (∀ (x : ZMod (p ^ h)) (X : Int), (X : ZMod (p ^ h)) = x →
      match localEncoding p h e hp hh heh x with
      | .inl (r, u) => depth p h 0 x = r.val ∧ (p : Int) ^ r.val ∣ X ∧
          ((X / (p : Int) ^ r.val : Int) : ZMod (p ^ (h - e))) = u
      | .inr z => e ≤ depth p h 0 x ∧ (p : Int) ^ e ∣ X ∧
          ((X / (p : Int) ^ e : Int) : ZMod (p ^ (h - e))) = z) ∧
    (∀ X Y : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) =
        localEncoding p h e hp hh heh (Y : ZMod (p ^ h)) →
      ∀ (a : ℕ+) (b : Int),
        depth p h 0 ((((a : Nat) : Int) * X + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
        depth p h 0 ((((a : Nat) : Int) * Y + (p : Int) ^ e * b : Int) : ZMod (p ^ h))) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ h) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have specification : ∀ (x : ZMod (p ^ h)) (X : Int),
      (X : ZMod (p ^ h)) = x →
      match localEncoding p h e hp hh heh x with
      | .inl (r, u) => depth p h 0 x = r.val ∧ (p : Int) ^ r.val ∣ X ∧
          ((X / (p : Int) ^ r.val : Int) : ZMod (p ^ (h - e))) = u
      | .inr z => e ≤ depth p h 0 x ∧ (p : Int) ^ e ∣ X ∧
          ((X / (p : Int) ^ e : Int) : ZMod (p ^ (h - e))) = z := by
    intro x X hX
    have threshold (j : Nat) (hj : j ≤ h) :
        j ≤ depth p h 0 x ↔ p ^ j ∣ x.val := by
      have hs := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
        p h hh).1 0 x).2 j hj
      have hcast : (ZMod.cast x : ZMod (p ^ j)) = (x.val : ZMod (p ^ j)) := by
        simpa only [ZMod.natCast_zmod_val] using
          (ZMod.cast_natCast (R := ZMod (p ^ j)) (pow_dvd_pow p hj) x.val)
      rw [hcast, ZMod.cast_zero] at hs
      exact hs.trans (ZMod.natCast_eq_zero_iff _ _)
    have quotient (j : Nat) (hje : j ≤ e) (hd : p ^ j ∣ x.val) :
        (p : Int) ^ j ∣ X ∧
        ((X / (p : Int) ^ j : Int) : ZMod (p ^ (h - e))) =
          ((x.val / p ^ j : Nat) : ZMod (p ^ (h - e))) := by
      have hxval : (X : ZMod (p ^ h)) = (x.val : ZMod (p ^ h)) := by
        simpa only [ZMod.natCast_zmod_val] using hX
      obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub
        X (x.val : Int) (p ^ h)).1 (by exact_mod_cast hxval)
      have hval : (x.val : Int) = (p : Int) ^ j * (x.val / p ^ j : Nat) := by
        exact_mod_cast (Nat.mul_div_cancel' hd).symm
      have hpow : (p : Int) ^ h = (p : Int) ^ j * (p : Int) ^ (h - j) := by
        rw [← pow_add, Nat.add_sub_of_le (hje.trans heh)]
      have hXe : X = (p : Int) ^ j *
          ((x.val / p ^ j : Nat) - (p : Int) ^ (h - j) * t) := by
        simp only [Nat.cast_pow] at ht
        rw [hval, hpow] at ht
        nlinarith only [ht]
      constructor
      · exact ⟨_, hXe⟩
      · have hj0 : (p : Int) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
        rw [hXe, Int.mul_ediv_cancel_left _ hj0]
        have hz : (Int.cast ((p : Int) ^ (h - j)) : ZMod (p ^ (h - e))) = 0 := by
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
          exact_mod_cast pow_dvd_pow p (by omega : h - e ≤ h - j)
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hz, zero_mul, sub_zero]
    unfold localEncoding
    dsimp only
    split_ifs with hr
    · dsimp only
      refine ⟨rfl, ?_⟩
      have hd := (threshold (depth p h 0 x) (by omega)).1 le_rfl
      simpa only [ZMod.coe_unitOfCoprime] using quotient _ (le_of_lt hr) hd
    · dsimp only
      refine ⟨by omega, ?_⟩
      exact quotient e le_rfl ((threshold e heh).1 (by omega))
  refine ⟨specification, ?_⟩
  intro X Y hcode a b
  have threshold (Z : Int) (j : Nat) (hj : j ≤ h) :
      j ≤ depth p h 0 (Z : ZMod (p ^ h)) ↔ (p : Int) ^ j ∣ Z := by
    have hs := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      p h hh).1 0 (Z : ZMod (p ^ h))).2 j hj
    simpa only [ZMod.cast_intCast (pow_dvd_pow p hj), ZMod.cast_zero,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] using hs
  have same (hd : (p : Int) ^ h ∣ ((a : Nat) : Int) * (Y - X)) :
      depth p h 0 ((((a : Nat) : Int) * X + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
      depth p h 0 ((((a : Nat) : Int) * Y + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) := by
    have hd' : ((p ^ h : Nat) : Int) ∣
        (((a : Nat) : Int) * Y + (p : Int) ^ e * b) -
          (((a : Nat) : Int) * X + (p : Int) ^ e * b) := by
      rw [Nat.cast_pow]
      convert hd using 1 <;> ring
    exact congrArg (depth p h 0)
      ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 hd')
  have hx := specification (X : ZMod (p ^ h)) X rfl
  have hy := specification (Y : ZMod (p ^ h)) Y rfl
  rw [← hcode] at hy
  cases hc : localEncoding p h e hp hh heh (X : ZMod (p ^ h)) with
  | inr z =>
      rw [hc] at hx hy
      have hq := (ZMod.intCast_eq_intCast_iff_dvd_sub
        (X / (p : Int) ^ e) (Y / (p : Int) ^ e) (p ^ (h - e))).1
          (hx.2.2.trans hy.2.2.symm)
      have hd := mul_dvd_mul_left ((p : Int) ^ e) hq
      have hpow : (p : Int) ^ e * ((p ^ (h - e) : Nat) : Int) = (p : Int) ^ h := by
        rw [Nat.cast_pow, ← pow_add, Nat.add_sub_of_le heh]
      rw [hpow, mul_sub, Int.mul_ediv_cancel' hx.2.1,
        Int.mul_ediv_cancel' hy.2.1] at hd
      exact same (hd.mul_left _)
  | inl ru =>
      rcases ru with ⟨r, u⟩
      rw [hc] at hx hy
      have hq := (ZMod.intCast_eq_intCast_iff_dvd_sub
        (X / (p : Int) ^ r.val) (Y / (p : Int) ^ r.val) (p ^ (h - e))).1
          (hx.2.2.trans hy.2.2.symm)
      have hdiff : (p : Int) ^ (r.val + (h - e)) ∣ Y - X := by
        have hd := mul_dvd_mul_left ((p : Int) ^ r.val) hq
        rw [Nat.cast_pow, ← pow_add, mul_sub, Int.mul_ediv_cancel' hy.2.1,
          Int.mul_ediv_cancel' hx.2.1] at hd
        exact hd
      let s := padicValInt p ((a : Nat) : Int)
      by_cases hcross : e ≤ r.val + s
      · have hd := mul_dvd_mul (padicValInt_dvd (p := p) ((a : Nat) : Int)) hdiff
        rw [← pow_add] at hd
        exact same ((pow_dvd_pow (p : Int) (by omega : h ≤ s + (r.val + (h - e)))).trans hd)
      · have hrs : r.val + s + 1 ≤ e := by omega
        have low_response (Z : Int) (hzdepth : depth p h 0 (Z : ZMod (p ^ h)) = r.val) :
            depth p h 0 ((((a : Nat) : Int) * Z + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
              r.val + s := by
          clear specification hcode hc hx hy hq hdiff
          have hrh : r.val < h := r.isLt.trans_le heh
          have hd : (p : Int) ^ r.val ∣ Z := (threshold Z r.val (by omega)).1 (by omega)
          have hn : ¬ (p : Int) ^ (r.val + 1) ∣ Z := by
            intro hn
            have := (threshold Z (r.val + 1) (by omega)).2 hn
            omega
          have hz : Z ≠ 0 := by
            intro hz
            apply hn
            rw [hz]
            exact dvd_zero _
          have hv : padicValInt p Z = r.val := by
            have hl := ((padicValInt_dvd_iff (p := p) r.val Z).1 hd).resolve_left hz
            have hu : ¬ r.val + 1 ≤ padicValInt p Z := by
              intro hu
              exact hn ((padicValInt_dvd_iff (p := p) (r.val + 1) Z).2 (Or.inr hu))
            omega
          have ha : ((a : Nat) : Int) ≠ 0 := by exact_mod_cast a.ne_zero
          have hval : padicValInt p (((a : Nat) : Int) * Z) = r.val + s := by
            rw [padicValInt.mul ha hz, hv]
            exact Nat.add_comm _ _
          have hprod : ((a : Nat) : Int) * Z ≠ 0 := mul_ne_zero ha hz
          have hbase : (p : Int) ^ (r.val + s) ∣ ((a : Nat) : Int) * Z := by
            rw [padicValInt_dvd_iff]
            exact Or.inr (by omega)
          have hnext : ¬ (p : Int) ^ (r.val + s + 1) ∣ ((a : Nat) : Int) * Z := by
            intro hd
            have := ((padicValInt_dvd_iff (p := p) (r.val + s + 1) _).1 hd).resolve_left hprod
            omega
          have ht : (p : Int) ^ (r.val + s + 1) ∣ (p : Int) ^ e * b :=
            (pow_dvd_pow (p : Int) hrs).mul_right b
          have hout : r.val + s ≤
              depth p h 0 ((((a : Nat) : Int) * Z + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) :=
            (threshold (((a : Nat) : Int) * Z + (p : Int) ^ e * b)
              (r.val + s) ((Nat.le_succ _).trans (hrs.trans heh))).2
              (dvd_add hbase ((pow_dvd_pow (p : Int) ((Nat.le_succ _).trans hrs)).mul_right b))
          have hnout : ¬ r.val + s + 1 ≤
              depth p h 0 ((((a : Nat) : Int) * Z + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) := by
            intro hnout
            have hhout := (threshold (((a : Nat) : Int) * Z + (p : Int) ^ e * b)
              (r.val + s + 1) (hrs.trans heh)).1 hnout
            apply hnext
            simpa only [add_sub_cancel_right] using dvd_sub hhout ht
          omega
        exact (low_response X hx.1).trans (low_response Y hy.1).symm

#print axioms localEncoding
#print axioms local_encoding_signed_response


end D5.S3.Factorization.PrimePowers.AffineGcdBehavior
