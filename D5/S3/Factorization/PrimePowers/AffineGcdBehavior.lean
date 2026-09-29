/- GID: D5/S3/Factorization/PrimePowers/AffineGcdBehavior
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/AffineGcdBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed S/D quotient coordinates have exact signed representatives and sufficient affine response laws. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import D5.S3.Arith.Congruence.PrimePowerAffineBehavior
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
/- The local code is exactly the quotient of signed sources by all affine
   responses, and every typed code has a signed (hence positive) source. -/
theorem local_encoding_complete (p h e : Nat) (hp : p.Prime)
    (hh : 1 ≤ h) (heh : e ≤ h) :
    (∀ X Y : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) =
        localEncoding p h e hp hh heh (Y : ZMod (p ^ h)) ↔
      ∀ (a : ℕ+) (b : Int),
        depth p h 0 ((((a : Nat) : Int) * X + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
        depth p h 0 ((((a : Nat) : Int) * Y + (p : Int) ^ e * b : Int) : ZMod (p ^ h))) ∧
    (∀ c : LocalCode p h e, ∃ X : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) = c) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ h) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have threshold (Z : Int) (j : Nat) (hj : j ≤ h) :
      j ≤ depth p h 0 (Z : ZMod (p ^ h)) ↔ (p : Int) ^ j ∣ Z := by
    have hs := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      p h hh).1 0 (Z : ZMod (p ^ h))).2 j hj
    simpa only [ZMod.cast_intCast (pow_dvd_pow p hj), ZMod.cast_zero,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] using hs
  let supplier := D5.S3.Arith.Congruence.PrimePowerAffineBehavior.local_classification
    p h e hp heh
  rcases supplier with
    ⟨depthFact, congruentFact, _positiveLift, affineLift, _wordForm,
      _wordRealize, responseFact, _unitCollapse⟩
  have signedDepth (X : Int) :
      D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h X =
        depth p h 0 (X : ZMod (p ^ h)) := by
    let d := D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h X
    let r := depth p h 0 (X : ZMod (p ^ h))
    have hdle : d ≤ h := (depthFact X).1
    have hrle : r ≤ h := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      p h hh).1 0 (X : ZMod (p ^ h))).1
    have hdx : (p : Int) ^ d ∣ X := by
      have hg := (depthFact X).2.1
      have hgdiv := Int.gcd_dvd_left X ((p : Int) ^ h)
      rw [hg] at hgdiv
      simpa only [Nat.cast_pow] using hgdiv
    have hdr : d ≤ r := (threshold X d hdle).2 hdx
    have hrx : (p : Int) ^ r ∣ X := (threshold X r hrle).1 le_rfl
    have hrgcd : p ^ r ∣ Int.gcd X ((p : Int) ^ h) := by
      exact_mod_cast (Int.dvd_coe_gcd hrx (pow_dvd_pow (p : Int) hrle))
    rw [(depthFact X).2.1] at hrgcd
    have hrd : r ≤ d := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hrgcd
    exact Nat.le_antisymm hdr hrd
  let embed : LocalCode p h e →
      (Nat × ZMod (p ^ (h - e))) ⊕ ZMod (p ^ (h - e)) :=
    fun c => match c with
      | .inl (r, u) => .inl (r.val, u.val)
      | .inr z => .inr z
  have embed_inj : Function.Injective embed := by
    intro c d hcd
    cases c with
    | inl cu =>
        cases d with
        | inl du =>
            rcases cu with ⟨r, u⟩
            rcases du with ⟨s, v⟩
            have hpairs : (r.val, (u : ZMod (p ^ (h - e)))) =
                (s.val, (v : ZMod (p ^ (h - e)))) := by
              exact Sum.inl.inj (by simpa only [embed] using hcd)
            have hrs : r = s := Fin.ext (congrArg Prod.fst hpairs)
            have huv : u = v := Units.ext (congrArg Prod.snd hpairs)
            simp only [hrs, huv]
        | inr z =>
            have : Sum.inl (cu.1.val, (cu.2 : ZMod (p ^ (h - e)))) =
                Sum.inr z := by simpa only [embed] using hcd
            cases this
    | inr z =>
        cases d with
        | inl du =>
            have : Sum.inr z =
                Sum.inl (du.1.val, (du.2 : ZMod (p ^ (h - e)))) := by
              simpa only [embed] using hcd
            cases this
        | inr v =>
            have hz : z = v := Sum.inr.inj (by simpa only [embed] using hcd)
            simp only [hz]
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
  have normalized (X : Int) :
      D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta p h e X =
        embed (localEncoding p h e hp hh heh (X : ZMod (p ^ h))) := by
    have hs := specification (X : ZMod (p ^ h)) X rfl
    cases hc : localEncoding p h e hp hh heh (X : ZMod (p ^ h)) with
    | inl ru =>
        rcases ru with ⟨r, u⟩
        rw [hc] at hs
        have hlow :
            D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h X < e := by
          rw [signedDepth X, hs.1]
          exact r.isLt
        simp only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
          if_pos hlow, embed, hc, Sum.inl.injEq]
        rw [signedDepth X, hs.1]
        exact Prod.ext rfl hs.2.2
    | inr z =>
        rw [hc] at hs
        have hdeep :
            ¬ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h X < e := by
          rw [signedDepth X]
          omega
        simpa only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
          if_neg hdeep, embed, hc, Sum.inr.injEq] using hs.2.2
  have response_iff (X Y : Int) :
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) =
        localEncoding p h e hp hh heh (Y : ZMod (p ^ h)) ↔
      ∀ (a : ℕ+) (b : Int),
        depth p h 0 ((((a : Nat) : Int) * X + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
        depth p h 0 ((((a : Nat) : Int) * Y + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) := by
    have heta : (localEncoding p h e hp hh heh (X : ZMod (p ^ h)) =
        localEncoding p h e hp hh heh (Y : ZMod (p ^ h))) ↔
        D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta p h e X =
          D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta p h e Y := by
      rw [normalized X, normalized Y]
      exact ⟨fun hc => congrArg embed hc, fun hc => embed_inj hc⟩
    rw [heta]
    constructor
    · intro he a b
      obtain ⟨A, B, hA, hB, hc⟩ := affineLift ((a : Nat) : Int) b
      have hr := (responseFact X Y).1.mp he A B hA hB
      have hleft := (congruentFact _ _ (hc X)).1
      have hright := (congruentFact _ _ (hc Y)).1
      have hs := hleft.trans (hr.trans hright.symm)
      simpa only [signedDepth] using hs
    · intro hr
      apply (responseFact X Y).1.mpr
      intro a b ha hb
      have hap : 0 < a.toNat := by omega
      have hs := hr ⟨a.toNat, hap⟩ b
      simpa only [← signedDepth, PNat.mk_coe,
        Int.toNat_of_nonneg (le_of_lt ha)] using hs

  refine ⟨response_iff, ?_⟩
  intro c
  cases c with
  | inr z =>
      let q := z.val
      let x : Nat := p ^ e * q
      have hxlt : x < p ^ h := by
        dsimp [x]
        have hq := z.val_lt
        have hpow : p ^ e * p ^ (h - e) = p ^ h := by
          rw [← pow_add, Nat.add_sub_of_le heh]
        exact ((Nat.mul_lt_mul_left (pow_pos hp.pos e)).mpr hq).trans_eq hpow
      have hxe : (p : Nat) ^ e ∣ x := by exact ⟨q, by simp [x, Nat.mul_comm]⟩
      have hdepth : e ≤ depth p h 0 ((x : Int) : ZMod (p ^ h)) :=
        (threshold (x : Int) e heh).2 (by exact_mod_cast hxe)
      refine ⟨(x : Int), ?_⟩
      unfold localEncoding
      dsimp only
      have hnot : ¬depth p h 0 ((x : Int) : ZMod (p ^ h)) < e := by omega
      rw [dif_neg hnot]
      have hxval : (((x : Int) : ZMod (p ^ h)).val) = x := by
        simpa only [Int.cast_natCast] using ZMod.val_natCast_of_lt hxlt
      rw [hxval]
      simp [x, Nat.mul_div_cancel_left _ (pow_pos hp.pos e)]
      exact ZMod.natCast_zmod_val z
  | inl ru =>
      let r := ru.1.val
      let u := ru.2
      let M := p ^ (h - e)
      by_cases hM : M = 1
      · let x : Nat := p ^ r
        have hxlt : x < p ^ h := by
          dsimp [x]
          exact Nat.pow_lt_pow_right hp.one_lt (by omega)
        have hnot : ¬ (r + 1 ≤ depth p h 0 ((x : Int) : ZMod (p ^ h))) := by
          intro hd
          have hd' := (threshold (x : Int) (r + 1) (by omega)).1 hd
          rw [show x = p ^ r by rfl, Nat.cast_pow] at hd'
          have honeI : (p : Int) ∣ 1 := by
            have hp0 : (p : Int) ≠ 0 := by exact_mod_cast hp.ne_zero
            apply Int.dvd_of_mul_dvd_mul_left (pow_ne_zero r hp0)
            simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hd'
          exact hp.not_dvd_one (by exact_mod_cast honeI)
        have hdepth : depth p h 0 ((x : Int) : ZMod (p ^ h)) = r := by
          have hle := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
            p h hh).1 0 ((x : Int) : ZMod (p ^ h))
          have hlow := (threshold (x : Int) r (by omega)).2 (by
            exact_mod_cast (dvd_refl (p ^ r)))
          omega
        have hrlt : r < e := ru.1.isLt
        refine ⟨(x : Int), ?_⟩
        unfold localEncoding
        dsimp only
        have hlt : depth p h 0 ((x : Int) : ZMod (p ^ h)) < e := by
          rw [hdepth]
          exact hrlt
        rw [dif_pos hlt]
        simp only [hdepth]
        apply congrArg Sum.inl
        apply Prod.ext
        · rfl
        · haveI : Subsingleton (ZMod M)ˣ := by rw [hM]; infer_instance
          exact Subsingleton.elim _ _
      · let q := (u : ZMod M).val
        have hqM : Nat.Coprime q M := ZMod.val_coe_unit_coprime u
        have hpq : ¬ p ∣ q := by
          intro hpq
          apply (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpq, ?_⟩) hqM
          rw [← pow_one p]
          have hk : 1 ≤ h - e := by
            have hk0 : h - e ≠ 0 := by
              intro hk0
              apply hM
              dsimp [M]
              simp [hk0]
            omega
          exact pow_dvd_pow p hk
        let x : Nat := p ^ r * q
        have hxlt : x < p ^ h := by
          dsimp [x]
          have hq := (u : ZMod M).val_lt
          have hpow : p ^ r * p ^ (h - e) < p ^ h := by
            rw [← pow_add]
            exact Nat.pow_lt_pow_right hp.one_lt (by omega)
          exact ((Nat.mul_lt_mul_left (pow_pos hp.pos r)).mpr hq).trans hpow
        have hnot : ¬ (r + 1 ≤ depth p h 0 ((x : Int) : ZMod (p ^ h))) := by
          intro hd
          have hd' := (threshold (x : Int) (r + 1) (by omega)).1 hd
          rw [show x = p ^ r * q by rfl, Nat.cast_mul, Nat.cast_pow] at hd'
          have hdq : p ∣ q := by
            have hp0 : (p : Int) ≠ 0 := by exact_mod_cast hp.ne_zero
            have hdqI : (p : Int) ∣ (q : Int) := by
              apply Int.dvd_of_mul_dvd_mul_left (pow_ne_zero r hp0)
              simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hd'
            exact_mod_cast hdqI
          exact hpq hdq
        have hdepth : depth p h 0 ((x : Int) : ZMod (p ^ h)) = r := by
          have hle := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
            p h hh).1 0 ((x : Int) : ZMod (p ^ h))
          have hlow := (threshold (x : Int) r (by omega)).2 (by
            exact_mod_cast (dvd_mul_right (p ^ r) q))
          omega
        have hrlt : r < e := ru.1.isLt
        refine ⟨(x : Int), ?_⟩
        unfold localEncoding
        dsimp only
        have hlt : depth p h 0 ((x : Int) : ZMod (p ^ h)) < e := by
          rw [hdepth]
          exact hrlt
        rw [dif_pos hlt]
        simp only [hdepth]
        have hxval : (((x : Int) : ZMod (p ^ h)).val) = x := by
          simpa only [Int.cast_natCast] using ZMod.val_natCast_of_lt hxlt
        apply congrArg Sum.inl
        apply Prod.ext
        · rfl
        · apply Units.ext
          change (((x : Int) : ZMod (p ^ h)).val / p ^ r : ZMod M) = (u : ZMod M)
          rw [hxval]
          rw [show x / p ^ r = q by
            change p ^ r * q / p ^ r = q
            simpa [Nat.mul_comm] using Nat.mul_div_left q (pow_pos hp.pos r)]
          exact ZMod.natCast_zmod_val (u : ZMod M)

#print axioms local_encoding_complete

end D5.S3.Factorization.PrimePowers.AffineGcdBehavior
