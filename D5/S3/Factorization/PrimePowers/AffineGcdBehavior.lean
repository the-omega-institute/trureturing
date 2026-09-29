/- GID: D5/S3/Factorization/PrimePowers/AffineGcdBehavior
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/AffineGcdBehavior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive mixed words retain an affine form with gcd-divisible translation. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.AffineGcdBehavior

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

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

/-- Distinct low quotient coordinates admit a concrete local affine continuation:
one resulting residue is zero and the other has strictly smaller depth. -/
theorem affine_low_quotient_separation (p h e r : Nat) (hp : p.Prime)
    (heh : e ≤ h) (hre : r < e) (u v : Int)
    (huv : (u : ZMod (p ^ (h - e))) ≠ (v : ZMod (p ^ (h - e)))) :
    ∃ a : Nat, 0 < a ∧ ∃ b : Int,
      ∀ x y : Int,
        (x : ZMod (p ^ h)) = ((p : Int) ^ r * u : ZMod (p ^ h)) →
        (y : ZMod (p ^ h)) = ((p : Int) ^ r * v : ZMod (p ^ h)) →
        D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p h 0
          ((a : Int) * x + (p : Int) ^ e * b : ZMod (p ^ h)) = h ∧
        D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p h 0
          ((a : Int) * y + (p : Int) ^ e * b : ZMod (p ^ h)) < h := by
  letI : Fact p.Prime := ⟨hp⟩
  have htop (z : ZMod (p ^ h)) :
      D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p h 0 z = h ↔
        z = 0 :=
    (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result p h (by omega)).2.1 0 z
  have hquot : ¬ ((p ^ (h - e) : Nat) : Int) ∣ v - u := by
    intro hd
    apply huv
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub u v (p ^ (h - e))).2 hd
  have hscale : ¬ ((p ^ h : Nat) : Int) ∣ ((p ^ e : Nat) : Int) * (v - u) := by
    intro hd
    have hpow : ((p ^ h : Nat) : Int) =
        ((p ^ e : Nat) : Int) * ((p ^ (h - e) : Nat) : Int) := by
      rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_of_le heh]
    rw [hpow] at hd
    exact hquot ((mul_dvd_mul_iff_left
      (by exact_mod_cast pow_ne_zero e hp.ne_zero)).1 hd)
  have hmul : ((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r = (p : Int) ^ e := by
    rw [Nat.cast_pow, ← pow_add, Nat.sub_add_cancel (le_of_lt hre)]
  have hzero :
      D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p h 0
        (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * u +
          (p : Int) ^ e * -u : ZMod (p ^ h)) = h := by
    apply (htop _).2
    have hz : ((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * u +
        (p : Int) ^ e * -u = 0 := by
      rw [hmul]
      ring
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_neg, Int.cast_zero] using
      congrArg (fun z : Int => (z : ZMod (p ^ h))) hz
  have hlt :
      D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p h 0
        (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
          (p : Int) ^ e * -u : ZMod (p ^ h)) < h := by
    have hnonzero :
        (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
          (p : Int) ^ e * -u : ZMod (p ^ h)) ≠ 0 := by
      intro hz
      have hz' : ((((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
          (p : Int) ^ e * -u : Int) : ZMod (p ^ h)) = 0 := by
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          Int.cast_neg] using hz
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz'
      apply hscale
      have heq : ((p ^ e : Nat) : Int) * (v - u) =
          ((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
            (p : Int) ^ e * -u := by
        simp only [Nat.cast_pow]
        have hmul' : (p : Int) ^ (e - r) * (p : Int) ^ r = (p : Int) ^ e := by
          simpa only [Nat.cast_pow] using hmul
        rw [hmul']
        ring
      rw [heq]
      exact hd
    have hbound :=
      (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result p h (by omega)).1
        0 (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
          (p : Int) ^ e * -u : ZMod (p ^ h))
    have hne_depth :
        D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p h 0
          (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
            (p : Int) ^ e * -u : ZMod (p ^ h)) ≠ h := by
      intro heq
      exact hnonzero ((htop _).1 heq)
    exact Nat.lt_of_le_of_ne hbound.1 hne_depth
  refine ⟨p ^ (e - r), pow_pos hp.pos _, -u, ?_⟩
  intro x y hx hy
  have hxout :
      (((p ^ (e - r) : Nat) : Int) * x + (p : Int) ^ e * -u : ZMod (p ^ h)) =
      (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * u +
        (p : Int) ^ e * -u : ZMod (p ^ h)) := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_neg] at hx ⊢
    rw [hx]
    ring
  have hyout :
      (((p ^ (e - r) : Nat) : Int) * y + (p : Int) ^ e * -u : ZMod (p ^ h)) =
      (((p ^ (e - r) : Nat) : Int) * (p : Int) ^ r * v +
        (p : Int) ^ e * -u : ZMod (p ^ h)) := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_neg] at hy ⊢
    rw [hy]
    ring
  constructor
  · simpa only [Int.cast_neg] using (hxout.symm ▸ hzero)
  · simpa only [Int.cast_neg] using (hyout.symm ▸ hlt)

#print axioms affine_low_quotient_separation

end D5.S3.Factorization.PrimePowers.AffineGcdBehavior
