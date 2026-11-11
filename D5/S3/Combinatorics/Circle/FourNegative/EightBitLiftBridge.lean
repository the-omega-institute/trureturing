/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftBridge
   generality: I
   mirror-B: none(waiver:consumed-by-eight-bit-physical-lift)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal physical eight-bit insertion and its charge-prefix proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.EightBitLiftSchedule

/-! # Recovering the literal old order and the fresh cut -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShortening RunFirstEarTransport
open private ear_prefix ear_perm from D5.S3.Combinatorics.Circle.RunFirstEarTransport

def oldPart {k : ℕ} (w : List (Fin (k + 1))) : List (Fin k) :=
  w.filterMap (Fin.lastCases none (fun i => some i))

theorem oldPart_sum {k : ℕ} (w : List (Fin (k + 1))) :
    ((oldPart w).map (actualSource k 85)).sum = (w.map (fullFirst k)).sum := by
  induction w with
  | nil => simp [oldPart]
  | cons j w ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [oldPart, fullFirst] using ih
      · simpa [oldPart, fullFirst] using
          congrArg (actualSource k 85 i + ·) ih

theorem oldPart_perm {k : ℕ} (w : List (Fin (k + 1)))
    (hw : w.Perm (List.finRange (k + 1))) :
    (oldPart w).Perm (List.finRange k) := by
  have h := List.Perm.filterMap (Fin.lastCases none (fun i : Fin k => some i)) hw
  change (oldPart w).Perm (oldPart (List.finRange (k + 1))) at h
  rw [List.finRange_succ_last] at h
  simpa [oldPart, List.filterMap_append, List.filterMap_map, Function.comp_def] using h

theorem oldPart_restore {k : ℕ} (w : List (Fin (k + 1))) (hw : Fin.last k ∉ w) :
    (oldPart w).map Fin.castSucc = w := by
  induction w with
  | nil => simp [oldPart]
  | cons j w ih =>
      have hj : j ≠ Fin.last k := by intro h; apply hw; simp [h]
      have hn : Fin.last k ∉ w := by intro h; apply hw; simp [h]
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      simpa [oldPart] using congrArg (i.castSucc :: ·) (ih hn)

theorem next_modulus_half (k : ℕ) : modulus (k + 1) / 2 = modulus k := by
  unfold modulus
  rw [pow_succ]
  omega

theorem jointWord_of_orders (k : ℕ) (sigma : List (Fin k)) (cut : ℕ)
    (hcut : cut ≤ k) (hold : OriginalOrder k 85 sigma)
    (hnew : OriginalOrder (k + 1) 170 (earWord k sigma cut)) :
    JointWord k (earWord k sigma cut) := by
  have hlen : sigma.length = k := by simpa using hold.1.length_eq
  have hfirst (n : ℕ) :
      (((earWord k sigma cut).take n).map (fullFirst k)).sum =
        ((sigma.take (if n ≤ cut then n else n - 1)).map (actualSource k 85)).sum := by
    rw [ear_prefix k sigma cut (by omega) (fullFirst k) n]
    simp [fullFirst]
  refine ⟨hnew.1, ?_, hnew.2.1, ?_⟩
  · have h := hfirst (k + 1)
    have he : (earWord k sigma cut).length = k + 1 := by
      simpa using hnew.1.length_eq
    rw [List.take_of_length_le (by omega : (earWord k sigma cut).length ≤ k + 1)] at h
    have hc : ¬ k + 1 ≤ cut := by omega
    simp only [if_neg hc, Nat.add_sub_cancel] at h
    rw [List.take_of_length_le (by omega : sigma.length ≤ k), hold.2.1] at h
    exact h
  · intro n
    rw [hfirst n]
    have hx := hold.2.2 (if n ≤ cut then n else n - 1)
    have hy := hnew.2.2 n
    rw [next_modulus_half] at hy
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩

theorem orders_of_jointWord (k : ℕ) (w : List (Fin (k + 1))) (hw : JointWord k w) :
    ∃ sigma : List (Fin k), ∃ cut : ℕ, cut ≤ k ∧
      w = earWord k sigma cut ∧ OriginalOrder k 85 sigma ∧
      OriginalOrder (k + 1) 170 (earWord k sigma cut) := by
  have hperm := oldPart_perm w hw.1
  have hnd := hw.1.nodup_iff.mpr (List.nodup_finRange _)
  obtain ⟨l, r, heq⟩ := List.mem_iff_append.mp
    (hw.1.mem_iff.mpr (List.mem_finRange (Fin.last k)))
  have hn : (l ++ Fin.last k :: r).Nodup := by rw [← heq]; exact hnd
  have hnl : Fin.last k ∉ l := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 _ hm _ (by simp) rfl
  have hnr : Fin.last k ∉ r := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  let sigma := oldPart w
  let cut := (oldPart l).length
  have hs : sigma = oldPart l ++ oldPart r := by
    dsimp [sigma]
    rw [heq]
    simp [oldPart, List.filterMap_append]
  have hlen : sigma.length = k := by simpa [sigma] using hperm.length_eq
  have hc : cut ≤ k := by rw [← hlen, hs]; simp [cut]
  have hear : w = earWord k sigma cut := by
    rw [earWord, hs]
    simp only [cut, List.take_left, List.drop_left]
    rw [oldPart_restore l hnl, oldPart_restore r hnr, heq]
    simp
  have hold : OriginalOrder k 85 sigma := by
    refine ⟨hperm, ?_, ?_⟩
    · rw [oldPart_sum]
      exact hw.2.1
    · intro n
      have hp : sigma.take n <+: oldPart w := List.take_prefix n sigma
      obtain ⟨p, hpw, hps⟩ := List.prefix_filterMap_iff.mp hp
      have hp : p = w.take p.length := List.prefix_iff_eq_take.mp hpw
      rw [hps]
      change ((oldPart p).map (actualSource k 85)).sum ∈ Set.Icc 0 (modulus k / 2)
      rw [oldPart_sum, hp]
      exact ⟨(hw.2.2.2 _).1, (hw.2.2.2 _).2.1⟩
  refine ⟨sigma, cut, hc, hear, hold, ?_⟩
  rw [← hear]
  refine ⟨hw.1, hw.2.2.1, ?_⟩
  intro n
  rw [next_modulus_half]
  exact ⟨(hw.2.2.2 n).2.2.1, (hw.2.2.2 n).2.2.2⟩

theorem insertion_only_eight_bit_lift (k : ℕ) (hk : 8 ≤ k)
    (sigma : List (Fin k)) (cut : ℕ) (hcut : cut ≤ k)
    (hold : OriginalOrder k 85 sigma)
    (hnew : OriginalOrder (k + 1) 170 (earWord k sigma cut)) :
    ∃ tau : List (Fin (k + 8)), ∃ targetCut : ℕ, targetCut ≤ k + 8 ∧
      OriginalOrder (k + 8) 85 tau ∧
      OriginalOrder (k + 9) 170 (earWord (k + 8) tau targetCut) ∧
      insertionDeletion (earWord (k + 8) tau targetCut) = earWord k sigma cut := by
  have h := physical_joint_lift k hk (earWord k sigma cut)
    (jointWord_of_orders k sigma cut hcut hold hnew)
  obtain ⟨tau, c, hc, he, hfirst, hsecond⟩ := orders_of_jointWord (k + 8) _ h.1
  exact ⟨tau, c, hc, hfirst, hsecond, by rw [← he]; exact h.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
