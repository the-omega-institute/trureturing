/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Boundary
   generality: I
   mirror-B: none(waiver:consumed-boundary-lemmas)
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Ascending physical orders on the one-negative and exactly periodic boundary. -/
import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Arithmetic
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
import D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private ear_prefix ear_perm
  from D5.S3.Combinatorics.Circle.RunFirstEarTransport
open private old_value
  from D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Source

private theorem nonnegative_strip {α : Type*} (f : α → ℤ) (B h : ℤ) (l : List α)
    (hf : ∀ x ∈ l, 0 ≤ f x) (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ B) :
    InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using And.intro hh hend
  | cons x xs ih =>
    have hx := hf x (by simp)
    have hxs : ∀ y ∈ xs, 0 ≤ f y := fun y hy => hf y (by simp [hy])
    have hs : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hxs y hy)
    simp only [List.map_cons, List.sum_cons] at hend
    exact ⟨hh, by omega, ih hxs (by omega) (by omega)⟩

private theorem natural_source_total (k t : ℕ) (hk : 0 < k) :
    ((List.range k).map (fun i => centered (modulus k) ((2 : ℤ)^i*t))).sum = 0 := by
  have h := (ZeroSumSubsets.source_cycle hk t).2.1
  rw [Fin.sum_univ_eq_sum_range] at h
  simpa [actualSource, List.sum_map_range] using h

private theorem range_labels (k : ℕ) (hk : 0 < k) :
    (List.range k).map (label k hk) = List.finRange k := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    apply Fin.ext
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, label]
    exact Nat.mod_eq_of_lt (by simpa using hi)

/-- The unit seed has one final negative; the fresh physical label follows every
old positive and precedes that negative. This is consumed by the p=1 branch. -/
theorem ascending_unit (k : ℕ) (hk : 2 ≤ k) :
    OriginalOrder k 1 (List.finRange k) ∧
    OriginalOrder (k+1) 2 (earWord k (List.finRange k) (k-1)) := by
  let B : ℤ := 2^(k-1)
  let f := fun i : ℕ => centered (modulus k) ((2 : ℤ)^i*1)
  let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*2)
  let P := List.range (k-1)
  have hB : 1 ≤ B := by dsimp [B]; positivity
  have hN : modulus k = 2*B-1 := by
    dsimp [modulus, B]
    rw [show k=(k-1)+1 by omega, pow_succ]
    ring
  have hN' : modulus (k+1)=4*B-1 := by rw [modulus, pow_succ, show (2:ℤ)^k=2*B by
    dsimp [B]; rw [show k=(k-1)+1 by omega, pow_succ]; ring]; ring
  have hfhalf : modulus k / 2 = B-1 := by rw [hN]; omega
  have hghalf : modulus (k+1) / 2 = 2*B-1 := by rw [hN']; omega
  have hf (i : ℕ) (hi : i<k-1) : f i=(2:ℤ)^i := by
    obtain ⟨hpos,hodd⟩ := TwoRunSource.modulus_positive_odd k (by omega)
    have hpow : (2:ℤ)^i < B := by
      dsimp [B]
      exact pow_lt_pow_right₀ (by norm_num) hi
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      (by rw [hfhalf]; constructor <;> have : (0:ℤ) ≤ 2^i := by positivity <;> omega)
    simp only [centered_mod, mul_one]
  have hg (i : ℕ) (hi : i<k-1) : g i=2*(2:ℤ)^i := by
    obtain ⟨hpos,hodd⟩ := TwoRunSource.modulus_positive_odd (k+1) (by omega)
    have hpow : (2:ℤ)^i < B := by
      dsimp [B]
      exact pow_lt_pow_right₀ (by norm_num) hi
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      (by rw [hghalf]; constructor <;> have : (0:ℤ) ≤ 2^i := by positivity <;> omega)
    rw [centered_mod]; congr 1; ring
  have hfresh : g k=1 := by
    dsimp [g]
    have he : (2:ℤ)^k*2=(2:ℤ)^(k+1)*1 := by rw [pow_succ]; ring
    rw [he, centered_full_period]
    obtain ⟨hpos,hodd⟩ := TwoRunSource.modulus_positive_odd (k+1) (by omega)
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      (by rw [hghalf]; omega)
    exact centered_mod _ _
  have hPsum : (P.map f).sum = B-1 := by
    simpa [P,B] using ladder_sum f 0 (k-1) 1 (by
      intro i hi; simpa using hf i hi)
  have hPsum' : (P.map g).sum=2*(B-1) := by
    have h := ladder_sum g 0 (k-1) 2 (by
      intro i hi; simpa [mul_comm] using hg i hi)
    simpa [P,B,mul_comm] using h
  have hword : P ++ [k-1] = List.range k := by
    simpa [P,show k-1+1=k by omega] using (List.range_succ (n:=k-1)).symm
  have htotal := natural_source_total k 1 (by omega)
  have htotal' := natural_source_total (k+1) 2 (by omega)
  change ((List.range k).map f).sum=0 at htotal
  change ((List.range (k+1)).map g).sum=0 at htotal'
  have hnegative : f (k-1)=-(B-1) := by
    rw [← hword,List.map_append,List.sum_append] at htotal
    simp only [List.map_singleton,List.sum_singleton,hPsum] at htotal
    omega
  have hnegative' : g (k-1)=-(2*B-1) := by
    rw [List.range_succ,← hword,List.map_append,List.sum_append] at htotal'
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      hPsum',hfresh] at htotal'
    omega
  have hPstrip : InStrip f (B-1) 0 P :=
    nonnegative_strip f _ _ P (by intro i hi; rw [hf i (List.mem_range.mp hi)]; positivity)
      (by omega) (by rw [hPsum]; omega)
  have holdstrip : InStrip f (modulus k/2) 0 (List.range k) := by
    rw [← hword,hfhalf]
    apply inStrip_append hPstrip
    simp only [List.map_append,List.sum_append,hPsum,InStrip,hnegative,List.map_singleton,
      List.sum_singleton]
    omega
  have hnewstrip : InStrip g (modulus (k+1)/2) 0 (P++[k,k-1]) := by
    rw [hghalf]
    have hpos : InStrip g (2*B-1) 0 P :=
      nonnegative_strip g _ _ P (by intro i hi; rw [hg i (List.mem_range.mp hi)]; positivity)
        (by omega) (by rw [hPsum']; omega)
    apply inStrip_append hpos
    simp only [hPsum',InStrip,hfresh,hnegative']
    omega
  have hnewperm : (P++[k,k-1]).Perm (List.range (k+1)) := by
    rw [List.range_succ,← hword]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add,List.cons_append,List.singleton_append,
      Multiset.coe_cons,Multiset.coe_nil]
    ac_rfl
  have hold := lift_order k 1 (by omega) (List.range k) (List.Perm.refl _)
    holdstrip (natural_source_total k 1 (by omega))
  have hnew := lift_order (k+1) 2 (by omega) (P++[k,k-1]) hnewperm
    hnewstrip (natural_source_total (k+1) 2 (by omega))
  have hearmark := marked_word k (k-1) (by omega) P [k-1]
    (by simp [P]) (by rw [hword])
  rw [hword,range_labels] at hearmark
  rw [← hearmark] at hnew
  simpa only [range_labels] using And.intro hold hnew

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
