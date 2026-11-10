/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Endpoint
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full physical four-gap max-plus-two cone with a single old word and literal cut-zero ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.DescendingActual
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.AscendingActual
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.AdvancedX

/-! Every independent gap ordering is retained before the natural fourth-gap lift. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Endpoint
open SourceWidth PeriodicShortening RunFirstEarTransport Chambers
open private seedZ old charge natural_lift_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private actual_word_totals from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private label from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private valley_rising_inventory valley_rising_strong valley_falling_actual peak_actual actual_orders_of_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
open private descending_actual from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.DescendingActual
open private ascending_actual from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.AscendingActual
open private descending_edge_actual from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.AdvancedX

private theorem base_actual (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    let d0:=max (max a b) c+2
    (baseWord a b c).Perm (List.range (a+b+c+d0)) ∧
      Strong (old a b c d0) (charge a b c d0)
        (2^(d0-1)*2^a*2^b*2^c) 0 (seedZ a b c) (baseWord a b c) := by
  dsimp only
  by_cases hdesc : c≤b ∧ b≤a
  · have hd : max (max a b) c+2=a+2 := by
      rw [max_eq_left hdesc.2,max_eq_left (by omega)]
    rw [hd]
    by_cases hedge : (2:ℕ)^c=4 ∧ (2:ℕ)^a=2*2^b
    · have hc2 : c=2 := Nat.pow_right_injective (by decide)
        (show (2:ℕ)^c=2^2 by simpa using hedge.1)
      have ha1 : a=b+1 := Nat.pow_right_injective (by decide)
        (show (2:ℕ)^a=2^(b+1) by rw [pow_succ]; omega)
      subst a
      subst c
      simpa only [Nat.add_assoc] using descending_edge_actual b hb
    · exact descending_actual a b c hc hdesc.1 hdesc.2 hedge
  · by_cases hasc : a≤b ∧ b≤c
    · have hac : a<c := by omega
      have hd : max (max a b) c+2=c+2 := by
        rw [max_eq_right hasc.1,max_eq_right hasc.2]
      rw [hd]
      exact ascending_actual a b c ha hasc.1 hasc.2 hac
    · by_cases hval : b<a ∧ b<c
      · by_cases hac : a<c
        · have hd : max (max a b) c+2=c+2 := by
            rw [max_eq_left hval.1.le,max_eq_right hac.le]
          refine ⟨?_,valley_rising_strong a b c hb hval.1 hac⟩
          exact valley_rising_inventory a b c hb hval.1 hac
        · have hca : c≤a := by omega
          have hd : max (max a b) c+2=a+2 := by
            rw [max_eq_left hval.1.le,max_eq_left hca]
          rw [hd]
          exact valley_falling_actual a b c hb hval.2 hca
      · have hab : a<b := by omega
        have hcb : c<b := by omega
        have hd : max (max a b) c+2=b+2 := by
          rw [max_eq_right hab.le,max_eq_left hcb.le]
        rw [hd]
        exact peak_actual a b c ha hc hab hcb

set_option maxHeartbeats 1200000 in
/-- One actual physical order and its literal cut-zero ear work throughout the full max-plus-two cone. -/
theorem actualSource_max_plus_two_first_ear (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : max (max a b) c+2≤d) :
    ∃ sigma : List (Fin (a+b+c+d)),
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma 0) := by
  let d0:=max (max a b) c+2
  let t:=d-d0
  let B:ℤ:=2^(d0-1)*2^a*2^b*2^c
  let xs:=baseWord a b c
  have hd' : d0+t=d := by dsimp [d0,t] at *; omega
  obtain ⟨hinv,hstrong⟩:=base_actual a b c ha hb hc
  change xs.Perm (List.range (a+b+c+d0)) at hinv
  change Strong (old a b c d0) (charge a b c d0) B 0 (seedZ a b c) xs at hstrong
  have hx : ∀ i∈xs, i<a+b+c+d0 := fun i hi => List.mem_range.mp (hinv.mem_iff.mp hi)
  have hAB : seedZ a b c≤B := by
    cases he:xs with
    | nil => simp only [he,Strong,zero_add] at hstrong; exact hstrong.2.2.2
    | cons i ys => simp only [he,Strong,zero_add] at hstrong; exact hstrong.2.2.2.1
  have hA : 1≤seedZ a b c := by
    have hp : 0<seedZ a b c := by dsimp [seedZ]; positivity
    omega
  have htot:=actual_word_totals a b c d0 xs ha hb hc (by dsimp [d0];omega) hinv
  have hl:=natural_lift_strong a b c d0 t B xs ha hb hc
    (by dsimp [d0];omega) hA hAB hx hstrong htot.2
  have hpow : (2:ℤ)^t*B=2^(d-1)*2^a*2^b*2^c := by
    dsimp [B]
    rw [show d-1=t+(d0-1) by dsimp [t,d0] at *;omega,pow_add]
    ring
  rw [hd',hpow] at hl
  have hword : physicalWord a b c d=List.range t++xs.map (t+·) := rfl
  have hlInv : (List.range t++xs.map (t+·)).Perm (List.range (a+b+c+d)) := by
    have hmap : (List.range (a+b+c+d0)).map (t+·)=List.range' t (a+b+c+d0) := by
      rw [List.range_eq_range']
      simpa only [Nat.add_zero] using (List.map_add_range' (a:=t) 0 (a+b+c+d0) 1)
    have hi:=(hinv.map (t+·)).append_left (List.range t)
    have hr := List.range'_append_1 (s:=0) (m:=t) (n:=a+b+c+d0)
    simp only [Nat.zero_add] at hr
    rw [hmap,List.range_eq_range',hr] at hi
    simpa only [Nat.zero_add,←List.range_eq_range',show t+(a+b+c+d0)=a+b+c+d by omega] using hi
  refine ⟨(physicalWord a b c d).map (label (a+b+c+d) (by omega)),?_⟩
  apply actual_orders_of_strong a b c d (physicalWord a b c d) ha hb hc (by omega)
  · simpa only [hword] using hlInv
  · simpa only [hword] using hl

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Endpoint
