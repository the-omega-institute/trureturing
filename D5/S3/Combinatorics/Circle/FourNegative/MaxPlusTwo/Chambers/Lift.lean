/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Lift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Lift
   mirror-E: none(waiver:internal-source-lift)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Natural lift compatibility for both actual centered sources. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source

/-! Increasing the fourth gap leaves charge unchanged and scales every inherited shadow. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport
open private source_shadow_charge
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source

private def seedZ (a b c : ℕ) : ℤ := 2^a*2^b*2^c+(1+2^a+2^a*2^b)
private def modZ (a b c d : ℕ) : ℤ := 2^a*2^b*2^c*2^d-1
private def old (a b c d i : ℕ) : ℤ := centered (modZ a b c d) (2^i*seedZ a b c)
private def enlarged (a b c d i : ℕ) : ℤ :=
  centered (2*modZ a b c d+1) (2^i*(2*seedZ a b c))
private def charge (a b c d i : ℕ) : ℤ := 2*old a b c d i-enlarged a b c d i
private def shadow (a b c d i : ℕ) : ℤ := enlarged a b c d i-old a b c d i

set_option maxHeartbeats 1000000 in
private theorem inherited_source_lift (a b c d t i : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) (hi : i<a+b+c+d) :
    charge a b c (d+t) (t+i)=charge a b c d i ∧
    shadow a b c (d+t) (t+i)=(2:ℤ)^t*shadow a b c d i := by
  obtain ⟨u0,v0,w0,x0,_⟩ := source_shadow_charge a b c d ha hb hc hd
  obtain ⟨u1,v1,w1,x1,_⟩ := source_shadow_charge a b c (d+t) ha hb hc (by omega)
  dsimp only at u0 v0 w0 x0 u1 v1 w1 x1
  change (2*old a b c (d+t) (t+i)-enlarged a b c (d+t) (t+i)=
      2*old a b c d i-enlarged a b c d i) ∧
    (enlarged a b c (d+t) (t+i)-old a b c (d+t) (t+i)=
      2^t*(enlarged a b c d i-old a b c d i))
  unfold old enlarged modZ seedZ
  have ht : d+t-1=d-1+t := by omega
  by_cases hu : i<d
  · have hs0 := u0 i hu
    have hs1 := u1 (t+i) (by omega)
    rw [hs0.1,hs1.1,hs0.2,hs1.2]
    by_cases hp : i+1<d
    · simp only [if_pos hp,if_pos (show t+i+1<d+t by omega),pow_add]
      constructor <;> first | trivial | ring
    · simp only [if_neg hp,if_neg (show ¬t+i+1<d+t by omega),ht,pow_add]
      constructor <;> first | trivial | ring
  · by_cases hv : i<d+c
    · let j:=i-d
      have hi0 : i=d+j := by dsimp [j]; omega
      have hi1 : t+(d+j)=d+t+j := by dsimp [j]; omega
      rw [hi0,hi1]
      have hs0 := v0 j (by dsimp [j]; omega)
      have hs1 := v1 j (by dsimp [j]; omega)
      rw [hs0.1,hs1.1,hs0.2,hs1.2]
      constructor
      · rfl
      · split_ifs <;> rw [ht,pow_add] <;> ring
    · by_cases hw : i<d+c+b
      · let j:=i-(d+c)
        have hi0 : i=d+c+j := by dsimp [j]; omega
        have hi1 : t+(d+c+j)=d+t+c+j := by dsimp [j]; omega
        rw [hi0,hi1]
        have hs0 := w0 j (by dsimp [j]; omega)
        have hs1 := w1 j (by dsimp [j]; omega)
        rw [hs0.1,hs1.1,hs0.2,hs1.2]
        constructor
        · rfl
        · split_ifs <;> rw [ht,pow_add] <;> ring
      · let j:=i-(d+c+b)
        have hi0 : i=d+c+b+j := by dsimp [j]; omega
        have hi1 : t+(d+c+b+j)=d+t+c+b+j := by dsimp [j]; omega
        rw [hi0,hi1]
        have hs0 := x0 j (by dsimp [j]; omega)
        have hs1 := x1 j (by dsimp [j]; omega)
        rw [hs0.1,hs1.1,hs0.2,hs1.2]
        constructor
        · rfl
        · split_ifs <;> rw [ht,pow_add] <;> ring

private theorem inherited_old_lift (a b c d t i : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) (hi : i<a+b+c+d) :
    old a b c (d+t) (t+i)=
      (2:ℤ)^t*old a b c d i-((2:ℤ)^t-1)*charge a b c d i := by
  obtain ⟨hq,hz⟩ := inherited_source_lift a b c d t i ha hb hc hd hi
  dsimp [charge,shadow] at hq hz ⊢
  nlinarith only [hq,hz]

private theorem new_low_source (a b c d t i : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) (hi : i<t) :
    charge a b c (d+t) i=0 ∧ old a b c (d+t) i=2^i*seedZ a b c := by
  have hu := (source_shadow_charge a b c (d+t) ha hb hc (by omega)).1 i (by omega)
  dsimp only at hu
  rw [ite_eq_left (show i+1<d+t by omega)] at hu
  change 2*old a b c (d+t) i-enlarged a b c (d+t) i=0 ∧
    enlarged a b c (d+t) i-old a b c (d+t) i=2^i*seedZ a b c at hu
  exact ⟨hu.1,by linarith only [hu.1,hu.2]⟩

open private ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem new_low_mass (a b c d t : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) :
    ((List.range t).map (old a b c (d+t))).sum=(2^t-1)*seedZ a b c := by
  simpa only [Nat.zero_add,←List.range_eq_range'] using
    ladder_sum (old a b c (d+t)) 0 t (seedZ a b c)
      (fun i hi => (new_low_source a b c d t i ha hb hc hd hi).2)

/-- Summing inherited source compatibility recovers the stated remaining-charge lift. -/
private theorem lifted_prefix_height (a b c d t : ℕ) (xs : List ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hx : ∀ i∈xs, i<a+b+c+d) :
    (((List.range t++xs.map (t+·)).map (old a b c (d+t))).sum)=
      (2:ℤ)^t*(xs.map (old a b c d)).sum+
        ((2:ℤ)^t-1)*(seedZ a b c-(xs.map (charge a b c d)).sum) := by
  have hh : ((xs.map (t+·)).map (old a b c (d+t))).sum=
      (2:ℤ)^t*(xs.map (old a b c d)).sum-
        ((2:ℤ)^t-1)*(xs.map (charge a b c d)).sum := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [inherited_old_lift a b c d t i ha hb hc hd (hx i (by simp)),
        ih (fun j hj => hx j (by simp [hj]))]
      ring
  rw [List.map_append,List.sum_append,new_low_mass a b c d t ha hb hc hd,hh]
  ring

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
