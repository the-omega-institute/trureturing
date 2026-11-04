/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Lift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Lift
   mirror-E: none(waiver:internal-source-lift)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Natural lift compatibility for both actual centered sources. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip

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
-- Both actual-source tables are expanded over the four physical intervals.
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
    · simp only [ite_eq_left hp,ite_eq_left (show t+i+1<d+t by omega),pow_add]
      constructor <;> first | trivial | ring
    · simp only [ite_eq_right hp,ite_eq_right (show ¬t+i+1<d+t by omega),ht,pow_add]
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
  simp only [ite_eq_left (show i+1<d+t by omega)] at hu
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
      (fun i hi => by simpa only [Nat.zero_add] using
        (new_low_source a b c d t i ha hb hc hd hi).2)

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


open private Strong strong_positive_block strong_append strong_scaled strong_strips
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip

private theorem charge_nonneg (a b c d i : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) (hi : i<a+b+c+d) :
    0≤charge a b c d i := by
  obtain ⟨u,v,w,x,_⟩:=source_shadow_charge a b c d ha hb hc hd
  dsimp only at u v w x
  change 0≤2*old a b c d i-enlarged a b c d i
  unfold old enlarged modZ seedZ
  by_cases hu : i<d
  · rw [(u i hu).1]
    split_ifs <;> norm_num
  · by_cases hv : i<d+c
    · have he : i=d+(i-d) := by omega
      rw [he,(v (i-d) (by omega)).1]
      split_ifs <;> positivity
    · by_cases hw : i<d+c+b
      · have he : i=d+c+(i-(d+c)) := by omega
        rw [he,(w (i-(d+c)) (by omega)).1]
        split_ifs <;> positivity
      · have he : i=d+c+b+(i-(d+c+b)) := by omega
        rw [he,(x (i-(d+c+b)) (by omega)).1]
        split_ifs <;> positivity

private theorem new_low_charge_mass (a b c d t : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) :
    ((List.range t).map (charge a b c (d+t))).sum=0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hv
  exact (new_low_source a b c d t i ha hb hc hd (List.mem_range.mp hi)).1

/-- Every prefix of the newly prepended physical block is strong. -/
private theorem new_low_strong (a b c d t : ℕ) (B : ℤ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hA : 1≤seedZ a b c) (hAB : seedZ a b c≤B) :
    Strong (old a b c (d+t)) (charge a b c (d+t))
      ((2:ℤ)^t*B) 0 (seedZ a b c) (List.range t) := by
  apply strong_positive_block
  · intro i hi
    rw [(new_low_source a b c d t i ha hb hc hd (List.mem_range.mp hi)).2]
    positivity
  · intro i hi
    exact (new_low_source a b c d t i ha hb hc hd (List.mem_range.mp hi)).1
  · omega
  · exact hA
  · rw [new_low_mass a b c d t ha hb hc hd]
    have hm:=mul_le_mul_of_nonneg_left hAB (show 0≤(2:ℤ)^t by positivity)
    nlinarith only [hm]

/-- The literal natural lift preserves every actual strong prefix, including the endpoint. -/
private theorem natural_lift_strong (a b c d t : ℕ) (B : ℤ) (xs : List ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hA : 1≤seedZ a b c) (hAB : seedZ a b c≤B)
    (hx : ∀ i∈xs, i<a+b+c+d)
    (hs : Strong (old a b c d) (charge a b c d) B 0 (seedZ a b c) xs)
    (hq : (xs.map (charge a b c d)).sum=seedZ a b c) :
    Strong (old a b c (d+t)) (charge a b c (d+t)) ((2:ℤ)^t*B)
      0 (seedZ a b c) (List.range t++xs.map (t+·)) := by
  apply strong_append
  · exact new_low_strong a b c d t B ha hb hc hd hA hAB
  · rw [new_low_mass a b c d t ha hb hc hd,
      new_low_charge_mass a b c d t ha hb hc hd,zero_add,sub_zero]
    have he:=strong_scaled (old a b c d) (charge a b c d)
      (old a b c (d+t)) (charge a b c (d+t)) (t+·)
      ((2:ℤ)^t) B 0 (seedZ a b c) xs (by exact_mod_cast Nat.one_le_two_pow)
      hs (fun i hi => charge_nonneg a b c d i ha hb hc hd (hx i hi)) (by omega)
      (fun i hi => inherited_old_lift a b c d t i ha hb hc hd (hx i hi))
      (fun i hi => (inherited_source_lift a b c d t i ha hb hc hd (hx i hi)).1)
    simpa only [mul_zero,zero_add] using he

/-- The lift has exactly zero old total and preserves the complete actual charge. -/
private theorem natural_lift_totals (a b c d t : ℕ) (xs : List ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hx : ∀ i∈xs, i<a+b+c+d)
    (hf : (xs.map (old a b c d)).sum=0)
    (hq : (xs.map (charge a b c d)).sum=seedZ a b c) :
    ((List.range t++xs.map (t+·)).map (old a b c (d+t))).sum=0 ∧
      ((List.range t++xs.map (t+·)).map (charge a b c (d+t))).sum=seedZ a b c := by
  constructor
  · rw [lifted_prefix_height a b c d t xs ha hb hc hd hx,hf,hq]
    ring
  · rw [List.map_append,List.sum_append,new_low_charge_mass a b c d t ha hb hc hd,
      zero_add,List.map_map]
    convert hq using 2
    apply List.map_congr_left
    intro i hi
    exact (inherited_source_lift a b c d t i ha hb hc hd (hx i hi)).1


/-- The same naturally lifted physical word has both actual centered-source strips. -/
private theorem natural_lift_strips (a b c d t : ℕ) (B : ℤ) (xs : List ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hA : 1≤seedZ a b c) (hAB : seedZ a b c≤B)
    (hx : ∀ i∈xs, i<a+b+c+d)
    (hs : Strong (old a b c d) (charge a b c d) B 0 (seedZ a b c) xs)
    (hq : (xs.map (charge a b c d)).sum=seedZ a b c) :
    let ys:=List.range t++xs.map (t+·)
    InStrip (old a b c (d+t)) ((2:ℤ)^t*B-1) 0 ys ∧
      InStrip (enlarged a b c (d+t)) (2*((2:ℤ)^t*B)-1) (seedZ a b c) ys := by
  have hl:=natural_lift_strong a b c d t B xs ha hb hc hd hA hAB hx hs hq
  have hh:=strong_strips (old a b c (d+t)) (charge a b c (d+t))
    ((2:ℤ)^t*B) 0 (seedZ a b c) (List.range t++xs.map (t+·)) hl
  have he : (fun i => 2*old a b c (d+t) i-charge a b c (d+t) i)=
      enlarged a b c (d+t) := by
    funext i
    dsimp only [charge]
    ring
  simpa only [he,mul_zero,zero_add] using hh

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
