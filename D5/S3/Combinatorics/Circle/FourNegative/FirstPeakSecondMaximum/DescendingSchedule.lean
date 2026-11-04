/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/DescendingSchedule
   generality: I
   mirror-B: none(waiver:private-consumed-construction)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Descending schedule for the physical first-peak joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingSource
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

/-! DescendingSchedule for the paired physical source construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private D A B L M E delta oldSeam newSeam oldNext newNext Gates
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingArithmetic
open private allocate
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingCharts
open private bank terminal word bank_inventory bank_good bank_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingSource
open private size sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue source_signs negatives chain_values new_base_bounds source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private inserted_perm from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option maxHeartbeats 2600000 in
private theorem descending_joint_construction (a b c d : ℕ)
    (hc : 2 ≤ c) (hcb : c<b) (hbd : b ≤ d) (hda : d<a) :
    ∃ sigma : List (Fin (a + b + c + d)),
      OriginalOrder (a + b + c + d) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧ 
      OriginalOrder (a + b + c + d + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + d) sigma 0) := by
  classical
  let k := a + b + c + d
  let s := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
  let n : ℤ := 2 ^ (a-d)
  let y : ℤ := 2 ^ b
  let z : ℤ := 2 ^ c
  let t : ℤ := 2 ^ d
  let AA := A n y z t
  let BB := B n y t
  let LL := L n z t
  let MM := M y z t
  let DD := D y z
  let Bn := 2 * BB-1
  let Ln := 2 * LL-z-1
  let Mn := 2 * MM-DD
  let N := sourceMod a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  have hx : (2:ℤ) ^ a=n * t := by
    dsimp [n,t]
    rw [←pow_add]
    congr 1
    omega
  have hbase : base a b c d=![AA,BB,LL,MM] := by
    funext i
    fin_cases i <;> dsimp [base,AA,BB,LL,MM,A,B,L,M,DD,D,y,z,t]
    all_goals (try rw [hx]) <;> ring
  have hnewbase : newBase a b c d=![2 * AA,Bn,Ln,Mn] := by
    funext i
    fin_cases i <;> dsimp [newBase,charge,Bn,Ln,Mn,DD,D,y,z]
    all_goals rw [hbase] <;> dsimp <;> ring
  have hseed : (s:ℤ)=AA := by
    dsimp [s,AA,A,D,y,z]
    push_cast
    simp only [pow_add]
    rw [hx]
    ring
  have hmod : modulus k=N := by dsimp [modulus,k,N,sourceMod]; ring
  have hmodn : modulus (k + 1)=2 * N + 1 := by dsimp [modulus,k,N,sourceMod]; ring
  obtain ⟨corner,rZ,vZ,hrZ,hrnZ,hvZ,hvcZ,bounds,cornerData⟩ := allocate a b c d hc hcb hbd hda
  change 1 ≤ rZ at hrZ
  change rZ ≤ n at hrnZ
  change 2 * vZ<t at hvcZ
  change Gates corner n y z t rZ vZ at bounds
  have half (j : ℕ) (hj : 1 ≤ j) : (2:ℤ) ^ j=2 * 2 ^ (j-1) := by
    conv_lhs => rw [show j=(j-1) + 1 by omega,pow_succ]
    ring
  -- All signed allocation and binary capacity obligations precede toNat.
  have hvInt : vZ<(2:ℤ) ^ (d-1) := by
    have hh := half d (by omega)
    dsimp [t] at hvcZ
    nlinarith only [hvcZ,hh]
  let r := rZ.toNat
  let v := vZ.toNat
  have er : (r:ℤ)=rZ := Int.toNat_of_nonneg (by omega)
  have ev : (v:ℤ)=vZ := Int.toNat_of_nonneg hvZ
  have hr : 1 ≤ r := by exact_mod_cast (show (1:ℤ) ≤ r by omega)
  have hrn : r ≤ 2 ^ (a-d) := by
    have h : (r:ℤ) ≤ (2:ℤ) ^ (a-d) := by simpa [n,er] using hrnZ
    exact_mod_cast h
  have hvCap : v<2 ^ (d-1) := by
    have h : (v:ℤ)<(2:ℤ) ^ (d-1) := by simpa [ev] using hvInt
    exact_mod_cast h
  have cp : ((2 ^ (a-d)-r:ℕ):ℤ)=n-rZ := by
    rw [Nat.cast_sub hrn,er]
    norm_cast
  have cq : ((r-1:ℕ):ℤ)=rZ-1 := by
    rw [Nat.cast_sub hr,er]
    norm_num
  have hbit : corner=true → ∃ e, e<d-1 ∧ v=2 ^ e := by
    intro hcorner
    obtain ⟨hdb,_,_,hv⟩ := cornerData hcorner
    refine ⟨b-c-1,by omega,?_⟩
    have h : (v:ℤ)=(2:ℤ) ^ (b-c-1) := ev.trans hv
    exact_mod_cast h
  let P := bank corner a b c d r v
  let T := terminal corner a b c d
  let l := word corner a b c d r v
  have hp : l.Perm (List.range k) :=
    bank_inventory corner a b c d r v (by omega) (by omega) hc (by omega) hda hr hrn
  have pos (j : Fin 4) (i : ℕ) (hi : i∈P j) : 0 ≤ f i ∧ 0 ≤ g i := by
    have hg := bank_good corner a b c d r v (by omega) (by omega) hc (by omega) hda j i hi
    have hs := source_signs a b c d (by omega) (by omega) hc (by omega) i hg.1
    rw [if_neg hg.2] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have mass := bank_masses corner a b c d r v (by omega) (by omega) hc (by omega) hda hr hrn hvCap hbit
  have mo := mass false
  have mg := mass true
  dsimp only [Bool.false_eq_true,ite_false,ite_true] at mo mg
  rw [hbase] at mo
  rw [hnewbase] at mg
  simp only [chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,er,ev,cp,cq,
    Nat.cast_pow,Nat.cast_ofNat] at mo mg
  let C := fun j : ℕ => (((2 ^ (j-1)-1:ℕ):ℤ))
  change ((P 0).map f).sum=C a * MM-n * MM + MM ∧ 
    ((P 1).map f).sum=(if corner then C d * AA-vZ * AA + (n-rZ) * MM else C c * BB + (n-rZ) * MM + vZ * AA) ∧ 
    ((P 2).map f).sum=(if corner then C c * BB + vZ * AA else C d * AA-vZ * AA) ∧ 
    ((P 3).map f).sum=C b * LL + (rZ-1) * MM at mo
  change ((P 0).map g).sum=C a * Mn-n * Mn + Mn ∧ 
    ((P 1).map g).sum=(if corner then C d * (2 * AA)-vZ * (2 * AA) + (n-rZ) * Mn else C c * Bn + (n-rZ) * Mn + vZ * (2 * AA)) ∧ 
    ((P 2).map g).sum=(if corner then C c * Bn + vZ * (2 * AA) else C d * (2 * AA)-vZ * (2 * AA)) ∧ 
    ((P 3).map g).sum=C b * Ln + (rZ-1) * Mn at mg
  have nat0 := native_masses a b c d (by omega) (by omega) hc (by omega) 0
  have nat1 := native_masses a b c d (by omega) (by omega) hc (by omega) 1
  have nat2 := native_masses a b c d (by omega) (by omega) hc (by omega) 2
  have nat3 := native_masses a b c d (by omega) (by omega) hc (by omega) 3
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbase,hnewbase,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,Nat.zero_add,
    show d + (c-1)=d + c-1 by omega,
    show d + c + (b-1)=d + c + b-1 by omega,
    show d + c + b + (a-1)=k-1 by dsimp [k]; omega] at nat0 nat1 nat2 nat3
  change C d * AA + f (d-1)=BB-AA ∧ C d * (2 * AA) + g (d-1)=Bn-2 * AA ∧ 
    2 * f (d-1)=BB-N ∧ 2 * g (d-1)=Bn-(2 * N + 1) at nat0
  change C c * BB + f (d + c-1)=LL-BB ∧ C c * Bn + g (d + c-1)=Ln-Bn ∧ 
    2 * f (d + c-1)=LL-N ∧ 2 * g (d + c-1)=Ln-(2 * N + 1) at nat1
  change C b * LL + f (d + c + b-1)=MM-LL ∧ C b * Ln + g (d + c + b-1)=Mn-Ln ∧ 
    2 * f (d + c + b-1)=MM-N ∧ 2 * g (d + c + b-1)=Mn-(2 * N + 1) at nat2
  change C a * MM + f (k-1)=AA-MM ∧ C a * Mn + g (k-1)=AA-Mn ∧ 
    2 * f (k-1)=AA-N ∧ 2 * g (k-1)=AA-(2 * N + 1) at nat3
  have os0 : ((P 0).map f).sum + f (T 0)=oldSeam corner n y z t rZ vZ 0 := by
    cases corner <;> dsimp [T,terminal,oldSeam] at * 
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals nlinarith only [mo.1,nat3.1]
  have os1 : ((P 0).map f).sum + f (T 0) + ((P 1).map f).sum + f (T 1)=oldSeam corner n y z t rZ vZ 1 := by
    cases corner <;> dsimp [T,terminal,oldSeam] at * 
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals nlinarith only [mo.1,nat3.1,mo.2.1,nat0.1,nat1.1]
  have os2 : ((P 0).map f).sum + f (T 0) + ((P 1).map f).sum + f (T 1) + ((P 2).map f).sum + f (T 2)=oldSeam corner n y z t rZ vZ 2 := by
    cases corner <;> dsimp [T,terminal,oldSeam] at * 
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals nlinarith only [mo.1,nat3.1,mo.2.1,nat0.1,nat1.1,mo.2.2.1]
  have ns0 : AA + ((P 0).map g).sum + g (T 0)=newSeam corner n y z t rZ vZ 0 := by
    cases corner <;> dsimp [T,terminal,newSeam] at * 
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals nlinarith only [mg.1,nat3.2.1]
  have ns1 : AA + ((P 0).map g).sum + g (T 0) + ((P 1).map g).sum + g (T 1)=newSeam corner n y z t rZ vZ 1 := by
    cases corner <;> dsimp [T,terminal,newSeam] at * 
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals nlinarith only [mg.1,nat3.2.1,mg.2.1,nat0.2.1,nat1.2.1]
  have ns2 : AA + ((P 0).map g).sum + g (T 0) + ((P 1).map g).sum + g (T 1) + ((P 2).map g).sum + g (T 2)=newSeam corner n y z t rZ vZ 2 := by
    cases corner <;> dsimp [T,terminal,newSeam] at * 
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals nlinarith only [mg.1,nat3.2.1,mg.2.1,nat0.2.1,nat1.2.1,mg.2.2.1]
  have term0 : 2 * f (T 0)=oldNext corner n y z t 0-N ∧ 
      2 * g (T 0)=newNext corner n y z t 0-(2 * N + 1) := by
    cases corner <;> dsimp [T,terminal,oldNext,newNext]
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals constructor <;> nlinarith only [nat0.2.2.1,nat0.2.2.2,nat1.2.2.1,nat1.2.2.2,nat3.2.2.1,nat3.2.2.2]
  have term1 : 2 * f (T 1)=oldNext corner n y z t 1-N ∧ 
      2 * g (T 1)=newNext corner n y z t 1-(2 * N + 1) := by
    cases corner <;> dsimp [T,terminal,oldNext,newNext]
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals constructor <;> nlinarith only [nat0.2.2.1,nat0.2.2.2,nat1.2.2.1,nat1.2.2.2,nat3.2.2.1,nat3.2.2.2]
  have term2 : 2 * f (T 2)=oldNext corner n y z t 2-N ∧ 
      2 * g (T 2)=newNext corner n y z t 2-(2 * N + 1) := by
    cases corner <;> dsimp [T,terminal,oldNext,newNext]
    all_goals dsimp [AA,BB,LL,MM,Bn,Ln,Mn] at * 
    all_goals constructor <;> nlinarith only [nat0.2.2.1,nat0.2.2.2,nat1.2.2.1,nat1.2.2.2,nat3.2.2.1,nat3.2.2.2]
  have totals := source_totals a b c d (by omega) (by omega) hc (by omega)
  have hfzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hear : g k=AA := by simpa [size,hbase] using totals.2.2
  have hgzero : AA + (l.map g).sum=0 := by
    have h := (hp.map g).sum_eq.trans totals.2.1
    rw [hbase] at h
    change (l.map g).sum = -AA at h
    omega
  have hNodd : N%2=1 := by
    have hh := half d (by omega)
    have he : N=2 * ((2:ℤ) ^ a * 2 ^ b * 2 ^ c * 2 ^ (d-1)-1) + 1 := by
      dsimp [N,sourceMod]
      rw [hh]
      ring
    omega
  have hN0 : 0 ≤ N := by
    have hh := (chain_values a b c d (by omega) (by omega) hc (by omega)).1 0
    rw [hbase] at hh
    change 1 ≤ AA ∧ AA<N at hh
    omega
  have lastold : 0 ≤ -f (T 3) ∧ -f (T 3) ≤ N/2 := by
    have finalGate := (bounds 3).1
    have hMpositive : 1 ≤ MM := by
      cases corner <;> dsimp [oldSeam,oldNext] at finalGate
      all_goals (dsimp [MM]; omega)
    have hh := (chain_values a b c d (by omega) (by omega) hc (by omega)).1 3
    rw [hbase] at hh
    change 1 ≤ MM ∧ MM<N at hh
    have ht : T 3=d + c + b-1 := by cases corner <;> rfl
    rw [ht]
    have htval := nat2.2.2.1
    omega
  have lastnew : 0 ≤ -g (T 3) ∧ -g (T 3) ≤ N := by
    have finalGate := (bounds 3).2
    have hMpositive : 1 ≤ Mn := by
      cases corner <;> dsimp [newSeam,newNext] at finalGate
      all_goals (dsimp [Mn,MM,DD]; omega)
    have hh := new_base_bounds a b c d (by omega) (by omega) hc (by omega) 3
    rw [hnewbase] at hh
    change 1 ≤ Mn ∧ Mn<2 * N + 1 at hh
    have ht : T 3=d + c + b-1 := by cases corner <;> rfl
    rw [ht]
    have htval := nat2.2.2.2
    omega
  have oldstrip : InStrip f (N/2) 0 l := by
    change InStrip f (N/2) 0 (P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3])
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · have gate := (bounds 0).1
      constructor
      · nlinarith only [os0,term0.1,gate.2,hNodd,Int.emod_add_mul_ediv N 2]
      · nlinarith only [os0,gate.1]
    · have gate := (bounds 1).1
      constructor
      · nlinarith only [os1,term1.1,gate.2,hNodd,Int.emod_add_mul_ediv N 2]
      · nlinarith only [os1,gate.1]
    · have gate := (bounds 2).1
      constructor
      · nlinarith only [os2,term2.1,gate.2,hNodd,Int.emod_add_mul_ediv N 2]
      · nlinarith only [os2,gate.1]
    · exact lastold
    · simpa [l,word,P,T] using hfzero
  have newtail : InStrip g N AA l := by
    change InStrip g N AA (P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3])
    have hAA : 0 ≤ AA := by
      have hh := (chain_values a b c d (by omega) (by omega) hc (by omega)).1 0
      rw [hbase] at hh
      change 1 ≤ AA ∧ AA<N at hh
      omega
    apply four_strip g (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) N AA
      (fun i hi => (pos 0 i hi).2) (fun i hi => (pos 1 i hi).2)
      (fun i hi => (pos 2 i hi).2) (fun i hi => (pos 3 i hi).2) hAA
    · have gate := (bounds 0).2
      constructor
      · nlinarith only [ns0,term0.2,gate.2]
      · nlinarith only [ns0,gate.1]
    · have gate := (bounds 1).2
      constructor
      · nlinarith only [ns1,term1.2,gate.2]
      · nlinarith only [ns1,gate.1]
    · have gate := (bounds 2).2
      constructor
      · nlinarith only [ns2,term2.2,gate.2]
      · nlinarith only [ns2,gate.1]
    · exact lastnew
    · simpa [l,word,P,T] using hgzero
  have newstrip : InStrip g N 0 (k::l) := by
    refine ⟨le_rfl,hN0,?_⟩
    simpa only [hear,zero_add] using newtail
  have hpnew : (k::l).Perm (List.range (k + 1)) := by
    simpa only [List.nil_append] using inserted_perm k [] l (by simpa only [List.nil_append] using hp)
  have fform : f=fun i => centered N ((2:ℤ) ^ i * AA) := by
    funext i
    change centered N ((2:ℤ) ^ i * base a b c d 0)=_
    rw [hbase]
    rfl
  have gform : g=fun i => centered (2 * N + 1) ((2:ℤ) ^ i * (2 * AA)) := by
    funext i
    change centered (2 * N + 1) ((2:ℤ) ^ i * (2 * base a b c d 0))=_
    rw [hbase]
    rfl
  refine ⟨l.map (label k (by dsimp [k]; omega)),?_,?_⟩
  · apply lift_order k s (by dsimp [k]; omega) l hp
    · simpa only [fform,hmod,hseed] using oldstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k s (by dsimp [k]; omega)
  · have hm := marked_word k 0 (by dsimp [k]; omega) [] l rfl (by simpa using hp)
    simp only [List.nil_append] at hm
    rw [hm]
    apply lift_order (k + 1) (2 * s) (by omega) (k::l) hpnew
    · have hs : ((2 * s:ℕ):ℤ)=2 * AA := by push_cast; rw [hseed]
      simpa only [gform,hmodn,hs,show (2 * N + 1)/2=N by omega] using newstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * s) (by dsimp [k]; omega)

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
