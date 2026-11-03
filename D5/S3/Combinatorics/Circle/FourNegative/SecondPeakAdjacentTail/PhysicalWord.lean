/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PhysicalWord
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PhysicalWord
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Paired physical strip construction with one literal insertion. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PhysicalBanks
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
open SourceWidth
open private bank terminal word bank_good bank_inventory bank_masses
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PhysicalBanks
open private size base newBase charge sourceMod chainLength chainStart nextBase nextNewBase
  oldValue newValue chain_values source_totals source_signs new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

/-- This internal lemma consumes actual windows; it does not assert their universal
existence. Fresh is inserted AFTER nU, and belongs to the second positive block. -/
private theorem physical_strips (a b c d v m : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hv : v≤2^(c-1)-1) (hm : m≤2^(b-1)-1)
    (ho : let AA := base a b c d 0; let BB := base a b c d 1
      let LL := base a b c d 2; let KK := base a b c d 3
      ∀ r : Fin 3,
      0≤2*(![BB-AA,((v:ℤ)+1)*BB-KK+(m:ℤ)*LL,((v:ℤ)+1)*BB-LL] r) ∧
      2*(![BB-AA,((v:ℤ)+1)*BB-KK+(m:ℤ)*LL,((v:ℤ)+1)*BB-LL] r)≤
        ![BB,AA,KK] r-1)
    (hn : let AA := base a b c d 0; let UU := newBase a b c d 1
      let VV := newBase a b c d 2; let WW := newBase a b c d 3
      ∀ r : Fin 3,
      0≤2*(![UU-2*AA,((v:ℤ)+1)*UU-WW+(m:ℤ)*VV,((v:ℤ)+1)*UU-VV] r) ∧
      2*(![UU-2*AA,((v:ℤ)+1)*UU-WW+(m:ℤ)*VV,((v:ℤ)+1)*UU-VV] r)≤
        ![UU,AA,WW] r-1) :
    let k := a+b+c+d
    let w := word a b c d v m
    w.Perm (List.range k) ∧ d≤k ∧
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 w ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0 (insertAt k w d) := by
  let k := a+b+c+d
  let P := bank a b c d v m
  let t := terminal a b c d
  let w := word a b c d v m
  let f := oldValue a b c d
  let g := newValue a b c d
  let N := sourceMod a b c d
  let AA := base a b c d 0
  let BB := base a b c d 1
  let LL := base a b c d 2
  let KK := base a b c d 3
  let UU := newBase a b c d 1
  let VV := newBase a b c d 2
  let WW := newBase a b c d 3
  let C := fun r : Fin 4 => (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))
  have hnew0 : newBase a b c d 0=2*AA := by simp [newBase,charge,AA]
  have hp := bank_inventory a b c d v m ha hb hc hd
  have pos (r : Fin 4) (i : ℕ) (hi : i∈P r) : 0≤f i ∧ 0≤g i := by
    have good := bank_good a b c d v m ha hb hc hd r i hi
    have hh := source_signs a b c d ha hb hc hd i good.1
    rw [if_neg good.2] at hh
    exact ⟨hh.1.le,hh.2.le⟩
  have masses := bank_masses a b c d v m ha hb hc hd hv hm
  have mo := masses false
  have mg := masses true
  dsimp only [Bool.false_eq_true,ite_false,ite_true] at mo mg
  change ((P 0).map f).sum=C 0*AA ∧
    ((P 1).map f).sum=C 3*KK+(m:ℤ)*LL+(v:ℤ)*BB ∧
    ((P 2).map f).sum=C 2*LL-(m:ℤ)*LL ∧
    ((P 3).map f).sum=C 1*BB-(v:ℤ)*BB at mo
  rw [hnew0] at mg
  change ((P 0).map g).sum=C 0*(2*AA) ∧
    ((P 1).map g).sum=C 3*WW+(m:ℤ)*VV+(v:ℤ)*UU ∧
    ((P 2).map g).sum=C 2*VV-(m:ℤ)*VV ∧
    ((P 3).map g).sum=C 1*UU-(v:ℤ)*UU at mg
  have nu : C 0*AA+f (t 0)=BB-AA ∧ C 0*(2*AA)+g (t 0)=UU-2*AA ∧
      2*f (t 0)=BB-N ∧ 2*g (t 0)=UU-(2*N+1) := by
    simpa [C,t,terminal,chainLength,chainStart,nextBase,nextNewBase,hnew0,AA,BB,UU,N,f,g,
      show 0+(d-1)=d-1 by omega] using native_masses a b c d ha hb hc hd 0
  have nv : C 1*BB+f (t 3)=LL-BB ∧ C 1*UU+g (t 3)=VV-UU ∧
      2*f (t 3)=LL-N ∧ 2*g (t 3)=VV-(2*N+1) := by
    simpa [C,t,terminal,chainLength,chainStart,nextBase,nextNewBase,BB,LL,UU,VV,N,f,g,
      show d+(c-1)=d+c-1 by omega] using native_masses a b c d ha hb hc hd 1
  have nw : C 2*LL+f (t 2)=KK-LL ∧ C 2*VV+g (t 2)=WW-VV ∧
      2*f (t 2)=KK-N ∧ 2*g (t 2)=WW-(2*N+1) := by
    simpa [C,t,terminal,chainLength,chainStart,nextBase,nextNewBase,LL,KK,VV,WW,N,f,g,
      show d+c+(b-1)=d+c+b-1 by omega] using native_masses a b c d ha hb hc hd 2
  have nx : C 3*KK+f (t 1)=AA-KK ∧ C 3*WW+g (t 1)=AA-WW ∧
      2*f (t 1)=AA-N ∧ 2*g (t 1)=AA-(2*N+1) := by
    simpa [C,t,terminal,chainLength,chainStart,nextBase,nextNewBase,AA,KK,WW,N,f,g,
      show d+c+b+(a-1)=a+b+c+d-1 by omega] using native_masses a b c d ha hb hc hd 3
  have eo0 : ((P 0).map f).sum+f (t 0)=BB-AA := by linarith [mo.1,nu.1]
  have eo1 : ((P 0).map f).sum+f (t 0)+((P 1).map f).sum+f (t 1)=
      ((v:ℤ)+1)*BB-KK+(m:ℤ)*LL := by nlinarith only [eo0,mo.2.1,nx.1]
  have eo2 : ((P 0).map f).sum+f (t 0)+((P 1).map f).sum+f (t 1)+
      ((P 2).map f).sum+f (t 2)=((v:ℤ)+1)*BB-LL := by nlinarith only [eo1,mo.2.2.1,nw.1]
  have en0 : ((P 0).map g).sum+g (t 0)=UU-2*AA := by linarith [mg.1,nu.2.1]
  have en1 : ((P 0).map g).sum+g (t 0)+AA+((P 1).map g).sum+g (t 1)=
      ((v:ℤ)+1)*UU-WW+(m:ℤ)*VV := by nlinarith only [en0,mg.2.1,nx.2.1]
  have en2 : ((P 0).map g).sum+g (t 0)+AA+((P 1).map g).sum+g (t 1)+
      ((P 2).map g).sum+g (t 2)=((v:ℤ)+1)*UU-VV := by nlinarith only [en1,mg.2.2.1,nw.2.1]
  have totals := source_totals a b c d ha hb hc hd
  have hzold : (w.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hznew : AA+(w.map g).sum=0 := by
    have hh := (hp.map g).sum_eq.trans totals.2.1
    change (w.map g).sum=-AA at hh
    omega
  have hfresh : g k=AA := totals.2.2
  have hBB := (chain_values a b c d ha hb hc hd).1 1
  have hLL := (chain_values a b c d ha hb hc hd).1 2
  have hVV := new_base_bounds a b c d ha hb hc hd 2
  change 1≤LL ∧ LL<N at hLL
  change 1≤BB ∧ BB<N at hBB
  change 1≤VV ∧ VV<2*N+1 at hVV
  have hN : 0≤N := by omega
  have oldstrip : InStrip f (N/2) 0 w := by
    change InStrip f (N/2) 0 (P 0 ++ t 0 :: P 1 ++ t 1 :: P 2 ++ t 2 :: P 3 ++ [t 3])
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (t 0) (t 1) (t 2) (t 3) (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · have hh := ho 0; change 0≤2*(BB-AA) ∧ 2*(BB-AA)≤BB-1 at hh; constructor <;> omega
    · have hh := ho 1; change 0≤2*(((v:ℤ)+1)*BB-KK+(m:ℤ)*LL) ∧ 2*(((v:ℤ)+1)*BB-KK+(m:ℤ)*LL)≤AA-1 at hh; constructor <;> omega
    · have hh := ho 2; change 0≤2*(((v:ℤ)+1)*BB-LL) ∧ 2*(((v:ℤ)+1)*BB-LL)≤KK-1 at hh; constructor <;> omega
    · constructor <;> omega
    · simpa [w,word,P,t] using hzold
  let pre := P 0 ++ [t 0]
  let post := P 1 ++ t 1 :: P 2 ++ t 2 :: P 3 ++ [t 3]
  have hw : w=pre++post := by simp [w,word,pre,post,List.append_assoc]
  have hlen : pre.length=d := by dsimp [pre,P,bank]; simp; omega
  have hear : insertAt k w d=pre++k::post := by
    rw [hw,←hlen]
    simp [insertAt]
  have newstrip : InStrip g N 0 (insertAt k w d) := by
    rw [hear]
    change InStrip g N 0 (P 0 ++ t 0 :: (k::P 1) ++ t 1 :: P 2 ++ t 2 :: P 3 ++ [t 3])
    apply four_strip g (P 0) (k::P 1) (P 2) (P 3) (t 0) (t 1) (t 2) (t 3) N 0
      (fun i hi => (pos 0 i hi).2) ?_
      (fun i hi => (pos 2 i hi).2) (fun i hi => (pos 3 i hi).2) le_rfl
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · rw [hfresh]
        have hAA := ((chain_values a b c d ha hb hc hd).1 0).1
        change 1≤AA at hAA
        omega
      · exact (pos 1 i hi).2
    · have hh := hn 0; change 0≤2*(UU-2*AA) ∧ 2*(UU-2*AA)≤UU-1 at hh; constructor <;> omega
    · have hh := hn 1; change 0≤2*(((v:ℤ)+1)*UU-WW+(m:ℤ)*VV) ∧ 2*(((v:ℤ)+1)*UU-WW+(m:ℤ)*VV)≤AA-1 at hh
      simp only [List.map_cons,List.sum_cons,hfresh]
      constructor <;> omega
    · have hh := hn 2; change 0≤2*(((v:ℤ)+1)*UU-VV) ∧ 2*(((v:ℤ)+1)*UU-VV)≤WW-1 at hh
      simp only [List.map_cons,List.sum_cons,hfresh]
      constructor <;> omega
    · constructor <;> omega
    · have sumform : ((pre++k::post).map g).sum=AA+(w.map g).sum := by
        rw [hw]
        simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,hfresh]
        ring
      have hform : P 0 ++ t 0 :: (k::P 1) ++ t 1 :: P 2 ++ t 2 :: P 3 ++ [t 3]=pre++k::post := by
        simp [pre,post,List.append_assoc]
      rw [hform,sumform]
      simpa using hznew
  exact ⟨hp,by dsimp [k]; omega,oldstrip,newstrip⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
