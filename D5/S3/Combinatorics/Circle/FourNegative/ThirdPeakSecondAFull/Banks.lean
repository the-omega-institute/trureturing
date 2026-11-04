/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks
   generality: I
   mirror-B: none(waiver:physical-dependent-source-family)
   mirror-E: none(waiver:physical-dependent-source-family)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Native mask partitions and the five literal bank inventories. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
open SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private full stock complement terminal q h H fmask jmask mmask Rmask deltaMask rho branch Branch isFinite branch_complete
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private size negatives chainLength chainStart
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def finiteBanks (a b c d : ℕ) : List (List ℕ × ℕ) :=
  if (a,b,c,d)=(4,2,5,2) then
    [([0,2,3],6),([4,5],1),([9,11],12),([7,10],8)]
  else if (a,b,c,d)=(4,2,6,2) then
    [([0,2,3,4],7),([5,8],13),([10,12],9),([6,11],1)]
  else
    [([0,2,3,4],7),([5,6],1),([8,10,11],14),([12,13],9)]

private def genericBanks (a b c d : ℕ) (br : Branch) : List (List ℕ × ℕ) :=
  let U := stock a b c d 0 (full a b c d 0)
  let V (m : ℕ) := stock a b c d 1 m
  let W := stock a b c d 2 (full a b c d 2)
  let X (m : ℕ) := stock a b c d 3 m
  let Vc (m : ℕ) := complement a b c d 1 m
  let Xc (m : ℕ) := complement a b c d 3 m
  let n0 := terminal a b c d 0
  let n1 := terminal a b c d 1
  let n2 := terminal a b c d 2
  let n3 := terminal a b c d 3
  match br with
  | .a1 =>
      [(Vc (h b c-1),n1),(W++V (h b c-H a c),n2),
       (Xc 1,n3),(U++V (H a c-1)++X 1,n0)]
  | .a2 =>
      [(Vc (h b c-1),n1),(W++V (h b c-H a c),n2),
       (Xc (fmask a d)++V (H a c-1),n3),(U++X (fmask a d),n0)]
  | .b0 =>
      [(Vc (h b c-1),n1),(W++X (mmask a b d)++V (h b c-Rmask a b c d),n2),
       (Xc (mmask a b d ||| fmask a d)++V (Rmask a b c d-1),n3),
       (U++X (fmask a d),n0)]
  | .b1one | .b1quot =>
      [(Vc (h b c-1),n1),
       (W++X (mmask a b d)++V (h b c-Rmask a b c d+deltaMask a b c d),n2),
       (Xc (mmask a b d ||| fmask a d)++
          V ((Rmask a b c d-1) ^^^ deltaMask a b c d),n3),
       (U++X (fmask a d),n0)]
  | .c =>
      let M := 3*rho a d/4
      let nu := rho a d/2
      [(Xc (M-1),n3),(X (M-1)++complement a b c d 2 1++V 1,n2),
       (complement a b c d 1 (1 ||| nu),n1),
       (U++stock a b c d 2 1++V nu,n0)]
  | .finite1 | .finite2 | .finite3 => finiteBanks a b c d

private def bankWord (a b c d : ℕ) : List ℕ :=
  (genericBanks a b c d (branch a b c d)).flatMap (fun p => p.1 ++ [p.2])

private theorem chamber_split (len off mask : ℕ) (hm : mask < 2^len) :
    (chamberLabels len off (2^len-1 ^^^ mask) ++ chamberLabels len off mask).Perm
      (List.range' off len) := by
  simpa only [chamberLabels_full] using
    (chamberLabels_split len off (2^len-1) mask
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he]))

private theorem inventory (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    (bankWord a b c d).Perm (List.range (size a b c d)) := by
  classical
  have hcase := branch_complete a b c d hb hba hac hd hda
  rcases hcase with h|h|h|h|h|h|h|h|h <;> subst branch
  all_goals
    simp [bankWord,genericBanks,finiteBanks,terminal,full,stock,complement,
      q,h,H,rho,fmask,jmask,mmask,Rmask,deltaMask,Branch] at *
  all_goals
    apply List.Perm.trans ?_ (by
      simpa [size] using List.range'_append_1 (s:=0) (m:=d) (n:=c+b+a))
  all_goals
    try { apply Multiset.coe_eq_coe.mp; simp only [←Multiset.coe_add]; ac_rfl }
  all_goals omega

private theorem stock_good (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (r : Fin 4) (mask i : ℕ) (hi : i ∈ stock a b c d r mask) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  obtain ⟨e,he,_,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;>
    simp only [chainLength,chainStart,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three] at he hval <;>
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false] <;> omega

private theorem terminal_good (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (r : Fin 4) :
    terminal a b c d r < size a b c d ∧
      terminal a b c d r ∈ negatives a b c d := by
  fin_cases r <;> simp [terminal,negatives,size] <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
