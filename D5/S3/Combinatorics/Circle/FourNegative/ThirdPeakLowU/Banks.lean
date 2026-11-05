/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Banks
   generality: I
   mirror-B: none(waiver:consumed-low-u-support)
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Literal low-U label banks and their exact saturation-aware masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! Literal low-U label banks and their exact saturation-aware masses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU

open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private size sourceMod base newBase charge oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase weightedMask packet_masses chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! The packet order is shared by I and II.  The four masks are literal
    complements in their own full physical banks; the fresh label is inserted
    inside the second packet, after its positives and before the W negative. -/

private def lowUBanks (a b c d u v w : ℕ) : Fin 4 → List ℕ :=
  let uf := 2^(d-1)-1
  let vf := 2^(c-1)-1
  let wf := 2^(b-1)-1
  let xf := 2^(a-1)-1
  ![chamberLabels (c-1) d (vf ^^^ (v-1)),
    chamberLabels (b-1) (d+c) (wf ^^^ w) ++ chamberLabels (d-1) 0 u,
    chamberLabels (b-1) (d+c) w ++ chamberLabels (a-1) (d+c+b) xf,
    chamberLabels (d-1) 0 (uf ^^^ u) ++ chamberLabels (c-1) d (v-1)]

private def lowUTerminals (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d+c-1,d+c+b-1,d+c+b+a-1,d-1]

private def lowUWord (a b c d u v w : ℕ) : List ℕ :=
  let P := lowUBanks a b c d u v w
  let T := lowUTerminals a b c d
  P 0 ++ [T 0] ++ P 1 ++ [T 1] ++ P 2 ++ [T 2] ++ P 3 ++ [T 3]

private theorem lowU_inventory (a b c d u v w : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hu : u < 2^(d-1)) (hv : v-1 < 2^(c-1)) (hw : w < 2^(b-1)) :
    (lowUWord a b c d u v w).Perm (List.range (a+b+c+d)) := by
  let uf := 2^(d-1)-1
  let vf := 2^(c-1)-1
  let wf := 2^(b-1)-1
  let xf := 2^(a-1)-1
  let U0 := chamberLabels (d-1) 0 (uf ^^^ u)
  let U1 := chamberLabels (d-1) 0 u
  let V0 := chamberLabels (c-1) d (vf ^^^ (v-1))
  let V1 := chamberLabels (c-1) d (v-1)
  let W0 := chamberLabels (b-1) (d+c) (wf ^^^ w)
  let W1 := chamberLabels (b-1) (d+c) w
  let X0 := chamberLabels (a-1) (d+c+b) xf
  have hU := chamberLabels_split (d-1) 0 uf u
    (by intro i hi _; simp [uf, Nat.testBit_two_pow_sub_one, hi])
  have hV := chamberLabels_split (c-1) d vf (v-1)
    (by intro i hi _; simp [vf, Nat.testBit_two_pow_sub_one, hi])
  have hW := chamberLabels_split (b-1) (d+c) wf w
    (by intro i hi _; simp [wf, Nat.testBit_two_pow_sub_one, hi])
  have hu' : (U0 ++ U1).Perm (List.range' 0 (d-1)) := by
    simpa only [U0,U1,uf,chamberLabels_full] using hU
  have hv' : (V0 ++ V1).Perm (List.range' d (c-1)) := by
    simpa only [V0,V1,vf,chamberLabels_full] using hV
  have hw' : (W0 ++ W1).Perm (List.range' (d+c) (b-1)) := by
    simpa only [W0,W1,wf,chamberLabels_full] using hW
  have join (off m n : ℕ) :
      List.range' off m ++ List.range' (off+m) n = List.range' off (m+n) :=
    List.range'_append_1
  have hX : X0 = List.range' (d+c+b) (a-1) := by
    simp only [X0,xf,chamberLabels_full]
  have merge (off len : ℕ) (hl : 1 ≤ len) :
      List.range' off (len-1) ++ [off+len-1] = List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have h0 := merge 0 d (by omega)
  have h1 := merge d c (by omega)
  have h2 := merge (d+c) b (by omega)
  have h3 := merge (d+c+b) a (by omega)
  simp only [Nat.zero_add] at h0
  have hrange :
      ((List.range' 0 (d-1) ++ [d-1]) ++
        (List.range' d (c-1) ++ [d+c-1]) ++
        (List.range' (d+c) (b-1) ++ [d+c+b-1]) ++
        (List.range' (d+c+b) (a-1) ++ [a+b+c+d-1])) =
        List.range (a+b+c+d) := by
    rw [h0,h1,h2]
    rw [show a+b+c+d-1=d+c+b+a-1 by omega, h3]
    have j0 : List.range' 0 d ++ List.range' d c = List.range' 0 (d+c) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d) (n:=c))
    have j1 : List.range' 0 (d+c) ++ List.range' (d+c) b =
        List.range' 0 (d+c+b) := by
      simpa only [Nat.zero_add] using
        (List.range'_append_1 (s:=0) (m:=d+c) (n:=b))
    have j2 : List.range' 0 (d+c+b) ++ List.range' (d+c+b) a =
        List.range' 0 (a+b+c+d) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a))
    rw [j0,j1,j2]
    simp only [Nat.zero_add,←List.range_eq_range']
  have hblocks :
      (lowUWord a b c d u v w : Multiset ℕ) =
        ↑V0 + {d+c-1} + ↑W0 + {d+c+b-1} + ↑U1 +
        {a+b+c+d-1} + ↑W1 + ↑X0 +
        ↑U0 + ↑V1 + {d-1} := by
    dsimp [lowUWord,lowUBanks,lowUTerminals,W0,W1,U0,U1,V0,V1,X0,uf,vf,wf,xf]
    simp only [←Multiset.coe_add,Multiset.coe_singleton]
    ac_rfl
  have huM := Multiset.coe_eq_coe.mpr hu'
  have hvM := Multiset.coe_eq_coe.mpr hv'
  have hwM := Multiset.coe_eq_coe.mpr hw'
  simp only [←Multiset.coe_add] at huM hvM hwM
  apply Multiset.coe_eq_coe.mp
  rw [hblocks]
  calc
    (V0 : Multiset ℕ) + {d+c-1} + (W0 : Multiset ℕ) + {d+c+b-1} +
        (U1 : Multiset ℕ) + {a+b+c+d-1} + (W1 : Multiset ℕ) +
        (X0 : Multiset ℕ) + (U0 : Multiset ℕ) + (V1 : Multiset ℕ) + {d-1} =
      ((U0 : Multiset ℕ) + U1) + {d-1} + ((V0 : Multiset ℕ) + V1) +
        {d+c-1} + ((W0 : Multiset ℕ) + W1) + {d+c+b-1} +
        (X0 : Multiset ℕ) + {a+b+c+d-1} := by ac_rfl
    _ = ↑(List.range' 0 (d-1)) + {d-1} +
        ↑(List.range' d (c-1)) + {d+c-1} +
        ↑(List.range' (d+c) (b-1)) + {d+c+b-1} +
        ↑(List.range' (d+c+b) (a-1)) + {a+b+c+d-1} := by
      rw [huM,hvM,hwM,hX]
    _ = ↑(List.range (a+b+c+d)) := by
      rw [←hrange]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem lowU_good (a b c d u v w : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hu : u < 2^(d-1)) (hv : v-1 < 2^(c-1)) (hw : w < 2^(b-1))
    (j : Fin 4) (i : ℕ) (hi : i ∈ lowUBanks a b c d u v w j) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  have range_iff (start len : ℕ) :
      i ∈ List.range' start len ↔ start ≤ i ∧ i < start+len := by
    simp only [List.mem_range',Nat.one_mul]
    constructor
    · rintro ⟨k,hk,rfl⟩; omega
    · intro hh; exact ⟨i-start,by omega,by omega⟩
  fin_cases j <;> dsimp [lowUBanks] at hi
  · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  · simp only [List.mem_append] at hi
    rcases hi with hi|hi
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      omega
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      omega
  · simp only [List.mem_append] at hi
    rcases hi with hi|hi
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      omega
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      omega
  · simp only [List.mem_append] at hi
    rcases hi with hi|hi
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      omega
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      omega


private theorem lowU_list_masses (a b c d u v w : ℕ)
    (hu : u < 2^(d-1)) (hv : v-1 < 2^(c-1)) (hw : w < 2^(b-1))
    (f : ℕ → ℤ) (F : Fin 4 → ℤ)
    (hf : ∀ r : Fin 4, ∀ e < chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    let C := fun r : Fin 4 => ((2^(chainLength a b c d r-1)-1 : ℕ) : ℤ)
    (fun r => ((lowUBanks a b c d u v w r).map f).sum) =
      ![(C 1-(v-1 : ℕ))*F 1,(C 2-w)*F 2+u*F 0,
        w*F 2+C 3*F 3,(C 0-u)*F 0+(v-1 : ℕ)*F 1] := by
  dsimp only
  let full := fun r : Fin 4 => 2^(chainLength a b c d r-1)-1
  have hfull (r : Fin 4) : full r < 2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have mass (r : Fin 4) (m : ℕ) (hm : m < 2^(chainLength a b c d r-1)) :
      ((chamberLabels (chainLength a b c d r-1) (chainStart b c d r) m).map f).sum =
        (m : ℤ)*F r := chamberLabels_sum _ _ _ hm f (F r) (hf r)
  have comp (r : Fin 4) (m : ℕ) (hm : m < 2^(chainLength a b c d r-1)) :
      ((chamberLabels (chainLength a b c d r-1) (chainStart b c d r)
        (full r ^^^ m)).map f).sum = ((full r : ℤ)-m)*F r := by
    have hs := ((chamberLabels_split (chainLength a b c d r-1)
      (chainStart b c d r) (full r) m
      (by intro e he _; simp [full,Nat.testBit_two_pow_sub_one,he])).map f).sum_eq
    simp only [List.map_append,List.sum_append] at hs
    rw [mass r m hm,mass r _ (hfull r)] at hs
    linarith only [hs]
  have hu' : u < 2^(chainLength a b c d 0-1) := by simpa [chainLength] using hu
  have hv' : v-1 < 2^(chainLength a b c d 1-1) := by simpa [chainLength] using hv
  have hw' : w < 2^(chainLength a b c d 2-1) := by simpa [chainLength] using hw
  have mU := mass 0 u hu'
  have mV := mass 1 (v-1) hv'
  have mW := mass 2 w hw'
  have mX := mass 3 _ (hfull 3)
  have nU := comp 0 u hu'
  have nV := comp 1 (v-1) hv'
  have nW := comp 2 w hw'
  simp only [chainLength,chainStart,full,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] at *
  funext r
  fin_cases r <;> dsimp [lowUBanks]
  all_goals simp only [List.map_append,List.sum_append,mU,mV,mW,mX,nU,nV,nW]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
