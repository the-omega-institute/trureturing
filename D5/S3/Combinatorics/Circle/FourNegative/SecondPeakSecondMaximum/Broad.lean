/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/Broad
   generality: I
   mirror-B: none(waiver:private-consumed-physical-certificate)
   mirror-E: none(waiver:private-consumed-physical-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical reversed-middle certificate with the actual binary U transfer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BroadData
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
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

open private Values values
  Values.z Values.w Values.r Values.q Values.x Values.y Values.H Values.S
  Values.A Values.B Values.L Values.K Values.SU Values.SV Values.SW
  Values.D Values.Dp Values.E Values.F Values.J
  broad_windows range_mass broadBanks broadTerminals broadWord
  broadBanks_inventory broadBanks_good
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum.BroadData

set_option maxHeartbeats 2400000 in
private theorem broad_certificate_exists (a b c d : ℕ)
    (hc : 2≤c) (hcd : c+2≤d) (hda : d<a) (hab : a≤b) :
    Nonempty (Certificate a b c d) := by
  classical
  let z : ℤ := 2^c
  let w : ℤ := 2^d
  let r : ℤ := 2^(a-d)
  let q : ℤ := 2^(b-a)
  let V := values z w r q
  have hz : 4≤z := by dsimp [z]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc; norm_num at this; omega
  have hw : 4*z≤w := by
    change 4*(2:ℤ)^c ≤ (2:ℤ)^d
    have he : (2:ℤ)^d=(2:ℤ)^c*2^(d-c) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    have hdc : 2≤d-c := by omega
    have : 4≤(2:ℤ)^(d-c) := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hdc
      norm_num at hh ⊢
      exact hh
    have hp : 0 < (2:ℤ)^c := by positivity
    nlinarith
  have hr : 2≤r := by dsimp [r]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (by omega : 1≤a-d); norm_num at this; omega
  have hq : 1≤q := by
    dsimp [q]
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 0≤b-a by omega)
    norm_num at hh ⊢
    exact hh
  have hwin := broad_windows z w r q hz hw hr hq
  rcases hwin with ⟨hDp,hDpD,hDH,hKcap,hSWcap,hAcap,hEpos,hEupper,hFpos,
    hJpos,hJA,hB3A,hS4A,hXold,hXoldcap,hXnew,hXnewcap⟩
  have hx : (2:ℤ)^a = r*w := by
    dsimp [r,w]
    rw [← pow_add]
    congr 1
    omega
  have hy : (2:ℤ)^b = q*r*w := by
    dsimp [q,r,w]
    rw [← pow_add,← pow_add]
    congr 1 <;> omega
  have hzpow : (2:ℤ)^c = z := by rfl
  have hwpow : (2:ℤ)^d = w := by rfl
  have hbase : base a b c d = ![(Values.A V),(Values.B V),(Values.L V),(Values.K V)] := by
    funext i
    fin_cases i <;> dsimp [base,V,values]
    all_goals try simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
      Matrix.cons_val_succ]
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try rw [hzpow]
    all_goals try rw [hwpow]
    all_goals ring_nf
  have hnewbase : newBase a b c d =
      ![2*(Values.A V),(Values.SU V),(Values.SV V),(Values.SW V)] := by
    funext i
    fin_cases i <;> dsimp [newBase,charge,base,V,values]
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try rw [hzpow]
    all_goals try rw [hwpow]
    all_goals ring_nf
  let f := oldValue a b c d
  let g := newValue a b c d
  let N := sourceMod a b c d
  have hqnonneg : 0 ≤ (Values.E V) / (Values.A V) :=
    Int.ediv_nonneg hEpos.le (by dsimp [V,values]; positivity)
  let u : ℕ := ((Values.E V) / (Values.A V)).toNat
  have hu_cast : (u : ℤ) = (Values.E V) / (Values.A V) := by
    dsimp [u]
    exact Int.toNat_of_nonneg hqnonneg
  have hApos : 0 < (Values.A V) := by dsimp [V,values]; positivity
  have hrem_nonneg : 0 ≤ (Values.E V) % (Values.A V) :=
    Int.emod_nonneg _ (by exact ne_of_gt hApos)
  have hdiv : (u:ℤ)*(Values.A V) + (Values.E V) % (Values.A V) = (Values.E V) := by
    simpa [hu_cast] using Int.ediv_mul_add_emod (Values.E V) (Values.A V)
  let P := broadBanks a b c d u
  let T := broadTerminals a b c d
  let B := fun j : Fin 4 => (P j).toFinset
  let ps : List (Finset ℕ × ℕ) :=
    [(B 0,T 0),(B 1,T 1),(B 2,T 2),(B 3,T 3)]
  have hu : u < 2^(d-1) := by
    have he : 0 ≤ u := by omega
    have hltInt : 2*(u:ℤ) < w := by
      have hle : (u:ℤ)*(Values.A V) ≤ (Values.E V) := by nlinarith [hdiv,hrem_nonneg]
      have h2le : 2*((u:ℤ)*(Values.A V)) ≤ 2*(Values.E V) :=
        mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℤ) ≤ 2)
      have h2le' : 2*(u:ℤ)*(Values.A V) ≤ 2*(Values.E V) := by
        simpa [mul_assoc] using h2le
      have hqprod0 : 2*(u:ℤ)*(Values.A V) < (Values.w V)*(Values.A V) := lt_of_le_of_lt h2le' hEupper
      have hqprod : 2*(u:ℤ)*(Values.A V) < w*(Values.A V) := by
        simpa [V,values] using hqprod0
      exact lt_of_mul_lt_mul_right hqprod hApos.le
    have hltNat : 2*u < (2:ℕ)^d := by
      have hltInt' : 2*(u:ℤ) < (2:ℤ)^d := by simpa [w] using hltInt
      exact_mod_cast hltInt'
    have hp : (2:ℤ)^(d-1) * 2 = w := by
      calc
        (2:ℤ)^(d-1) * 2 = (2:ℤ)^((d-1)+1) := by rw [pow_succ]
        _ = (2:ℤ)^d := by congr 1 <;> omega
        _ = w := hwpow.symm
    have hp' : (2:ℕ)^(d-1) * 2 = 2^d := by
      calc
        (2:ℕ)^(d-1) * 2 = 2^((d-1)+1) := by rw [pow_succ]
        _ = 2^d := by congr 1 <;> omega
    rw [← hp'] at hltNat
    omega
  have hp := broadBanks_inventory a b c d (u) hc hcd hda hab hu
  have hn (j : Fin 4) : (P j).Nodup := by
    have ht := hp.nodup_iff.mpr List.nodup_range
    simp only [broadWord,List.nodup_append] at ht
    fin_cases j <;> tauto
  have hperm (j : Fin 4) : (B j).toList.Perm (P j) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hn j)).mpr
    intro i
    simp [B]
  have good (j : Fin 4) (i : ℕ) (hi : i ∈ B j) :
      i < size a b c d ∧ i ∉ negatives a b c d := by
    exact broadBanks_good a b c d (u) hc hcd hda hab hu j i
      (List.mem_toFinset.mp hi)
  have hm (side : Bool) (j : Fin 4) :
      (if side then newMass a b c d (B j) else oldMass a b c d (B j)) =
      ((P j).map (if side then g else f)).sum := by
    have mm := packet_masses a b c d (by omega) (by omega) (by omega) (by omega)
      (B j) (by intro i hi; exact good j i hi)
    have tosum (ff : ℕ→ℤ) : (∑ i∈B j,ff i)=((P j).map ff).sum := by
      exact List.sum_toFinset ff (hn j)
    cases side
    · exact mm.1.symm.trans (tosum f)
    · exact mm.2.symm.trans (tosum g)
  have tab := chain_values a b c d (by omega) (by omega) (by omega) (by omega)
  have hW (side : Bool) (i : ℕ) (hi : i<a-1) :
      (if side then g else f) (d+c+b-a+i) =
        (2:ℤ)^i * (if side then q*(Values.SV V) else q*(Values.L V)) := by
    cases side
    · have hh := tab.2.1 2 (b-a+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + (b-a+i) = d+c+b-a+i by
        simp [chainStart]; omega] at hh
      change f (d+c+b-a+i) = (2:ℤ)^(b-a+i)*base a b c d 2 at hh
      rw [hbase] at hh
      simpa [pow_add,q,mul_assoc,mul_left_comm,mul_comm] using hh
    · have hh := tab.2.2.1 2 (b-a+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + (b-a+i) = d+c+b-a+i by
        simp [chainStart]; omega] at hh
      change g (d+c+b-a+i) = (2:ℤ)^(b-a+i)*newBase a b c d 2 at hh
      rw [hnewbase] at hh
      simpa [pow_add,q,mul_assoc,mul_left_comm,mul_comm] using hh
  have hW1 (side : Bool) (i : ℕ) (hi : i<b-a) :
      (if side then g else f) (d+c+i) =
        (2:ℤ)^i * (if side then (Values.SV V) else (Values.L V)) := by
    cases side
    · have hh := tab.2.1 2 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + i = d+c+i by simp [chainStart]] at hh
      change f (d+c+i) = (2:ℤ)^i*base a b c d 2 at hh
      rw [hbase] at hh
      exact hh
    · have hh := tab.2.2.1 2 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + i = d+c+i by simp [chainStart]] at hh
      change g (d+c+i) = (2:ℤ)^i*newBase a b c d 2 at hh
      rw [hnewbase] at hh
      exact hh
  have hX (side : Bool) (i : ℕ) (hi : i<d-1) :
      (if side then g else f) (a+b+c+i) =
        (2:ℤ)^i * (if side then r*(Values.SW V) else r*(Values.K V)) := by
    cases side
    · have hh := tab.2.1 3 (a-d+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + (a-d+i) = a+b+c+i by
        simp [chainStart]; omega] at hh
      change f (a+b+c+i) = (2:ℤ)^(a-d+i)*base a b c d 3 at hh
      rw [hbase] at hh
      simpa [pow_add,r,mul_assoc,mul_left_comm,mul_comm] using hh
    · have hh := tab.2.2.1 3 (a-d+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + (a-d+i) = a+b+c+i by
        simp [chainStart]; omega] at hh
      change g (a+b+c+i) = (2:ℤ)^(a-d+i)*newBase a b c d 3 at hh
      rw [hnewbase] at hh
      simpa [pow_add,r,mul_assoc,mul_left_comm,mul_comm] using hh
  have hX1 (side : Bool) (i : ℕ) (hi : i<a-d) :
      (if side then g else f) (b+c+d+i) =
        (2:ℤ)^i * (if side then (Values.SW V) else (Values.K V)) := by
    cases side
    · have hh := tab.2.1 3 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + i = b+c+d+i by
        simp [chainStart]; omega] at hh
      change f (b+c+d+i) = (2:ℤ)^i*base a b c d 3 at hh
      rw [hbase] at hh
      simpa [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.vecHead, Matrix.vecTail] using hh
    · have hh := tab.2.2.1 3 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + i = b+c+d+i by
        simp [chainStart]; omega] at hh
      change g (b+c+d+i) = (2:ℤ)^i*newBase a b c d 3 at hh
      rw [hnewbase] at hh
      simpa [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.vecHead, Matrix.vecTail] using hh
  have hV (side : Bool) (i : ℕ) (hi : i<c-1) :
      (if side then g else f) (d+i) =
        (2:ℤ)^i * (if side then (Values.SU V) else (Values.B V)) := by
    cases side
    · have hh := tab.2.1 1 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 1 + i = d+i by simp [chainStart]] at hh
      change f (d+i) = (2:ℤ)^i*base a b c d 1 at hh
      rw [hbase] at hh
      exact hh
    · have hh := tab.2.2.1 1 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 1 + i = d+i by simp [chainStart]] at hh
      change g (d+i) = (2:ℤ)^i*newBase a b c d 1 at hh
      rw [hnewbase] at hh
      exact hh
  have hpowq : (2:ℤ)^(b-1) = (2:ℤ)^(a-1) * q := by
    dsimp [q]
    rw [← pow_add]
    congr 1
    omega
  have hpowr : (2:ℤ)^(a-1) = (2:ℤ)^(d-1) * r := by
    dsimp [r]
    rw [← pow_add]
    congr 1
    omega
  have hWold : ((P 0).map f).sum = ((2:ℤ)^(b-1)-q)*(Values.L V) := by
    dsimp [P,broadBanks]
    have hh := range_mass f (q*(Values.L V)) (d+c+b-a) (a-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hW false i hi)
    rw [hh]
    rw [hpowq]
    ring
  have hWnew : ((P 0).map g).sum = ((2:ℤ)^(b-1)-q)*(Values.SV V) := by
    dsimp [P,broadBanks]
    have hh := range_mass g (q*(Values.SV V)) (d+c+b-a) (a-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hW true i hi)
    rw [hh]
    rw [hpowq]
    ring
  have hXoldMass : ((P 1).map f).sum = ((2:ℤ)^(a-1)-r)*(Values.K V) := by
    dsimp [P,broadBanks]
    have hh := range_mass f (r*(Values.K V)) (a+b+c) (d-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hX false i hi)
    rw [hh]
    rw [hpowr]
    ring
  have hXnewMass : ((P 1).map g).sum = ((2:ℤ)^(a-1)-r)*(Values.SW V) := by
    dsimp [P,broadBanks]
    have hh := range_mass g (r*(Values.SW V)) (a+b+c) (d-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hX true i hi)
    rw [hh]
    rw [hpowr]
    ring
  have hVold : ((List.range' d (c-1)).map f).sum =
      ((2:ℤ)^(c-1)-1)*(Values.B V) := by
    exact range_mass f (Values.B V) d (c-1) (by
      intro i hi; simpa using hV false i hi)
  have hVnew : ((List.range' d (c-1)).map g).sum =
      ((2:ℤ)^(c-1)-1)*(Values.SU V) := by
    exact range_mass g (Values.SU V) d (c-1) (by
      intro i hi; simpa using hV true i hi)
  have hW1old : ((List.range' (d+c) (b-a)).map f).sum =
      ((2:ℤ)^(b-a)-1)*(Values.L V) := by
    exact range_mass f (Values.L V) (d+c) (b-a) (by
      intro i hi; simpa using hW1 false i hi)
  have hW1new : ((List.range' (d+c) (b-a)).map g).sum =
      ((2:ℤ)^(b-a)-1)*(Values.SV V) := by
    exact range_mass g (Values.SV V) (d+c) (b-a) (by
      intro i hi; simpa using hW1 true i hi)
  have hX1old : ((List.range' (b+c+d) (a-d)).map f).sum =
      ((2:ℤ)^(a-d)-1)*(Values.K V) := by
    exact range_mass f (Values.K V) (b+c+d) (a-d) (by
      intro i hi; simpa using hX1 false i hi)
  have hX1new : ((List.range' (b+c+d) (a-d)).map g).sum =
      ((2:ℤ)^(a-d)-1)*(Values.SW V) := by
    exact range_mass g (Values.SW V) (b+c+d) (a-d) (by
      intro i hi; simpa using hX1 true i hi)
  let U0 := chamberLabels (d-1) 0 ((2^(d-1)-1) ^^^ (u))
  let U1 := chamberLabels (d-1) 0 (u)
  have hU1old : (U1.map f).sum = ((u : ℕ):ℤ)*(Values.A V) := by
    dsimp [U1]
    apply chamberLabels_sum
    · exact hu
    · intro e he
      have hh := tab.2.1 0 e (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + e = e by simp [chainStart]] at hh
      change f e = (2:ℤ)^e * base a b c d 0 at hh
      rw [hbase] at hh
      simpa [Nat.zero_add, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.vecHead, Matrix.vecTail] using hh
  have hU1new : (U1.map g).sum = ((u : ℕ):ℤ)*(2*(Values.A V)) := by
    dsimp [U1]
    apply chamberLabels_sum
    · exact hu
    · intro e he
      have hh := tab.2.2.1 0 e (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + e = e by simp [chainStart]] at hh
      change g e = (2:ℤ)^e * newBase a b c d 0 at hh
      rw [hnewbase] at hh
      simpa [Nat.zero_add, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.vecHead, Matrix.vecTail] using hh
  have hUfullold : ((List.range' 0 (d-1)).map f).sum =
      ((2:ℤ)^(d-1)-1)*(Values.A V) := by
    exact range_mass f (Values.A V) 0 (d-1) (by
      intro i hi
      have hh := tab.2.1 0 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + i = i by simp [chainStart]] at hh
      change f i = (2:ℤ)^i * base a b c d 0 at hh
      rw [hbase] at hh
      simpa using hh)
  have hUfullnew : ((List.range' 0 (d-1)).map g).sum =
      ((2:ℤ)^(d-1)-1)*(2*(Values.A V)) := by
    exact range_mass g (2*(Values.A V)) 0 (d-1) (by
      intro i hi
      have hh := tab.2.2.1 0 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + i = i by simp [chainStart]] at hh
      change g i = (2:ℤ)^i * newBase a b c d 0 at hh
      rw [hnewbase] at hh
      simpa using hh)
  have hU0old : (U0.map f).sum =
      ((2:ℤ)^(d-1)-1-(u : ℕ))*(Values.A V) := by
    have hU1old' :
        (chamberLabels (d-1) 0 u |>.map f).sum = ((u : ℕ):ℤ)*(Values.A V) := by
      simpa [U1] using hU1old
    have hs := chamberLabels_split (d-1) 0 (2^(d-1)-1) (u)
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    have hs' := (hs.map f).sum_eq
    rw [chamberLabels_full (d-1) 0] at hs'
    simp only [List.map_append, List.sum_append] at hs'
    rw [hU1old'] at hs'
    rw [hUfullold] at hs'
    norm_num at hs'
    push_cast at hs'
    have hs0 :
        (List.map f (chamberLabels (d-1) 0 ((2^(d-1)-1) ^^^ u))).sum =
          ((2:ℤ)^(d-1)-1-(u : ℕ))*(Values.A V) := by
      linarith only [hs']
    simpa [U0] using hs0
  have hU0new : (U0.map g).sum =
      ((2:ℤ)^(d-1)-1-(u : ℕ))*(2*(Values.A V)) := by
    have hU1new' :
        (chamberLabels (d-1) 0 u |>.map g).sum = ((u : ℕ):ℤ)*(2*(Values.A V)) := by
      simpa [U1] using hU1new
    have hs := chamberLabels_split (d-1) 0 (2^(d-1)-1) (u)
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    have hs' := (hs.map g).sum_eq
    rw [chamberLabels_full (d-1) 0] at hs'
    simp only [List.map_append, List.sum_append] at hs'
    rw [hU1new'] at hs'
    rw [hUfullnew] at hs'
    norm_num at hs'
    push_cast at hs'
    have hs0 :
        (List.map g (chamberLabels (d-1) 0 ((2^(d-1)-1) ^^^ u))).sum =
          ((2:ℤ)^(d-1)-1-(u : ℕ))*(2*(Values.A V)) := by
      linarith only [hs']
    simpa [U0] using hs0
  have mo : ((P 0).map f).sum = ((2:ℤ)^(b-1)-q)*(Values.L V) ∧
      ((P 1).map f).sum = ((2:ℤ)^(a-1)-r)*(Values.K V) ∧
      ((P 2).map f).sum = ((2:ℤ)^(d-1)-1-(u : ℕ))*(Values.A V) ∧
      ((P 3).map f).sum = ((2:ℤ)^(c-1)-1)*(Values.B V) +
        ((2:ℤ)^(b-a)-1)*(Values.L V) + ((2:ℤ)^(a-d)-1)*(Values.K V) +
        ((u : ℕ):ℤ)*(Values.A V) := by
    refine ⟨hWold,hXoldMass,?_,?_⟩
    · dsimp [P,broadBanks,U0]
      exact hU0old
    · dsimp [P,broadBanks,U1]
      simp only [List.map_append,List.sum_append]
      rw [hVold,hW1old,hX1old,hU1old]
  have mg : ((P 0).map g).sum = ((2:ℤ)^(b-1)-q)*(Values.SV V) ∧
      ((P 1).map g).sum = ((2:ℤ)^(a-1)-r)*(Values.SW V) ∧
      ((P 2).map g).sum = ((2:ℤ)^(d-1)-1-(u : ℕ))*(2*(Values.A V)) ∧
      ((P 3).map g).sum = ((2:ℤ)^(c-1)-1)*(Values.SU V) +
        ((2:ℤ)^(b-a)-1)*(Values.SV V) + ((2:ℤ)^(a-d)-1)*(Values.SW V) +
        ((u : ℕ):ℤ)*(2*(Values.A V)) := by
    refine ⟨hWnew,hXnewMass,?_,?_⟩
    · dsimp [P,broadBanks,U0]
      exact hU0new
    · dsimp [P,broadBanks,U1]
      simp only [List.map_append,List.sum_append]
      rw [hVnew,hW1new,hX1new,hU1new]
  have native (j : Fin 4) := native_masses a b c d
    (by omega) (by omega) (by omega) (by omega) j
  have n0 := native 2
  have n1 := native 3
  have n2 := native 0
  have n3 := native 1
  have hcast (n : ℕ) : ((2^(n-1)-1:ℕ):ℤ)=(2:ℤ)^(n-1)-1 := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (n-1);omega)]
    norm_cast
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbase,hnewbase,hcast,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_add]
    at n0 n1 n2 n3
  have e0 : d+c+(b-1)=T 0 := by dsimp [T,broadTerminals];omega
  have e1 : d+c+b+(a-1)=T 1 := by dsimp [T,broadTerminals];omega
  have e2 : d-1=T 2 := by rfl
  have e3 : d+(c-1)=T 3 := by dsimp [T,broadTerminals];omega
  rw [e0] at n0
  rw [e1] at n1
  rw [e3] at n3
  change ((2:ℤ)^(b-1)-1)*(Values.L V)+f (T 0)=(Values.K V)-(Values.L V) ∧
    ((2:ℤ)^(b-1)-1)*(Values.SV V)+g (T 0)=(Values.SW V)-(Values.SV V) ∧
    2*f (T 0)=(Values.K V)-N ∧ 2*g (T 0)=(Values.SW V)-(2*N+1) at n0
  change ((2:ℤ)^(a-1)-1)*(Values.K V)+f (T 1)=(Values.A V)-(Values.K V) ∧
    ((2:ℤ)^(a-1)-1)*(Values.SW V)+g (T 1)=(Values.A V)-(Values.SW V) ∧
    2*f (T 1)=(Values.A V)-N ∧ 2*g (T 1)=(Values.A V)-(2*N+1) at n1
  change ((2:ℤ)^(d-1)-1)*(Values.A V)+f (T 2)=(Values.B V)-(Values.A V) ∧
    ((2:ℤ)^(d-1)-1)*(2*(Values.A V))+g (T 2)=(Values.SU V)-(2*(Values.A V)) ∧
    2*f (T 2)=(Values.B V)-N ∧ 2*g (T 2)=(Values.SU V)-(2*N+1) at n2
  change ((2:ℤ)^(c-1)-1)*(Values.B V)+f (T 3)=(Values.L V)-(Values.B V) ∧
    ((2:ℤ)^(c-1)-1)*(Values.SU V)+g (T 3)=(Values.SV V)-(Values.SU V) ∧
    2*f (T 3)=(Values.L V)-N ∧ 2*g (T 3)=(Values.SV V)-(2*N+1) at n3
  let M := fun j : Fin 4 => oldMass a b c d (B j)
  let G := fun j : Fin 4 => newMass a b c d (B j)
  have m0 : M 0+f (T 0)=(Values.D V) := by
    rw [show M 0=((P 0).map f).sum from hm false 0,mo.1]
    have he : (Values.D V)=(Values.K V)-q*(Values.L V) := rfl
    rw [he]
    nlinarith only [n0.1]
  have m1 : M 1+f (T 1)=(Values.A V)-r*(Values.K V) := by
    rw [show M 1=((P 1).map f).sum from hm false 1,mo.2.1]
    nlinarith only [n1.1]
  have m2 : M 2+f (T 2)=(Values.B V)-(Values.A V)-(u : ℕ)*(Values.A V) := by
    rw [show M 2=((P 2).map f).sum from hm false 2,mo.2.2.1]
    nlinarith only [n2.1]
  have m3 : M 3+f (T 3)=(Values.L V)-(Values.B V)+((2:ℤ)^(b-a)-1)*(Values.L V)+
      ((2:ℤ)^(a-d)-1)*(Values.K V)+(u : ℕ)*(Values.A V) := by
    rw [show M 3=((P 3).map f).sum from hm false 3,mo.2.2.2]
    nlinarith only [n3.1]
  have g0 : G 0+g (T 0)=(Values.Dp V) := by
    rw [show G 0=((P 0).map g).sum from hm true 0,mg.1]
    have he : (Values.Dp V)=(Values.SW V)-q*(Values.SV V) := rfl
    rw [he]
    nlinarith only [n0.2.1]
  have g1 : G 1+g (T 1)=(Values.A V)-r*(Values.SW V) := by
    rw [show G 1=((P 1).map g).sum from hm true 1,mg.2.1]
    nlinarith only [n1.2.1]
  have g2 : G 2+g (T 2)=(Values.SU V)-2*(Values.A V)-
      2*(u : ℕ)*(Values.A V) := by
    rw [show G 2=((P 2).map g).sum from hm true 2,mg.2.2.1]
    nlinarith only [n2.2.1]
  have g3 : G 3+g (T 3)=(Values.SV V)-(Values.SU V)+((2:ℤ)^(b-a)-1)*(Values.SV V)+
      ((2:ℤ)^(a-d)-1)*(Values.SW V)+2*(u : ℕ)*(Values.A V) := by
    rw [show G 3=((P 3).map g).sum from hm true 3,mg.2.2.2]
    nlinarith only [n3.2.1]
  have heold : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2) =
      (Values.E V)-(u : ℕ)*(Values.A V) := by
    have he : (Values.E V)=(Values.B V)+(Values.D V)-r*(Values.K V) := rfl
    rw [he]
    nlinarith only [m0,m1,m2]
  have henew : G 0+g (T 0)+G 1+g (T 1)+G 2+g (T 2)+(Values.A V) =
      (Values.F V)-2*(u : ℕ)*(Values.A V) := by
    have he : (Values.F V)=(Values.SU V)+(Values.Dp V)-r*(Values.SW V) := rfl
    rw [he]
    nlinarith only [g0,g1,g2]
  have zold : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3)=0 := by
    have he : (Values.D V)=(Values.K V)-q*(Values.L V) := rfl
    nlinarith only [m0,m1,m2,m3,he]
  have znew : G 0+g (T 0)+G 1+g (T 1)+G 2+g (T 2)+G 3+g (T 3)+(Values.A V)=0 := by
    have he : (Values.Dp V)=(Values.SW V)-q*(Values.SV V) := rfl
    nlinarith only [g0,g1,g2,g3,he]
  have hrem_lt : (Values.E V) % (Values.A V) < (Values.A V) := Int.emod_lt_of_pos _ hApos
  have hUold : 0 ≤ (Values.E V) % (Values.A V) ∧ 2*((Values.E V) % (Values.A V)) ≤ (Values.B V)-1 := by
    constructor
    · exact hrem_nonneg
    · have hrem_le : (Values.E V) % (Values.A V) ≤ (Values.A V) - 1 := by omega
      have hB3AV : 3 * (Values.A V) < (Values.B V) := by simpa [V] using hB3A
      omega
  have hUnew : 0 ≤ 2*((Values.E V) % (Values.A V))+(Values.J V) ∧
      2*(2*((Values.E V) % (Values.A V))+(Values.J V)) ≤ (Values.SU V)-1 := by
    constructor
    · have hJposV : 0 < (Values.J V) := by simpa [V] using hJpos
      omega
    · rw [show (Values.SU V) = 2 * (Values.B V) - 1 by rfl]
      have hrem_le : (Values.E V) % (Values.A V) ≤ (Values.A V) - 1 := by omega
      have hJAV : (Values.J V) < (Values.A V) := by simpa [V] using hJA
      have hB3AV : 3 * (Values.A V) < (Values.B V) := by simpa [V] using hB3A
      omega
  have heq : (Values.E V)-(u:ℤ)*(Values.A V)=(Values.E V)%(Values.A V) := by
    linarith only [hdiv]
  have win (e S z C : ℤ) (he : 0≤e ∧ 2*e≤S-1)
      (hz : 2*z=S-(2*C+1)) : 0≤e ∧ e-z≤C := by omega
  have hKcapV : 2*(Values.H V) ≤ (Values.K V)-1 := by simpa [V] using hKcap
  have hSWcapV : 2*(Values.H V) ≤ (Values.SW V)-1 := by simpa [V] using hSWcap
  have hDltHV : (Values.D V) < (Values.H V) := by simpa [V] using hDH
  have hDpD_V : (Values.Dp V) < (Values.D V) := by simpa [V] using hDpD
  have hDH_V : (Values.D V) < (Values.H V) := by simpa [V] using hDH
  have hDpV : 0 < (Values.Dp V) := by simpa [V] using hDp
  have hDposV : 0 < (Values.D V) := by omega
  have hDpcap : 2*(Values.Dp V) ≤ (Values.SW V)-1 := by omega
  have hDcap : 2*(Values.D V) ≤ (Values.K V)-1 := by omega
  have k0 := win (Values.D V) (Values.K V) (f (T 0)) (N/2) ⟨by omega,hDcap⟩ (by
    have hz := n0.2.2.1
    omega)
  have k1 := win ((Values.D V)+(Values.S V)-r*(Values.H V)) (Values.A V) (f (T 1)) (N/2)
      ⟨hXold,hXoldcap⟩ (by
    have hz := n1.2.2.1
    omega)
  have k2 := win ((Values.E V)-(u:ℤ)*(Values.A V)) (Values.B V) (f (T 2)) (N/2)
      (by rw [heq]; exact hUold) (by
    have hz := n2.2.2.1
    omega)
  have k0n := win (Values.Dp V) (Values.SW V) (g (T 0)) N ⟨hDp.le,hDpcap⟩ n0.2.2.2
  have k1n := win ((Values.Dp V)+2*(Values.S V)-r*(Values.H V)) (Values.A V) (g (T 1)) N
      ⟨hXnew,hXnewcap⟩ (by
    have hz := n1.2.2.2
    omega)
  have k2n := win ((Values.F V)-2*(u:ℤ)*(Values.A V)) (Values.SU V) (g (T 2)) N
      (by
        have he : (Values.F V)-2*(u:ℤ)*(Values.A V) = 2*((Values.E V)%(Values.A V))+(Values.J V) := by
          have hFJ : (Values.F V) = 2*(Values.E V)+(Values.J V) := by
            dsimp [V,values]
            ring
          calc
            (Values.F V)-2*(u:ℤ)*(Values.A V) = (2*(Values.E V)+(Values.J V))-2*(u:ℤ)*(Values.A V) := by rw [hFJ]
            _ = 2*((Values.E V)-(u:ℤ)*(Values.A V))+(Values.J V) := by ring
            _ = 2*((Values.E V)%(Values.A V))+(Values.J V) := by rw [heq]
        rw [he]
        exact hUnew)
      n2.2.2.2
  have lastO : 0≤-f (T 3) ∧ -f (T 3)≤N/2 := by
    have hh := tab.1 2
    rw [hbase] at hh
    change 1 ≤ (Values.L V) ∧ (Values.L V) < N at hh
    have hz := n3.2.2.1
    change 2*f (T 3)=(Values.L V)-N at hz
    omega
  have lastN : 0≤-g (T 3) ∧ -g (T 3)≤N := by
    have hb := new_base_bounds a b c d (by omega) (by omega) (by omega) (by omega) 2
    rw [hnewbase] at hb
    change 1 ≤ (Values.SV V) ∧ (Values.SV V) < 2*N+1 at hb
    have hz := n3.2.2.2
    change 2*g (T 3)=(Values.SV V)-(2*N+1) at hz
    omega
  refine ⟨DataCertificate.mk ps ?_ ⟨1,by decide⟩ ?_ ?_ ?_ ?_⟩
  · change [T 0,T 1,T 2,T 3].Perm (negatives a b c d)
    have he : negatives a b c d=[T 2,T 3,T 0,T 1] := by
      dsimp [negatives,T,broadTerminals,size]
    rw [he]
    change ([T 0,T 1]++[T 2,T 3]).Perm ([T 2,T 3]++[T 0,T 1])
    exact List.perm_append_comm
  · intro pkt hpkt i hi
    simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals exact good _ i hi
  · have he : (blocksWord (orderedPackets ps)).Perm (broadWord a b c d u) := by
      have hh := (((((((hperm 0).append_right [T 0]).append (hperm 1)).append_right [T 1]).append
        (hperm 2)).append_right [T 2]).append (hperm 3)).append_right [T 3]
      simpa [ps, orderedPackets, blocksWord, broadWord] using hh
    exact Multiset.coe_eq_coe.mpr (he.trans hp)
  · change finiteChecks (oldMass a b c d) f (N/2) 0 ps
    simp only [ps,finiteChecks,zero_add]
    change 0≤M 0+f (T 0) ∧ M 0≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1) ∧ M 0+f (T 0)+M 1≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3≤N/2 ∧ True
    have hAS : (Values.A V) - r * (Values.K V) = (Values.S V) - r * (Values.H V) := by
      dsimp [V,values]
      ring
    have p0 : M 0 + f (T 0) = (Values.D V) := m0
    have p1 : M 0 + f (T 0) + M 1 + f (T 1) =
        (Values.D V) + (Values.A V) - r * (Values.K V) := by linarith [m0,m1]
    have p1' : M 0 + f (T 0) + M 1 + f (T 1) =
        (Values.D V) + (Values.S V) - r * (Values.H V) := by linarith [p1,hAS]
    have p2 : M 0 + f (T 0) + M 1 + f (T 1) + M 2 + f (T 2) =
        (Values.E V) - (u : ℤ) * (Values.A V) := heold
    have p2m : M 0 + f (T 0) + M 1 + f (T 1) + M 2 =
        (Values.E V) - (u : ℤ) * (Values.A V) - f (T 2) := by linarith [p2]
    have p3 : M 0 + f (T 0) + M 1 + f (T 1) + M 2 + f (T 2) + M 3 + f (T 3) = 0 := zold
    constructor
    · linarith [m0, k0.1]
    constructor
    · linarith [m0, k0.2]
    constructor
    · linarith [p1', k1.1]
    constructor
    · linarith [p1', k1.2]
    constructor
    · linarith [p2, k2.1]
    constructor
    · linarith [p2m, k2.2]
    constructor
    · linarith [p3, lastO.1]
    constructor
    · linarith [p3, lastO.2]
    · trivial
  · change finiteEarChecks (newMass a b c d) g N (base a b c d 0) 0 1 ps
    rw [hbase]
    change finiteEarChecks (newMass a b c d) g N (Values.A V) 0 1 ps
    simp only [ps,finiteEarChecks,finiteChecks,zero_add]
    change 0≤newMass a b c d (B 0)+g (T 0) ∧ newMass a b c d (B 0)≤N ∧
      0≤newMass a b c d (B 0)+g (T 0)+(newMass a b c d (B 1)+(Values.A V))+g (T 1) ∧
      newMass a b c d (B 0)+g (T 0)+(newMass a b c d (B 1)+(Values.A V))≤N ∧
      0≤newMass a b c d (B 0)+g (T 0)+(newMass a b c d (B 1)+(Values.A V))+g (T 1)+newMass a b c d (B 2)+g (T 2) ∧
      newMass a b c d (B 0)+g (T 0)+(newMass a b c d (B 1)+(Values.A V))+g (T 1)+newMass a b c d (B 2)≤N ∧
      0≤newMass a b c d (B 0)+g (T 0)+(newMass a b c d (B 1)+(Values.A V))+g (T 1)+newMass a b c d (B 2)+g (T 2)+newMass a b c d (B 3)+g (T 3) ∧
      newMass a b c d (B 0)+g (T 0)+(newMass a b c d (B 1)+(Values.A V))+g (T 1)+newMass a b c d (B 2)+g (T 2)+newMass a b c d (B 3)≤N ∧ True
    have hASnew : 2 * (Values.A V) - r * (Values.SW V) = 2 * (Values.S V) - r * (Values.H V) := by
      dsimp [V,values]
      ring_nf
    have q0 : G 0 + g (T 0) = (Values.Dp V) := g0
    have q1 : G 0 + g (T 0) + G 1 + (Values.A V) + g (T 1) =
        (Values.Dp V) + 2 * (Values.S V) - r * (Values.H V) := by linarith [g0,g1,hASnew]
    have q1m : G 0 + g (T 0) + G 1 + (Values.A V) =
        (Values.Dp V) + 2 * (Values.S V) - r * (Values.H V) - g (T 1) := by linarith [q1]
    have q2 : G 0 + g (T 0) + G 1 + (Values.A V) + g (T 1) + G 2 + g (T 2) =
        (Values.F V) - 2 * (u : ℤ) * (Values.A V) := by linarith [henew]
    have q2m : G 0 + g (T 0) + G 1 + (Values.A V) + g (T 1) + G 2 =
        (Values.F V) - 2 * (u : ℤ) * (Values.A V) - g (T 2) := by linarith [q2]
    have q3 : G 0 + g (T 0) + G 1 + (Values.A V) + g (T 1) + G 2 + g (T 2) + G 3 + g (T 3) = 0 := by
      linarith [znew]
    constructor
    · linarith [g0, k0n.1]
    constructor
    · linarith [g0, k0n.2]
    constructor
    · linarith [q1, k1n.1]
    constructor
    · linarith [q1m, k1n.2]
    constructor
    · linarith [q2, k2n.1]
    constructor
    · linarith [q2m, k2n.2]
    constructor
    · linarith [q3]
    constructor
    · linarith [lastN.2]
    · trivial
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
