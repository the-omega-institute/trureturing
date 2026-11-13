/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Boundary
   generality: I
   mirror-B: none(waiver:consumed-boundary-lemmas)
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Ascending physical orders on the one-negative and exactly periodic boundary. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Arithmetic
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
import D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Source

/-! The one-negative and periodic boundaries retain literal ascending labels. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private ear_prefix ear_perm
  from D5.S3.Combinatorics.Circle.RunFirstEarTransport
open private seed_bound long_charge_zero native_pair native_fresh
  from D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Arithmetic
open private old_value list_prefix_strip prefix_nonneg_le
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
    exact ⟨hh, by omega, ih (h+f x) hxs (by omega) (by omega)⟩

private theorem natural_source_total (k t : ℕ) (hk : 0 < k) :
    ((List.range k).map (fun i => centered (modulus k) ((2 : ℤ)^i*t))).sum = 0 := by
  have h := (ZeroSumSubsets.source_cycle hk t).2.1
  change (∑ i : Fin k, centered (modulus k) ((2 : ℤ)^i.val*t))=0 at h
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => centered (modulus k) ((2:ℤ)^i*t)) k] at h
  rw [←List.sum_toFinset _ List.nodup_range,List.toFinset_range]
  exact h

private theorem range_labels (k : ℕ) (hk : 0 < k) :
    (List.range k).map (label k hk) = List.finRange k := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    apply Fin.ext
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, label]
    exact Nat.mod_eq_of_lt (by simpa using hi)

set_option maxHeartbeats 4000000 in
-- Both complete native inventories and all-prefix checks are elaborated together.
/-- The unit seed has one final negative; the fresh physical label follows every
old positive and precedes that negative. This is consumed by the p=1 branch. -/
private theorem ascending_unit (k : ℕ) (hk : 2 ≤ k) :
    OriginalOrder k 1 (List.finRange k) ∧
    OriginalOrder (k+1) 2 (earWord k (List.finRange k) (k-1)) := by
  let B : ℤ := 2^(k-1)
  let f := fun i : ℕ => centered (modulus k) ((2 : ℤ)^i*1)
  let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*2)
  let P := List.range (k-1)
  have hB : 1 ≤ B := by dsimp [B];exact one_le_pow₀ (by norm_num)
  have hpowk : (2:ℤ)^k=2*B := by
    dsimp [B]
    calc (2:ℤ)^k=2^((k-1)+1) := by congr 1;omega
         _ = 2*2^(k-1) := by rw [pow_succ];ring
  have hN : modulus k = 2*B-1 := by rw [modulus,hpowk]
  have hN' : modulus (k+1)=4*B-1 := by rw [modulus,pow_succ,hpowk];ring
  have hfhalf : modulus k / 2 = B-1 := by rw [hN]; omega
  have hghalf : modulus (k+1) / 2 = 2*B-1 := by rw [hN']; omega
  have hf (i : ℕ) (hi : i<k-1) : f i=(2:ℤ)^i := by
    obtain ⟨hpos,hodd⟩ := TwoRunSource.modulus_positive_odd k (by omega)
    have hpow : (2:ℤ)^i < B := by
      dsimp [B]
      exact pow_lt_pow_right₀ (by norm_num) hi
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      (by
        rw [hfhalf]
        have h0 : (0:ℤ) ≤ 2^i := by positivity
        constructor <;> omega)
    simp only [centered_mod, mul_one]
  have hg (i : ℕ) (hi : i<k-1) : g i=2*(2:ℤ)^i := by
    obtain ⟨hpos,hodd⟩ := TwoRunSource.modulus_positive_odd (k+1) (by omega)
    have hpow : (2:ℤ)^i < B := by
      dsimp [B]
      exact pow_lt_pow_right₀ (by norm_num) hi
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      (by
        rw [hghalf]
        have h0 : (0:ℤ) ≤ 2^i := by positivity
        constructor <;> omega)
    rw [centered_mod]; congr 1; ring
  have hfresh : g k=1 := by
    dsimp [g]
    have he : (2:ℤ)^k*2=(2:ℤ)^(k+1)*1 := by rw [pow_succ]; ring
    rw [he]
    rw [show centered (modulus (k+1)) ((2:ℤ)^(k+1)*1)=centered (modulus (k+1)) (1:ℤ) by
      simpa using centered_full_period (k+1) 1]
    obtain ⟨hpos,hodd⟩ := TwoRunSource.modulus_positive_odd (k+1) (by omega)
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      (by rw [hghalf]; omega)
    exact centered_mod _ _
  have hPsum : (P.map f).sum = B-1 := by
    simpa [P,B,List.range_eq_range'] using ladder_sum f 0 (k-1) 1 (by
      intro i hi; simpa using hf i hi)
  have hPsum' : (P.map g).sum=2*(B-1) := by
    have h := ladder_sum g 0 (k-1) 2 (by
      intro i hi; simpa [mul_comm] using hg i hi)
    simpa [P,B,mul_comm,List.range_eq_range'] using h
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
    simp only [hPsum,InStrip,hnegative]
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
    simpa only [List.append_assoc,List.singleton_append] using
      (List.Perm.swap (k-1) k []).append_left P
  have hold := lift_order k 1 (by omega) (List.range k) (List.Perm.refl _)
    holdstrip (natural_source_total k 1 (by omega))
  have hnew := lift_order (k+1) 2 (by omega) (P++[k,k-1]) hnewperm
    hnewstrip (natural_source_total (k+1) 2 (by omega))
  have hearmark := marked_word k (k-1) (by omega) P [k-1]
    (by simp [P]) (by rw [hword])
  rw [hword,range_labels] at hearmark
  rw [← hearmark] at hnew
  simpa only [range_labels] using And.intro hold hnew

private theorem ascending_blocks (a p : ℕ) :
    (List.range p).flatMap (fun j => List.range' (j*a) a) = List.range (a*p) := by
  induction p with
  | zero => simp
  | succ p ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,Nat.mul_succ]
    simp only [List.range_eq_range']
    simpa only [Nat.zero_add,Nat.mul_comm] using
      List.range'_append_1 (s:=0) (m:=a*p) (n:=a)

set_option maxHeartbeats 4000000 in
-- The arbitrary block-count induction is checked with both native coordinates.
/-- On the exactly periodic boundary the literal ascending physical word has
sharp old height E(2^(a-1)-1); one native charge accounts for every doubled
coordinate, with the fresh occurrence inserted after the first positive run. -/
private theorem periodic_ascending (a p : ℕ) (ha : 2 ≤ a) (hp : 2 ≤ p) :
    OriginalOrder (a*p) (geom a p) (List.finRange (a*p)) ∧
    OriginalOrder (a*p+1) (2*geom a p)
      (earWord (a*p) (List.finRange (a*p)) (a-1)) := by
  let k := a*p
  let E := geom a p
  let J : ℤ := modulus a / 2
  let f := fun i : ℕ => centered (modulus k) ((2 : ℤ)^i*E)
  let v := actualSource k E
  let c := charge k E
  let sigma := List.finRange k
  have hk : 2 ≤ k := by dsimp [k]; nlinarith
  have hE : 0 ≤ (E:ℤ) := Int.natCast_nonneg E
  have hbase := (ascending_unit a ha).1
  have hbase_strip : InStrip (actualSource a 1) J 0 (List.finRange a) := by
    apply list_prefix_strip
    intro n
    simpa only [zero_add,J,Set.mem_Icc] using hbase.2.2 n
  have hpowa : (2:ℤ)^a=2*2^(a-1) := by
    calc (2:ℤ)^a=2^((a-1)+1) := by congr 1;omega
         _ = 2*2^(a-1) := by rw [pow_succ];ring
  have hJ : J=(2:ℤ)^(a-1)-1 := by
    dsimp [J,modulus]
    rw [hpowa]
    omega
  have hJ0 : 0 ≤ J := by rw [hJ];have := (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2) (n:=a-1));omega
  have hone : 1 ≤ 2^(a-1)-1 := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (show 1 ≤ a-1 by omega)
    norm_num at h
    omega
  have hrow (j : ℕ) (hj : j<p) :
      InStrip f ((E:ℤ)*J) 0 (List.range' (j*a) a) ∧
      ((List.range' (j*a) a).map f).sum=0 := by
    let theta := fun i : Fin a => j*a+i.val
    have hval (i : Fin a) : f (theta i)=(E:ℤ)*actualSource a 1 i := by
      have h := old_value a p 1 ha hp hone (⟨j,hj⟩:Fin p) i
      simpa only [f,k,E,theta,PhysicalJointRepetition.blockLabel,actualSource,one_mul]
        using h
    have hlist : (List.finRange a).map theta=List.range' (j*a) a := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map,List.getElem_finRange,List.getElem_range',theta,
          Fin.val_cast,Nat.one_mul]
    have hs := ThreeRowSource.scale_strip (actualSource a 1) f theta (E:ℤ) J
      ((E:ℤ)*J) 0 hE le_rfl (List.finRange a) (fun i _ => hval i) hbase_strip
    have hm := ThreeRowSource.scaled_sum (actualSource a 1) f theta (E:ℤ)
      (List.finRange a) (fun i _ => hval i)
    rw [hlist] at hs hm
    simp only [mul_zero] at hs
    rw [hbase.2.1,mul_zero] at hm
    exact ⟨hs,hm⟩
  have hblocks (q : ℕ) (hq : q ≤ p) :
      InStrip f ((E:ℤ)*J) 0 ((List.range q).flatMap (fun j => List.range' (j*a) a)) ∧
      (((List.range q).flatMap (fun j => List.range' (j*a) a)).map f).sum=0 := by
    induction q with
    | zero =>
      simp only [List.range_zero,List.flatMap_nil,List.map_nil,List.sum_nil,and_true]
      exact ⟨by omega,mul_nonneg hE hJ0⟩
    | succ q ih =>
      have hq' : q ≤ p := by omega
      obtain ⟨hs,hm⟩ := ih hq'
      obtain ⟨ht,hn⟩ := hrow q (by omega)
      simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,
        List.map_append,List.sum_append]
      refine ⟨inStrip_append hs ?_,by rw [hm,hn];ring⟩
      simpa only [hm,zero_add] using ht
  have hsharp : InStrip f ((E:ℤ)*J) 0 (List.range k) := by
    simpa only [ascending_blocks,k] using (hblocks p le_rfl).1
  have hwidth : width a p a=k := by
    dsimp [width,k]
    have he : p=(p-1)+1 := by omega
    conv_rhs => rw [he,Nat.mul_add]
    omega
  have hpair := fun i : Fin (width a p a) => native_pair a p a ha (by omega) le_rfl i
  rw [hwidth] at hpair
  have hc0 (i : Fin k) : 0 ≤ c i := (hpair i).1
  have htotc : (sigma.map c).sum=(E:ℤ) := by
    dsimp [sigma,c]
    rw [←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
    exact charge_sum k E hk (by
      have h := seed_bound a p a ha (by omega) le_rfl
      simpa only [hwidth,E] using h)
  have hcprefix (n : ℕ) : 0 ≤ ((sigma.take n).map c).sum ∧
      ((sigma.take n).map c).sum ≤ (E:ℤ) := by
    have h := prefix_nonneg_le sigma c (fun i _ => hc0 i) n
    rwa [htotc] at h
  have hcharge_early (n : ℕ) (hn : n ≤ a-1) : ((sigma.take n).map c).sum=0 := by
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    have hi' : i.val<n := by
      have h := (List.mem_take_iff_idxOf_lt (by simp : i∈List.finRange k)).mp hi
      simpa only [List.idxOf_finRange] using h
    have h := long_charge_zero a p a ha (by omega) le_rfl
    rw [hwidth] at h
    exact h i (by omega)
  have hprefix_eq (n : ℕ) : ((sigma.take n).map v).sum=
      (((List.range k).take n).map f).sum := by
    dsimp [sigma]
    rw [←range_labels k (by omega),←List.map_take,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' : i<k := List.mem_range.mp (List.mem_of_mem_take hi)
    simp only [Function.comp_def,v,actualSource,label,Nat.mod_eq_of_lt hi',f]
  have hprefix (n : ℕ) : 0 ≤ ((sigma.take n).map v).sum ∧
      ((sigma.take n).map v).sum ≤ (E:ℤ)*J := by
    rw [hprefix_eq]
    simpa only [zero_add] using inStrip_prefix hsharp n
  have hN : modulus k=(2*J+1)*(E:ℤ) := by
    have h := geom_mul a p (by omega)
    rw [←pow_mul] at h
    have he : (2:ℤ)^a-1=2*J+1 := by
      rw [hJ,hpowa]
      ring
    simpa only [k,E,modulus,he] using h.symm
  have hcap : (E:ℤ)*J ≤ modulus k/2 := by
    apply (Int.le_ediv_iff_mul_le (by norm_num : (0:ℤ)<2)).2
    rw [hN]
    nlinarith
  have h_old : OriginalOrder k E sigma := by
    refine ⟨List.Perm.refl _,?_,?_⟩
    · dsimp [sigma]
      rw [←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
      exact (ZeroSumSubsets.source_cycle (by omega) E).2.1
    · intro n
      exact ⟨(hprefix n).1,le_trans (hprefix n).2 hcap⟩
  have hfresh := native_fresh a p a ha (by omega) le_rfl
  rw [hwidth] at hfresh
  have hnewhalf : modulus (k+1)/2=modulus k := by
    dsimp [modulus]
    rw [pow_succ]
    omega
  have hnewprefix (n : ℕ) :
      (((earWord k sigma (a-1)).take n).map (actualSource (k+1) (2*E))).sum =
      2*((sigma.take (if n ≤ a-1 then n else n-1)).map v).sum -
      ((sigma.take (if n ≤ a-1 then n else n-1)).map c).sum +
      (if n ≤ a-1 then 0 else (E:ℤ)) := by
    rw [ear_prefix k sigma (a-1) (by dsimp [sigma];simp;dsimp [k];nlinarith)]
    have he : (fun i : Fin k => actualSource (k+1) (2*E) i.castSucc)=
        (fun i => 2*v i-c i) := by
      funext i
      exact (hpair i).2.2
    simp only [he,hfresh,sub_eq_add_neg,List.sum_map_add,List.sum_map_mul_left]
    congr 2
    simpa only [List.map_map,Function.comp_def] using
      (List.sum_neg ((sigma.take (if n ≤ a-1 then n else n-1)).map c)).symm
  have hnewperm := ear_perm k sigma (a-1) h_old.1
  refine ⟨h_old,hnewperm,?_,?_⟩
  · rw [(hnewperm.map (actualSource (k+1) (2*E))).sum_eq]
    rw [←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by omega) (2*E)).2.1
  · intro n
    rw [hnewprefix,hnewhalf,hN]
    by_cases hn : n ≤ a-1
    · simp only [hn,ite_true,hcharge_early n hn,sub_zero,add_zero]
      have h := hprefix n
      constructor <;> nlinarith
    · simp only [hn,ite_false]
      have h := hprefix (n-1)
      have hc := hcprefix (n-1)
      constructor <;> nlinarith

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
