/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Endpoint
   generality: I
   mirror-B: none(waiver:original-eight-binder-source-family)
   mirror-E: none(waiver:actual-source-dependent-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full original intermediate-tail joint lift, literal cut and every repeated prefix. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! The full original intermediate-tail joint lift for every 2≤a≤d<b<c.
Unrestricted four-gap joint lifting and Circle/J/C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
open SourceWidth PeriodicShortening RunFirstEarTransport
open private route word before after freshCut literal_cut
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Masks
open private physical_source
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Physical
open private size sourceMod base oldValue newValue source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- All original 2≤a≤d<b<c, without a feasibility premise or exponent bound:
one actual permutation, the literal early/late ear, both complete orders,
every natural replicate/take bound, and two independent repeated zero totals. -/
theorem actualSource_third_peak_intermediate_tail_joint_lift (a b c d : ℕ)
    (ha : 2≤a) (had : a≤d) (hdb : d<b) (hbc : b<c) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ,
      j=freshCut a b d ∧ j<a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  let k:=a+b+c+d
  let AA:=1+2^a+2^(a+b)+2^(a+b+c)
  let mode:=route a b d
  let pre:=before mode a b c d
  let post:=after mode a b c d
  let j:=freshCut a b d
  have hk : 0<k := by dsimp [k]; omega
  have data:=physical_source a b c d ha had hdb hbc
  have hword : word mode a b c d=pre++post := by
    dsimp [pre,post,before,after,word]
    split_ifs <;> simp [List.append_assoc]
  have hp : (pre++post).Perm (List.range k) := by rw [←hword]; exact data.1
  have hlen : pre.length=j := data.2.1
  have hj : j<k := data.2.2.1
  have hseed : (AA:ℤ)=base a b c d 0 := by
    dsimp [AA]
    push_cast
    dsimp [base]
    simp only [pow_add]
    ring
  have hmod : modulus k=sourceMod a b c d := by
    dsimp [modulus,k,sourceMod]
    simp only [pow_add]
  have hmod' : modulus (k+1)=2*sourceMod a b c d+1 := by
    dsimp only [modulus]
    rw [pow_succ]
    have hm:=hmod
    dsimp only [modulus] at hm
    omega
  have hhalf : (2*sourceMod a b c d+1)/2=sourceMod a b c d := by omega
  have holdstrip : InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (pre++post) := by
    rw [←hword]
    exact data.2.2.2.1
  have hnewstrip : InStrip (newValue a b c d) (sourceMod a b c d) 0 (pre++k::post) := by
    have hn:=data.2.2.2.2
    rw [hword] at hn
    change InStrip (newValue a b c d) (sourceMod a b c d) 0 (insertAt k (pre++post) j) at hn
    simpa only [insertAt,←hlen,List.take_append_of_le_length (le_refl pre.length),
      List.drop_append_of_le_length (le_refl pre.length),List.take_length,List.drop_length,
      Nat.sub_self,List.drop_zero,List.nil_append] using hn
  -- Native independent totals precede any zero-period transport.
  have totals:=source_totals a b c d ha (by omega) (by omega) (by omega)
  have zeroOld : ((List.range k).map
      (fun i => centered (modulus k) ((2:ℤ)^i*AA))).sum=0 := by
    rw [hmod,hseed]
    exact totals.1
  have zeroNew : ((List.range (k+1)).map
      (fun i => centered (modulus (k+1)) ((2:ℤ)^i*(2*AA:ℕ)))).sum=0 := by
    rw [hmod']
    simp only [Nat.cast_mul,Nat.cast_ofNat,hseed]
    change ((List.range (k+1)).map (newValue a b c d)).sum=0
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    change ((List.range (size a b c d)).map (newValue a b c d)).sum+newValue a b c d (size a b c d)=0
    rw [totals.2.1,totals.2.2]
    omega
  let sigma:=(pre++post).map (label k hk)
  have old : OriginalOrder k AA sigma := by
    apply lift_order k AA hk (pre++post) hp
    · rw [hmod,hseed]
      exact holdstrip
    · exact zeroOld
  have newperm : (pre++k::post).Perm (List.range (k+1)) := by
    have hr : (pre++k::post).Perm ((pre++post)++[k]) := by
      simpa only [List.append_assoc] using
        (List.perm_append_singleton k post).symm.append_left pre
    exact hr.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have new : OriginalOrder (k+1) (2*AA)
      ((pre++k::post).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*AA) (by omega) (pre++k::post) newperm
    · rw [hmod']
      simp only [Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf]
      exact hnewstrip
    · exact zeroNew
  have enlarged : OriginalOrder (k+1) (2*AA) (earWord k sigma j) := by
    change OriginalOrder (k+1) (2*AA) (earWord k ((pre++post).map (label k hk)) j)
    rw [marked_word k j hk pre post hlen hp]
    exact new
  have eo (m : ℕ):=zero_period_transport _ _ sigma old.2.1 old.2.2 m
  have en (m : ℕ):=zero_period_transport _ _ (earWord k sigma j) enlarged.2.1 enlarged.2.2 m
  have half : modulus (k+1)/2=modulus k := by rw [hmod',hhalf,hmod]
  exact ⟨sigma,j,rfl,hj,old,enlarged,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

#print axioms actualSource_third_peak_intermediate_tail_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
