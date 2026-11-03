/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Endpoint
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original four-bit joint lift on the full approved union, with literal cut and all natural takes. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Parameters

/-! Full HighD physical endpoint with natural repetitions and takes. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private physical_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Parameters
open private source_certificate literalCut
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SourceCertificate
open private word banks banks_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Banks
open private size seed sourceMod base oldValue newValue
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

private theorem literal_orders (a b c d : ℕ)
    (ha : 3≤a) (hac : a<c) (hcd : c+2≤d) (hdb : d<b) :
    ∃ v m M : ℕ, ∃ before : Bool, ∃ sigma : List (Fin (a+b+c+d)),
      let j:=literalCut a b c d v m M before
      j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  obtain ⟨v,m,M,before,hv0,hv,hM,hs,hw⟩:=physical_selection a b c d ha hac hcd hdb
  have construction:=source_certificate a b c d (by omega) (by omega) (by omega) (by omega)
    v m M before hv0 hv hM hs hw
  have hold:=construction.2.1
  have hnew:=construction.2.2
  let k:=a+b+c+d
  let AA:=1+2^a+2^(a+b)+2^(a+b+c)
  let l:=word a b c d v m M
  let j:=literalCut a b c d v m M before
  have hk : 0<k := by dsimp [k]; omega
  have hp : l.Perm (List.range k) := banks_inventory a b c d (by omega) (by omega) (by omega) (by omega) v m M hs
  have hj : j≤k := by
    have hh:=hp.length_eq
    simp only [List.length_range] at hh
    cases before
    · dsimp [j,literalCut]
      dsimp [l,word] at hh
      simp only [List.length_append,List.length_singleton] at hh
      omega
    · simp [j,literalCut]
  have hmod : modulus k=sourceMod a b c d := by dsimp [k,modulus,sourceMod]; ring
  have hmod' : modulus (k+1)=2*sourceMod a b c d+1 := by dsimp [k,modulus,sourceMod]; ring
  have hhalf : (2*sourceMod a b c d+1)/2=sourceMod a b c d := by omega
  have hseed : (AA:ℤ)=base a b c d 0 := by dsimp [AA,base]; push_cast; ring
  have hseed' : ((2*AA:ℕ):ℤ)=2*base a b c d 0 := by push_cast; rw [hseed]
  have ho : OriginalOrder k AA (l.map (label k hk)) := by
    apply lift_order k AA hk l hp
    · simpa only [hmod,hseed,oldValue] using hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k AA (by dsimp [k]; omega)
  let pre:=l.take j
  let post:=l.drop j
  have heword : pre++post=l := List.take_append_drop j l
  have hprelen : pre.length=j := by
    have hh:=hp.length_eq
    simp only [List.length_range] at hh
    simp [pre,List.length_take,Nat.min_eq_left (by omega : j≤l.length)]
  have hp' : (pre++k::post).Perm (List.range (k+1)) := by
    have hreorder : (pre++k::post).Perm (l++[k]) := by
      rw [←heword]
      simpa [List.append_assoc] using (List.perm_append_singleton k post).symm.append_left pre
    exact hreorder.trans (by simpa [List.range_succ] using hp.append_right [k])
  have hn : OriginalOrder (k+1) (2*AA)
      ((pre++k::post).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*AA) (by omega) (pre++k::post) hp'
    · simpa only [hmod',hseed',hhalf,insertAt,pre,post,newValue] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*AA) (by dsimp [k]; omega)
  have marked : OriginalOrder (k+1) (2*AA) (earWord k (l.map (label k hk)) j) := by
    rw [←heword]
    rw [marked_word k j hk pre post hprelen (by simpa [heword] using hp)]
    exact hn
  exact ⟨v,m,M,before,l.map (label k hk),hj,ho,marked⟩

def JointLift (a b c d : ℕ) (sigma : List (Fin (a+b+c+d))) (j : ℕ) : Prop :=
    j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ r n : ℕ, ((((List.replicate r sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ r n : ℕ, ((((List.replicate r (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ r : ℕ,
        (((List.replicate r sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate r (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0)

/-- Full physical domain: every 3<=a<c, c+2<=d and d<b.
The proof builds literal cut0 or the cut immediately after nX, and transports
both separately zero periods to every natural repetition and every natural take. -/
theorem actualSource_second_peak_high_d_joint_lift (a b c d : ℕ)
    (ha : 3≤a) (hac : a<c) (hcd : c+2≤d) (hdb : d<b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, JointLift a b c d sigma j := by
  obtain ⟨v,m,M,before,sigma,hj,ho,hn⟩:=literal_orders a b c d ha hac hcd hdb
  let j:=literalCut a b c d v m M before
  have eo (r : ℕ):=zero_period_transport _ _ sigma ho.2.1 ho.2.2 r
  have en (r : ℕ):=zero_period_transport _ _ (earWord (a+b+c+d) sigma j) hn.2.1 hn.2.2 r
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    have hp : (2:ℤ)^(a+b+c+d+1)=2*(2:ℤ)^(a+b+c+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun r => (eo r).2,
    fun r n => by simpa only [half] using (en r).2 n,
    fun r => ⟨(eo r).1,(en r).1⟩⟩

#print axioms actualSource_second_peak_high_d_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
