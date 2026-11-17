/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Endpoint
   generality: I
   mirror-B: none(waiver:physical-dependent-source-registration-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original-label paid-low-V joint lift and all natural repeated scalar prefixes. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Allocation
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! Original-source joint lift for the paid-V region.
Scope: every 2≤a<b≤d<c, a+2≤d, c≤b+d-2. It does not close the full
third-peak cone or Circle J/C3.1. The seed and every occurrence are original. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
open SourceWidth PeriodicShortening RunFirstEarTransport
open private paidH paidEarly paid_source
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Allocation
open private word from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private freshCut from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.SourceCertificate
open private sourceMod from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base oldValue newValue)
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (insertAt)
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- The entire original paid-V subregion: the actual old source,
the actual doubled-seed new source, literal conditional ear, every natural
finite repeat/take, and the two separately zero scalar totals. -/
theorem actualSource_third_peak_paid_V_joint_lift (a b c d : ℕ)
    (ha : 2≤a) (hab : a<b) (hbd : b≤d) (hdc : d<c)
    (had : a+2≤d) (hupper : c≤b+d-2) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ,
      j=freshCut a b c d (paidH a b c d) (paidEarly a b c d) ∧ j<a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  have data:=paid_source a b c d ha hab hbd hdc had hupper
  let k:=a+b+c+d
  let AA:=1+2^a+2^(a+b)+2^(a+b+c)
  let l:=word a b c d (paidH a b c d)
  let j:=freshCut a b c d (paidH a b c d) (paidEarly a b c d)
  have hk : 0<k := by dsimp [k];omega
  have hp : l.Perm (List.range k) := data.2.1
  have hj : j<k := data.2.2.2.1
  have hmod : modulus k=sourceMod a b c d := by dsimp [modulus,k,sourceMod];ring
  have hmod' : modulus (k+1)=2*sourceMod a b c d+1 := by dsimp [modulus,k,sourceMod];ring
  have hhalf : (2*sourceMod a b c d+1)/2=sourceMod a b c d := by omega
  have hseed : (AA:ℤ)=base a b c d 0 := by
    dsimp [AA]
    push_cast
    dsimp [base]
    ring
  have hseed' : ((2*AA:ℕ):ℤ)=2*base a b c d 0 := by push_cast;rw [hseed]
  let sigma:=l.map (label k hk)
  have ho : OriginalOrder k AA sigma := by
    apply lift_order k AA hk l hp
    · rw [hmod,hseed]
      change InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 l
      exact data.2.2.1
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k AA (by dsimp [k];omega)
  let pre:=l.take j
  let post:=l.drop j
  have heword : pre++post=l := List.take_append_drop j l
  have hpre : pre.length=j := by
    have hl:=hp.length_eq
    simp only [List.length_range] at hl
    simp [pre,List.length_take,Nat.min_eq_left (by omega : j≤l.length)]
  have hp' : (pre++k::post).Perm (List.range (k+1)) := by
    have hreorder : (pre++k::post).Perm (l++[k]) := by
      rw [←heword]
      simpa [List.append_assoc] using (List.perm_append_singleton k post).symm.append_left pre
    exact hreorder.trans (by simpa [List.range_succ] using hp.append_right [k])
  have hnew : OriginalOrder (k+1) (2*AA)
      ((pre++k::post).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*AA) (by omega) (pre++k::post) hp'
    · rw [hmod',hseed',hhalf]
      change InStrip (newValue a b c d) (sourceMod a b c d) 0
        (insertAt (size a b c d) l j)
      exact data.2.2.2.2
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*AA) (by dsimp [k];omega)
  have hn : OriginalOrder (k+1) (2*AA) (earWord k sigma j) := by
    dsimp [sigma]
    rw [←heword]
    rw [marked_word k j hk pre post hpre (by simpa [heword] using hp)]
    exact hnew
  have eo (m : ℕ):=zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ):=zero_period_transport _ _ (earWord k sigma j) hn.2.1 hn.2.2 m
  have half : modulus (k+1)/2=modulus k := by
    have he : (2:ℤ)^(k+1)=2*(2:ℤ)^k := by rw [pow_succ];ring
    dsimp [modulus]
    rw [he]
    omega
  exact ⟨sigma,j,rfl,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
