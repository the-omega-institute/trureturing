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
open private seed sourceMod base oldValue newValue from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size)
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private theorem literal_orders (a b c d : ℕ)
    (ha : 3≤a) (hac : a<c) (hcd : c+2≤d) (hdb : d<b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  obtain ⟨v,m,M,before,hv0,hv,hM,hs,hw⟩ := physical_selection a b c d ha hac hcd hdb
  have construction := source_certificate a b c d (by omega) (by omega) (by omega) (by omega)
    v m M before hv0 hv hM hs hw
  have hp := banks_inventory a b c d (by omega) (by omega) (by omega) (by omega) v m M hs
  have hj : literalCut a b c d v m M before≤a+b+c+d := by
    have hh := hp.length_eq
    simp only [List.length_range] at hh
    change (word a b c d v m M).length=a+b+c+d at hh
    cases before
    · dsimp [literalCut]
      dsimp [word] at hh
      simp only [List.length_append,List.length_singleton] at hh
      omega
    · simp [literalCut]
  exact (actual_nat_joint_iff a b c d (by omega) (by omega) (by omega) (by omega)).mpr
    ⟨word a b c d v m M,hp,construction.2.1,
      literalCut a b c d v m M before,hj,construction.2.2⟩

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
  obtain ⟨sigma,j,hj,ho,hn⟩:=literal_orders a b c d ha hac hcd hdb
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
