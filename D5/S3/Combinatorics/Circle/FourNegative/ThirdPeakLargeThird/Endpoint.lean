/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Endpoint
   generality: I
   mirror-B: none(source-only-unelaborated-draft)
   mirror-E: none(source-only-unelaborated-draft)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full specified large-third original-domain physical joint lift and every natural repeat/take. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Selection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! UNELABORATED SOURCE ONLY, kernel=false, official=false.
Scope is exactly 2≤b≤a<d and d+3≤c. This source unit asserts no closure of
the unchanged full Circle objective, adjacent c=d+1/2 faces, or d=a face.
The final theorem has no certificate, submask, or feasibility hypothesis. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open SourceWidth PeriodicShortening RunFirstEarTransport
open private selected_source from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Selection
open private actual_nat_joint_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private zero_period_transport from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- Every original tuple in the specified large-third domain has an old physical
order and a literal fresh-k ear. Each scalar coordinate has its own centered
strip for every natural repetition/take, and its own zero total. Source draft. -/
theorem actualSource_third_peak_large_third_joint_lift (a b c d : ℕ)
    (hb : 2≤b) (hba : b≤a) (had : a<d) (hdc : d+3≤c) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ,j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d+1)/2)) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  obtain ⟨sigma,j,hj,ho,hn⟩ :=
    (actual_nat_joint_iff a b c d (by omega) hb (by omega) (by omega)).mpr
      (selected_source a b c d hb hba had hdc)
  have old (m : ℕ):=zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have new (m : ℕ):=zero_period_transport _ _ (earWord (a+b+c+d) sigma j) hn.2.1 hn.2.2 m
  exact ⟨sigma,j,hj,ho,hn,fun m => (old m).2,fun m => (new m).2,
    fun m => ⟨(old m).1,(new m).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
