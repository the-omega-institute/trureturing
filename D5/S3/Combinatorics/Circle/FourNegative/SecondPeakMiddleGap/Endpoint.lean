/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete two-route physical joint lift for every independent 2<=d<c<a<=b. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Certificate

/-! The unrestricted Circle J and C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open private certificate_exists
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Certificate
open private strip_of_prefix
  from D5.S3.Combinatorics.Circle.PeriodicShortening

private theorem zero_period_transport {α : Type*} (f : α→ℤ) (C : ℤ) (l : List α)
    (hz : (l.map f).sum=0)
    (hp : ∀ n : ℕ, ((l.take n).map f).sum∈Set.Icc (0:ℤ) C) (m : ℕ) :
    (((List.replicate m l).flatten).map f).sum=0 ∧
    (∀ n : ℕ, ((((List.replicate m l).flatten).take n).map f).sum∈Set.Icc (0:ℤ) C) := by
  have hC : 0≤C := by simpa using (hp 0).2
  have hs : InStrip f C 0 l := strip_of_prefix f C 0 l (by simpa using hp)
  have hr (m : ℕ) : (((List.replicate m l).flatten).map f).sum=0 ∧
      InStrip f C 0 (List.replicate m l).flatten := by
    induction m with
    | zero => simp [InStrip,hC]
    | succ m ih =>
      simp only [List.replicate_succ,List.flatten_cons]
      exact ⟨by simp [List.map_append,List.sum_append,hz,ih.1],
        inStrip_append hs (by simpa only [hz,zero_add] using ih.2)⟩
  exact ⟨(hr m).1,fun n => by simpa only [zero_add,Set.mem_Icc] using inStrip_prefix (hr m).2 n⟩

/-- One old physical permutation, one literal fresh insertion, both complete orders,
all natural repeated prefixes and zero totals for every finite repetition. -/
theorem actualSource_second_peak_middle_gap_joint_lift (a b c d : ℕ)
    (hd : 2≤d) (hdc : d<c) (hca : c<a) (hab : a≤b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
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
  obtain ⟨sigma,j,hj,ho,hn⟩ :=
    (PacketNormalForm.actual_four_packet_iff a b c d (by omega) (by omega) (by omega) hd).mpr
      (certificate_exists a b c d hd hdc hca hab)
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord (a+b+c+d) sigma j) hn.2.1 hn.2.2 m
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    have hp : (2:ℤ)^(a+b+c+d+1)=2*(2:ℤ)^(a+b+c+d) := by rw [pow_succ];ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

#print axioms actualSource_second_peak_middle_gap_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap
