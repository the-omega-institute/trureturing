/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Endpoint
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Both unbounded original-source low-U physical joint lifts. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Constructors
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! Unbounded joint lifts for the two original low-U families.
The physical packet order is V,W,X,U and the fresh ear is in packet slot one,
after that packet's positive labels and before the W negative label.
The unrestricted Circle problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
open SourceWidth PeriodicShortening RunFirstEarTransport PacketNormalForm
open private construction_I_target construction_II_target
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Constructors
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

private theorem joint_of_certificate (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (cert : Nonempty (Certificate a b c d)) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))) (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈ Set.Icc (0 : ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈ Set.Icc (0 : ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  obtain ⟨sigma,j,hj,hold,hnew⟩ := (actual_four_packet_iff a b c d ha hb hc hd).mpr cert
  have eo (m : ℕ) := zero_period_transport _ _ sigma hold.2.1 hold.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord (a+b+c+d) sigma j) hnew.2.1 hnew.2.2 m
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    dsimp [modulus]
    rw [pow_succ]
    omega
  exact ⟨sigma,j,hj,hold,hnew,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

/-- Every original strict low-U source, including b+1=d. -/
theorem actualSource_third_peak_low_u_strict_joint_lift (a b c d : ℕ)
    (ha : 2≤a) (hab : a<b) (hbd : b<d) (hc : d+3≤c) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))) (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈ Set.Icc (0 : ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈ Set.Icc (0 : ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  exact joint_of_certificate a b c d ha (by omega) (by omega) (by omega)
    (construction_I_target a b c d ha hab hbd hc)

/-- Every original fallback source, including d=4. -/
theorem actualSource_third_peak_low_u_fallback_joint_lift (d : ℕ) (hd : 4≤d) :
    ∃ sigma : List (Fin (2+3+(d+2)+d)), ∃ j : ℕ, j≤2+3+(d+2)+d ∧
      OriginalOrder (2+3+(d+2)+d) (1+2^2+2^(2+3)+2^(2+3+(d+2))) sigma ∧
      OriginalOrder (2+3+(d+2)+d+1) (2*(1+2^2+2^(2+3)+2^(2+3+(d+2)))) (earWord (2+3+(d+2)+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (2+3+(d+2)+d) (1+2^2+2^(2+3)+2^(2+3+(d+2))))).sum ∈ Set.Icc (0 : ℤ) (modulus (2+3+(d+2)+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (2+3+(d+2)+d) sigma j)).flatten).take n).map
        (actualSource (2+3+(d+2)+d+1) (2*(1+2^2+2^(2+3)+2^(2+3+(d+2)))))).sum ∈ Set.Icc (0 : ℤ) (modulus (2+3+(d+2)+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map (actualSource (2+3+(d+2)+d) (1+2^2+2^(2+3)+2^(2+3+(d+2))))).sum=0 ∧
        (((List.replicate m (earWord (2+3+(d+2)+d) sigma j)).flatten).map
          (actualSource (2+3+(d+2)+d+1) (2*(1+2^2+2^(2+3)+2^(2+3+(d+2)))))).sum=0) := by
  exact joint_of_certificate 2 3 (d+2) d (by norm_num) (by norm_num) (by omega) (by omega)
    (construction_II_target d hd)

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
