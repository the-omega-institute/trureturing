/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllEndpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllEndpoint
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded a2 second peak AllEndpoint construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.AllSelection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Physical

/-! Full original a=2 endpoint at every b>d.
The unrestricted Circle statement is unchanged and remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SourceWidth PeriodicShortening RunFirstEarTransport
open private dyadic_allh_good from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.AllSelection
open private physical_order
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Physical
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- Exact exponent transport into the existing physical consumer. Every actual
label and the literal fresh insertion are inherited from that consumer. -/
private theorem complete_original_orders_all_h (b c d : ℕ)
    (hc : 3≤c) (hd : c+2≤d) (hb : d<b) :
    ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧
      OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧
      OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))
        (earWord (2+b+c+d) sigma j) := by
  let p : ℕ := 2^(d-c)
  let q : ℕ := 2^(c-2)
  let h : ℕ := 2^(b-d-1)
  have hce : c=2+(c-2) := by omega
  have hde : d=c+(d-c) := by omega
  have hbe : b=d+1+(b-d-1) := by omega
  have hqc : (2:ℤ)^c=4*(q:ℤ) := by
    calc
      (2:ℤ)^c = (2:ℤ)^(2+(c-2)) := congrArg (fun e : ℕ => (2:ℤ)^e) hce
      _ = 4*(q:ℤ) := by rw [pow_add]; norm_num [q]
  have hpc : (2:ℤ)^d=4*(p:ℤ)*q := by
    calc
      (2:ℤ)^d = (2:ℤ)^(c+(d-c)) := congrArg (fun e : ℕ => (2:ℤ)^e) hde
      _ = 4*(p:ℤ)*q := by
        rw [pow_add,hqc]
        simp only [p,Nat.cast_pow,Nat.cast_ofNat]
        ring
  have hbc : (2:ℤ)^b=8*(h:ℤ)*p*q := by
    calc
      (2:ℤ)^b = (2:ℤ)^(d+1+(b-d-1)) := congrArg (fun e : ℕ => (2:ℤ)^e) hbe
      _ = (2:ℤ)^d*2*(2:ℤ)^(b-d-1) := by rw [pow_add,pow_succ]
      _ = 8*(h:ℤ)*p*q := by
        rw [hpc]
        simp only [h,Nat.cast_pow,Nat.cast_ofNat]
        ring
  obtain ⟨v,m,M,before,hgood⟩ :=
    dyadic_allh_good (d-c) (c-2) (b-d-1) (by omega) (by omega)
  exact physical_order b c d p q h v m M before
    (by omega) (by omega) (by omega) hqc hpc hbc hgood

/-- Full original-source a=2 joint lift at every natural b>d, with both complete
orders, arbitrary natural repetitions/takes, and separate old/new zero totals. -/
theorem actualSource_second_peak_a2_all_h_joint_lift (b c d : ℕ)
    (hc : 3≤c) (hd : c+2≤d) (hb : d<b) :
    ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧
      OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧
      OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))
        (earWord (2+b+c+d) sigma j) ∧
      (∀ r n : ℕ, ((((List.replicate r sigma).flatten).take n).map
        (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (2+b+c+d)/2)) ∧
      (∀ r n : ℕ, ((((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).take n).map
        (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (2+b+c+d))) ∧
      (∀ r : ℕ,
        (((List.replicate r sigma).flatten).map
          (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum=0 ∧
        (((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).map
          (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum=0) := by
  obtain ⟨sigma,j,hj,ho,hn⟩ := complete_original_orders_all_h b c d hc hd hb
  have eo (r : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 r
  have en (r : ℕ) := zero_period_transport _ _ (earWord (2+b+c+d) sigma j) hn.2.1 hn.2.2 r
  have half : modulus (2+b+c+d+1)/2=modulus (2+b+c+d) := by
    have hp : (2:ℤ)^(2+b+c+d+1)=2*(2:ℤ)^(2+b+c+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,fun r => (eo r).2,
    fun r n => by simpa only [half] using (en r).2 n,
    fun r => ⟨(eo r).1,(en r).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
