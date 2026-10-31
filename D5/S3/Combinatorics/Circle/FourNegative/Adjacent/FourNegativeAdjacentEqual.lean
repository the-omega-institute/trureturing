/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentEqual
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentEqual
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical repetition and a narrow old strip give the diagonal paired-gap joint order. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoublePhysical
import D5.S3.Combinatorics.Circle.ThreeRowSource

/-! A literal first ear for the diagonal, retaining every repeated physical occurrence. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentEqual
open SourceWidth PeriodicShortening RunFirstEarTransport PeriodicShorteningArithmetic
open private ear_prefix ear_perm from D5.S3.Combinatorics.Circle.RunFirstEarTransport
open private prefix_nonneg_le sum_linear from D5.S3.Combinatorics.Circle.PeriodicShortening
open private centered_ladder positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource
open private ladder_sum label lift_order from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem first_ear (k t : ℕ) (hk : 2≤k)
    (ht : t≤2^(k-1)-1) (sigma : List (Fin k))
    (hp : sigma.Perm (List.finRange k))
    (hz : (sigma.map (actualSource k t)).sum=0)
    (H : ℤ) (hwidth : ∀ n, ((sigma.take n).map (actualSource k t)).sum ∈ Set.Icc (0 : ℤ) H)
    (hcap : 2*H+t≤modulus k) :
    OriginalOrder k t sigma ∧ OriginalOrder (k+1) (2*t) (earWord k sigma 0) := by
  have htZ : (t : ℤ)≤(2 : ℤ)^(k-1)-1 := by exact_mod_cast ht
  have hpow : (2 : ℤ)^k=2*2^(k-1) := by
    conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
    ring
  have hNpos : 0<modulus k := (TwoRunSource.modulus_positive_odd k (by omega)).1
  have hNNpos : 0<modulus (k+1) := (TwoRunSource.modulus_positive_odd (k+1) (by omega)).1
  have hNNo : modulus (k+1)%2=1 := (TwoRunSource.modulus_positive_odd (k+1) (by omega)).2
  have hNN : modulus (k+1)=2*modulus k+1 := by dsimp [modulus]; rw [pow_succ]; ring
  have hcharge (i : Fin k) := digit_data k t hk ht i
  have hnonneg (i : Fin k) : 0≤charge k t i := (hcharge i).1
  have hsum : (sigma.map (charge k t)).sum=t := by
    rw [(hp.map (charge k t)).sum_eq]
    simpa only [List.sum_ofFn,List.map_finRange] using charge_sum k t hk ht
  have hsource (i : Fin k) : actualSource (k+1) (2*t) i.castSucc =
      2*actualSource k t i-charge k t i := by
    have he : actualSource (k+1) (2*t) i.castSucc =
        actualSource (k+1) t ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩ := by
      dsimp [actualSource]
      push_cast
      rw [pow_succ]; congr 1 <;> ring
    exact he.trans (hcharge i).2.2
  have hear : actualSource (k+1) (2*t) (Fin.last k)=(t : ℤ) := by
    dsimp [actualSource]
    have he : (2 : ℤ)^k*(2*t)=t+(t : ℤ)*modulus (k+1) := by
      dsimp [modulus]; rw [pow_succ]; ring
    have hc : centered (modulus (k+1)) (t : ℤ)=(t : ℤ) :=
      centered_unique hNNpos hNNo (centered_bounds hNNpos hNNo _) ⟨by omega,by dsimp [modulus] at *; omega⟩
        (centered_mod _ _)
    calc
      _ = centered (modulus (k+1)) (t : ℤ) := centered_congr (by rw [he,Int.add_mul_emod_self_right])
      _ = _ := hc
  have hprefix (n : ℕ) : 0≤((sigma.take n).map (charge k t)).sum ∧
      ((sigma.take n).map (charge k t)).sum≤t := by
    simpa only [hsum] using prefix_nonneg_le sigma (charge k t) (fun i _ => hnonneg i) n
  have hnewprefix (n : ℕ) :
      (((earWord k sigma 0).take n).map (actualSource (k+1) (2*t))).sum ∈
        Set.Icc (0 : ℤ) (modulus (k+1)/2) := by
    rw [ear_prefix k sigma 0 (by omega),hear]
    simp_rw [hsource]
    rw [sum_linear]
    by_cases hn : n≤0
    · simp [hn]
      exact (by omega : 0≤modulus (k+1)/2)
    · simp only [hn,ite_false]
      have hs := hwidth (n-1)
      have hq := hprefix (n-1)
      constructor <;> omega
  refine ⟨⟨hp,hz,?_⟩,⟨ear_perm k sigma 0 hp,?_,hnewprefix⟩⟩
  · intro n
    have hs := hwidth n
    exact ⟨hs.1,by omega⟩
  · rw [ear_prefix k sigma 0 (by omega) _ (earWord k sigma 0).length,hear]
    have hn : ¬ (earWord k sigma 0).length≤0 := by simp [earWord]
    simp only [hn,ite_false]
    have hlen : (earWord k sigma 0).length-1=sigma.length := by simp [earWord]
    rw [hlen,List.take_length]
    simp_rw [hsource]
    rw [sum_linear,hz,hsum]
    ring

set_option maxHeartbeats 1000000 in
private theorem diagonal (n : ℕ) (hn : 2≤n) :
    ∃ sigma : List (Fin (2*n+2*n)),
      OriginalOrder (2*n+2*n) (1+2^n+2^(2*n)+2^(2*n+n)) sigma ∧
      OriginalOrder (2*n+2*n+1) (2*(1+2^n+2^(2*n)+2^(2*n+n)))
        (earWord (2*n+2*n) sigma 0) := by
  let k := 2*n+2*n
  let t : ℕ := 1+2^n+2^(2*n)+2^(2*n+n)
  let D : ℤ := t
  let z : ℤ := 2^n
  let q : ℤ := 2^(n-1)
  let H := (q-1)*D
  let f := fun i : ℕ => centered (modulus k) ((2 : ℤ)^i*t)
  have hz : 4≤z := by simpa [z] using pow_le_pow_right₀ (by decide : (1 : ℤ)≤2) hn
  have hzq : z=2*q := by
    dsimp [z,q]
    conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
    ring
  have hq : 2≤q := by omega
  have hD : ThreeRowSource.multiplier n 4=t := by
    simp [ThreeRowSource.multiplier,Finset.sum_range_succ,t]
    omega
  have hDi : 0<D := by dsimp [D,t]; positivity
  have hmult : D*(z-1)=modulus k := by
    have h := ThreeRowSource.multiplier_identity n 4
    simpa only [hD,D,z,show 4*n=k by dsimp [k]; omega,modulus] using h
  have htN : t<2^(4*n)-1 := by
    have hi : (t : ℤ)<(2 : ℤ)^(4*n)-1 := by
      have he : modulus k=(2 : ℤ)^(4*n)-1 := by dsimp [modulus,k]; congr 1; omega
      rw [←he]
      nlinarith
    have hp : (1 : ℕ)≤2^(4*n) := Nat.one_le_two_pow
    exact_mod_cast hi
  have hrep (i : ℕ) (hi : i<k) :
      f i=D*actualSource n 1 ⟨i%n,Nat.mod_lt _ (by omega)⟩ := by
    have h := ThreeRowSource.repeated_source n 4 1 (by omega) (by decide)
      ⟨i,by dsimp [k] at hi; omega⟩
    simpa only [hD,mul_one,Nat.mod_eq_of_lt htN,actualSource,D,
      show 4*n=k by dsimp [k]; omega] using h
  have base (i : ℕ) (hi : i<n) :
      actualSource n 1 ⟨i,hi⟩ = if i+1<n then (2 : ℤ)^i else -(q-1) := by
    have hb := centered_ladder (modulus n) 1 1 n i
      (TwoRunSource.modulus_positive_odd n (by omega)).1
      (TwoRunSource.modulus_positive_odd n (by omega)).2 (by decide)
      ⟨by decide,by dsimp [modulus]; omega⟩ hi (by dsimp [modulus]; ring)
    have he : -(modulus n-1)/2=-(q-1) := by
      dsimp [modulus]
      change -((2 : ℤ)^n-1-1)/2=-(q-1)
      change -(z-1-1)/2=-(q-1)
      omega
    simpa only [actualSource,Nat.cast_one,mul_one,he] using hb
  have row (j i : ℕ) (hj : j<4) (hi : i<n) :
      f (j*n+i)=if i+1<n then (2 : ℤ)^i*D else -H := by
    rw [hrep (j*n+i) (by dsimp [k]; omega)]
    have hm : (j*n+i)%n=i := by omega
    simp only [hm,base i hi]
    split_ifs <;> dsimp [H] <;> ring
  have block (j : ℕ) (hj : j<4) : InStrip f H 0 (List.range' (j*n) n) ∧
      ((List.range' (j*n) n).map f).sum=0 := by
    let P := List.range' (j*n) (n-1)
    have hmass : (P.map f).sum=H := by
      have hh := ladder_sum f (j*n) (n-1) D (fun i hi => by rw [row j i hj (by omega),if_pos (by omega)])
      simpa only [P,q,H] using hh
    have hpos : ∀ i∈P, 0≤f i := by
      intro i hi
      obtain ⟨a,ha,rfl⟩ := List.mem_range'.mp hi
      simp only [Nat.one_mul]
      rw [row j a hj (by omega),if_pos (by omega)]
      positivity
    have hneg : f (j*n+(n-1))=-H := by rw [row j (n-1) hj (by omega),if_neg (by omega)]
    have he : P++[j*n+(n-1)]=List.range' (j*n) n := by
      simpa only [show n-1+1=n by omega] using (List.range'_1_concat (s:=j*n) (n:=n-1)).symm
    have hH : 0≤H := by dsimp [H]; positivity
    have hp : InStrip f H 0 P := positive_block_strip hpos (by omega) (by rw [hmass]; omega)
    have hs : InStrip f H (0+(P.map f).sum) [j*n+(n-1)] := by simp [InStrip,hmass,hneg,hH]
    constructor
    · rw [←he]; exact inStrip_append hp hs
    · rw [←he]; simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hmass,hneg]; ring
  have all_rows (m : ℕ) (hm : m≤4) : InStrip f H 0 (List.range (m*n)) ∧
      ((List.range (m*n)).map f).sum=0 := by
    induction m with
    | zero => simp [InStrip,H]; positivity
    | succ m ih =>
      obtain ⟨hpre,hzero⟩ := ih (by omega)
      obtain ⟨hb,hbz⟩ := block m (by omega)
      have he : List.range (m*n)++List.range' (m*n) n=List.range ((m+1)*n) := by
        simpa only [List.range_eq_range',Nat.zero_add,Nat.add_mul,Nat.one_mul] using
          List.range'_append_1 (s:=0) (m:=m*n) (n:=n)
      constructor
      · rw [←he]; apply inStrip_append hpre; simpa only [hzero,zero_add] using hb
      · rw [←he]; simp only [List.map_append,List.sum_append,hzero,hbz,add_zero]
  have hs := all_rows 4 (by decide)
  have hNat : 0<k := by dsimp [k]; omega
  have hp : (List.range k).Perm (List.range k) := List.Perm.refl _
  let sigma := (List.range k).map (label k hNat)
  have hsigma : sigma.Perm (List.finRange k) := by
    have he : sigma=List.finRange k := by
      apply List.ext_getElem
      · simp [sigma]
      · intro i hi hi'
        apply Fin.ext
        simp only [sigma,List.getElem_map,List.getElem_range,List.getElem_finRange,label]
        exact Nat.mod_eq_of_lt (by simpa [sigma] using hi)
    rw [he]
  have hvalue (i : ℕ) (hi : i∈List.range k) : actualSource k t (label k hNat i)=f i := by
    simp only [actualSource,label,Nat.mod_eq_of_lt (List.mem_range.mp hi),f]
  have width : ∀ m, ((sigma.take m).map (actualSource k t)).sum ∈ Set.Icc (0 : ℤ) H := by
    intro m
    have hh := inStrip_prefix hs.1 m
    rw [show 4*n=k by dsimp [k]; omega] at hh
    have hm := List.map_congr_left (fun i hi => hvalue i (List.mem_of_mem_take hi))
    simpa only [sigma,List.take_map,List.map_map,hm,zero_add] using hh
  have zero : (sigma.map (actualSource k t)).sum=0 := by
    have hm := List.map_congr_left hvalue
    simpa only [sigma,List.map_map,hm,show 4*n=k by dsimp [k]; omega] using hs.2
  have ht : t≤2^(k-1)-1 := by
    have he : (2 : ℤ)^k=2*2^(k-1) := by
      conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
      ring
    have hh : (t : ℤ)≤(2 : ℤ)^(k-1)-1 := by
      change D≤(2 : ℤ)^(k-1)-1
      have hN : modulus k=(2 : ℤ)^k-1 := rfl
      nlinarith
    have hp : (1 : ℕ)≤2^(k-1) := Nat.one_le_two_pow
    exact_mod_cast hh
  refine ⟨sigma,first_ear k t (by dsimp [k]; omega) ht sigma hsigma zero H width ?_⟩
  dsimp [H]
  nlinarith

/-- The diagonal paired-gap family has a common physical order and an ear at cut zero. -/
theorem actualSource_four_negative_adjacent_equal_joint_lift (r s : ℕ)
    (hs : 2≤s) (hr : r=s) :
    ∃ sigma : List (Fin (2*r+2*s)),
      OriginalOrder (2*r+2*s) (1+2^r+2^(2*r)+2^(2*r+s)) sigma ∧
      OriginalOrder (2*r+2*s+1) (2*(1+2^r+2^(2*r)+2^(2*r+s)))
        (earWord (2*r+2*s) sigma 0) := by
  subst r
  exact diagonal s hs

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentEqual
