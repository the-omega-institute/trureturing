/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoublePhysical
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentDoublePhysical
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: An unbounded adjacent paired-gap physical joint witness at r=s+1. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

/-! A common physical permutation for the r=s+1 paired-gap branch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoublePhysical
open SourceWidth PeriodicShortening RunFirstEarTransport
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private chains from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleJointLift
open private Gates four_strip arithmetic inventory
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

set_option maxHeartbeats 1600000 in
-- The physical source, block masses and both full prefix strips are elaborated together.
/-- The complete r=s+1 branch of the adjacent paired-gap family, with the literal
numeric cut 2s+r and the same physical old labels in the marked new word. -/
theorem actualSource_four_negative_adjacent_double_joint_lift
    (r s : ℕ) (hs : 2 ≤ s) (hr : r=s+1) :
    ∃ sigma : List (Fin (2*r+2*s)),
      2*s+r ≤ 2*r+2*s ∧
      OriginalOrder (2*r+2*s) (1+2^r+2^(2*r)+2^(2*r+s)) sigma ∧
      OriginalOrder (2*r+2*s+1) (2*(1+2^r+2^(2*r)+2^(2*r+s)))
        (earWord (2*r+2*s) sigma (2*s+r)) := by
  subst r
  let n := s
  let k := 2*(n+1)+2*n
  let z : ℤ := 2^n
  let q : ℤ := 2^(n-1)
  let N := modulus k
  let A := 4*z^3+4*z^2+2*z+1
  let B := 4*z^3+2*z^2+z+1
  let L := 2*z^3+z^2+z+1
  let M := 2*z^3+2*z^2+2*z+1
  let GV := 2*B-1
  let GW := 2*L-1-z
  let GX := 2*M-1-2*z-2*z^2
  let t : ℕ := 1+2^(n+1)+2^(2*(n+1))+2^(2*(n+1)+n)
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A))
  have hn : 2 ≤ n := hs
  have hq : 2 ≤ q := by
    simpa [q] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 1 ≤ n-1 by omega)
  have hzq : z=2*q := by
    change (2 : ℤ)^n=2*2^(n-1)
    calc
      _ = (2 : ℤ)^((n-1)+1) := congrArg (fun m => (2 : ℤ)^m) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hN : N=4*z^4-1 := by
    dsimp [N,k,modulus,z]
    rw [show 2*(n+1)+2*n=n+n+n+n+2 by omega]
    simp only [pow_add]; ring
  have hNN : modulus (k+1)=2*N+1 := by dsimp [N,modulus]; rw [pow_succ]; ring
  have ht : (t : ℤ)=A := by
    dsimp [t,A,z]
    push_cast
    rw [show 2*(n+1)=n+n+2 by omega]
    simp only [pow_add,pow_succ]; ring
  obtain ⟨hU,hV,hW,hX,hU',hV',hW',hX',hear⟩ := chains n hn
  change ∀ i<n, f i=if i+1<n then 2^i*A else -(N-B)/2 at hU
  change ∀ i<n, f (n+i)=if i+1<n then 2^i*B else -(N-L)/2 at hV
  change ∀ i<n+1, f (2*n+i)=if i+1<n+1 then 2^i*L else -(N-M)/2 at hW
  change ∀ i<n+1, f (2*n+(n+1)+i)=if i+1<n+1 then 2^i*M else -(N-A)/2 at hX
  change ∀ i<n, g i=if i+1<n then 2^i*(2*A) else -(modulus (k+1)-GV)/2 at hU'
  change ∀ i<n, g (n+i)=if i+1<n then 2^i*GV else -(modulus (k+1)-GW)/2 at hV'
  change ∀ i<n+1, g (2*n+i)=if i+1<n+1 then 2^i*GW else -(modulus (k+1)-GX)/2 at hW'
  change ∀ i<n+1, g (2*n+(n+1)+i)=if i+1<n+1 then 2^i*GX else -(modulus (k+1)-A)/2 at hX'
  change g k=A at hear
  let U := List.range (n-1)
  let V := List.range' n (n-1)
  let W := List.range' (2*n) n
  let X := List.range' (3*n+2) (n-1)
  let x0 := 2*n+(n+1)
  let u := n-1
  let v := 2*n-1
  let w := 3*n
  let x := 4*n+1
  have posU (i : ℕ) (hi : i∈U) : f i=2^i*A ∧ g i=2^i*(2*A) := by
    have hi' : i<n-1 := List.mem_range.mp hi
    exact ⟨(hU i (by omega)).trans (ite_eq_left (by omega)),(hU' i (by omega)).trans (ite_eq_left (by omega))⟩
  have posV (i : ℕ) (hi : i<n-1) : f (n+i)=2^i*B ∧ g (n+i)=2^i*GV := by
    exact ⟨(hV i (by omega)).trans (ite_eq_left (by omega)),(hV' i (by omega)).trans (ite_eq_left (by omega))⟩
  have posW (i : ℕ) (hi : i<n) : f (2*n+i)=2^i*L ∧ g (2*n+i)=2^i*GW := by
    exact ⟨(hW i (by omega)).trans (ite_eq_left (by omega)),(hW' i (by omega)).trans (ite_eq_left (by omega))⟩
  have posX (i : ℕ) (hi : i<n-1) : f (3*n+2+i)=2^i*(2*M) ∧ g (3*n+2+i)=2^i*(2*GX) := by
    have e : 3*n+2+i=2*n+(n+1)+(i+1) := by omega
    rw [e]
    constructor
    · rw [hX (i+1) (by omega),ite_eq_left (by omega),pow_succ]; ring
    · rw [hX' (i+1) (by omega),ite_eq_left (by omega),pow_succ]; ring
  have hx0 : f x0=M ∧ g x0=GX := by
    simpa only [Nat.add_zero,pow_zero,one_mul,ite_eq_left (by omega : 0+1<n+1)] using
      And.intro (hX 0 (by omega)) (hX' 0 (by omega))
  have negU : f u=-(N-B)/2 ∧ g u=-(modulus (k+1)-GV)/2 := by
    simpa only [ite_eq_right (by omega : ¬ n-1+1<n)] using And.intro (hU (n-1) (by omega)) (hU' (n-1) (by omega))
  have negV : f v=-(N-L)/2 ∧ g v=-(modulus (k+1)-GW)/2 := by
    simpa only [show n+(n-1)=v by dsimp [v]; omega,ite_eq_right (by omega : ¬ n-1+1<n)] using
      And.intro (hV (n-1) (by omega)) (hV' (n-1) (by omega))
  have negW : f w=-(N-M)/2 ∧ g w=-(modulus (k+1)-GX)/2 := by
    simpa only [show 2*n+n=w by dsimp [w]; omega,ite_eq_right (by omega : ¬ n+1<n+1)] using
      And.intro (hW n (by omega)) (hW' n (by omega))
  have negX : f x=-(N-A)/2 ∧ g x=-(modulus (k+1)-A)/2 := by
    simpa only [show 2*n+(n+1)+n=x by dsimp [x]; omega,ite_eq_right (by omega : ¬ n+1<n+1)] using
      And.intro (hX n (by omega)) (hX' n (by omega))
  have sumU : (U.map f).sum=(q-1)*A ∧ (U.map g).sum=(q-1)*(2*A) := by
    have hu (i : ℕ) (hi : i<n-1) := posU i (List.mem_range.mpr hi)
    exact ⟨by simpa only [U,q,←List.range_eq_range'] using ladder_sum f 0 (n-1) A (fun i hi => by simpa using (hu i hi).1),
      by simpa only [U,q,←List.range_eq_range'] using ladder_sum g 0 (n-1) (2*A) (fun i hi => by simpa using (hu i hi).2)⟩
  have sumV : (V.map f).sum=(q-1)*B ∧ (V.map g).sum=(q-1)*GV :=
    ⟨ladder_sum f n (n-1) B (fun i hi => (posV i hi).1),
      ladder_sum g n (n-1) GV (fun i hi => (posV i hi).2)⟩
  have sumW : (W.map f).sum=(z-1)*L ∧ (W.map g).sum=(z-1)*GW :=
    ⟨ladder_sum f (2*n) n L (fun i hi => (posW i hi).1),
      ladder_sum g (2*n) n GW (fun i hi => (posW i hi).2)⟩
  have sumX : (X.map f).sum=(z-2)*M ∧ (X.map g).sum=(z-2)*GX := by
    have h1 := ladder_sum f (3*n+2) (n-1) (2*M) (fun i hi => (posX i hi).1)
    have h2 := ladder_sum g (3*n+2) (n-1) (2*GX) (fun i hi => (posX i hi).2)
    change (X.map f).sum=(q-1)*(2*M) at h1
    change (X.map g).sum=(q-1)*(2*GX) at h2
    rw [h1,h2,hzq]; constructor <;> ring
  have coefficients : 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ M ∧ 0 ≤ GV ∧ 0 ≤ GW ∧ 0 ≤ GX := by
    dsimp [A,B,L,M,GV,GW,GX]
    rw [hzq]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    all_goals nlinarith [sq_nonneg q,show 0 ≤ q^3 by positivity]
  obtain ⟨hA,hB,hL,hM,hGV,hGW,hGX⟩ := coefficients
  have up : ∀ i∈U, 0≤f i ∧ 0≤g i := by
    intro i hi; rw [(posU i hi).1,(posU i hi).2]; constructor <;> positivity
  have vp : ∀ i∈V, 0≤f i ∧ 0≤g i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simpa only [Nat.one_mul] using (show 0≤f (n+j) ∧ 0≤g (n+j) from by
      rw [(posV j hj).1,(posV j hj).2]; constructor <;> positivity)
  have wp : ∀ i∈W, 0≤f i ∧ 0≤g i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simpa only [Nat.one_mul] using (show 0≤f (2*n+j) ∧ 0≤g (2*n+j) from by
      rw [(posW j hj).1,(posW j hj).2]; constructor <;> positivity)
  have xp : ∀ i∈X, 0≤f i ∧ 0≤g i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simpa only [Nat.one_mul] using (show 0≤f (3*n+2+j) ∧ 0≤g (3*n+2+j) from by
      rw [(posX j hj).1,(posX j hj).2]; constructor <;> positivity)
  have x0p : 0≤f x0 ∧ 0≤g x0 := by rw [hx0.1,hx0.2]; exact ⟨hM,hGX⟩
  let F1 := [x0]++V
  let P := F1++[v]++W++[w]++U
  let R := [u]++X++[x]
  have hp : (P++R).Perm (List.range k) := by
    simpa only [P,R,F1,U,V,W,X,x0,u,v,w,x,k,List.append_assoc] using inventory n hn
  have holdG : Gates (N/2) (F1.map f).sum (f v) (W.map f).sum (f w)
      (U.map f).sum (f u) (X.map f).sum (f x) := by
    simp only [F1,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,
      hx0.1,sumU.1,sumV.1,sumW.1,sumX.1,negU.1,negV.1,negW.1,negX.1]
    simpa only [← hzq,← hN,A,B,L,M] using (arithmetic q hq).1
  have hnewG : Gates N (F1.map g).sum (g v) (W.map g).sum (g w)
      ((U++[k]).map g).sum (g u) (X.map g).sum (g x) := by
    simp only [F1,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,
      hx0.2,sumU.2,sumV.2,sumW.2,sumX.2,negU.2,negV.2,negW.2,negX.2,hear,hNN]
    simpa only [← hzq,← hN,A,B,L,M,GV,GW,GX] using (arithmetic q hq).2
  have hstrip : InStrip f (N/2) 0 (P++R) := by
    simpa only [P,R,List.append_assoc] using four_strip f (N/2) F1 W U X v w u x
      (by intro i hi; rcases List.mem_append.mp hi with hi|hi
          · simpa using (List.mem_singleton.mp hi ▸ x0p.1)
          · exact (vp i hi).1)
      (fun i hi => (wp i hi).1) (fun i hi => (up i hi).1) (fun i hi => (xp i hi).1)
      holdG
  have hstrip' : InStrip g N 0 (P++k::R) := by
    simpa only [P,R,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
      four_strip g N F1 W (U++[k]) X v w u x
        (by intro i hi; rcases List.mem_append.mp hi with hi|hi
            · simpa using (List.mem_singleton.mp hi ▸ x0p.2)
            · exact (vp i hi).2)
        (fun i hi => (wp i hi).2)
        (by intro i hi; rcases List.mem_append.mp hi with hi|hi
            · exact (up i hi).2
            · rw [List.mem_singleton.mp hi,hear]; exact hA)
        (fun i hi => (xp i hi).2) hnewG
  have hcut : P.length=2*n+(n+1) := by
    dsimp [P,F1,U,V,W]; simp only [List.length_append,List.length_singleton,List.length_range',List.length_range]; omega
  have hp' : (P++k::R).Perm (List.range (k+1)) := by
    have he : (P++k::R).Perm ((P++R)++[k]) := by
      change (P++([k]++R)).Perm ((P++R)++[k])
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add]
      ac_rfl
    rw [List.range_succ]
    exact he.trans (hp.append_right [k])
  have hz : ((List.range k).map f).sum=0 := by
    simpa only [f,N,← ht] using ThreeNegativeEqualOuterSourceBridge.source_zero k t (by dsimp [k]; omega)
  have hz' : ((List.range (k+1)).map g).sum=0 := by
    have he : ((2*t : ℕ) : ℤ)=2*A := by push_cast; rw [ht]
    simpa only [g,← he] using ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*t) (by dsimp [k]; omega)
  refine ⟨(P++R).map (label k (by dsimp [k]; omega)),by omega,?_,?_⟩
  · apply lift_order k t (by dsimp [k]; omega) (P++R) hp
    · simpa only [f,N,← ht] using hstrip
    · simpa only [f,N,← ht] using hz
  · rw [marked_word k (2*n+(n+1)) (by dsimp [k]; omega) P R hcut hp]
    have he : ((2*t : ℕ) : ℤ)=2*A := by push_cast; rw [ht]
    apply lift_order (k+1) (2*t) (by dsimp [k]; omega) (P++k::R) hp'
    · have hh : modulus (k+1)/2=N := by omega
      simpa only [g,he,hh] using hstrip'
    · simpa only [g,he] using hz'

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoublePhysical
