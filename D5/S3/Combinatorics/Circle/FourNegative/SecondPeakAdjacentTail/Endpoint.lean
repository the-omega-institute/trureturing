/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Endpoint
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Joint physical lift for every original adjacent-tail quadruple. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Rounding
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PhysicalWord
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.BoundaryWords
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint
import Batteries.Tactic.OpenPrivate

set_option maxErrors 20
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
open SourceWidth PeriodicShortening RunFirstEarTransport
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint
open private physical_strips
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PhysicalWord
open private base newBase charge sourceMod oldValue newValue size
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private boundaryWord boundaryB boundaryC boundaryCut boundary_strips
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.BoundaryWords
open private low_integer_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Selection
open private high_integer_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Rounding
open private common_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Selection
open private windows_of_residual
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

/-- The exact selector interface consumed by the physical packet.  It is an
internal arithmetic interface: the final theorem below has no selector
hypothesis once the three dyadic selector families are supplied. -/
private def AdjacentSelector (a b c d : ℕ) : Prop :=
  ∃ v m : ℕ, v≤2^(c-1)-1 ∧ m≤2^(b-1)-1 ∧
    Windows ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c)) (v:ℚ) (m:ℚ)

private theorem dyadic_half (n : ℕ) (hn : 1≤n) :
    (2:ℚ)^n/2=(2:ℚ)^(n-1) := by
  conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
  ring

private theorem nat_stock_of_rational (v : ℤ) (n : ℕ) (hn : 1≤n)
    (hv : (v:ℚ)≤(2:ℚ)^n/2-1) : v.toNat≤2^(n-1)-1 := by
  apply Int.toNat_le.mpr
  have hp : (1:ℕ)≤2^(n-1) := one_le_pow₀ (by norm_num)
  have hc : ((2^(n-1)-1:ℕ):ℚ)=(2:ℚ)^(n-1)-1 := by
    rw [Nat.cast_sub hp]
    norm_num
  rw [dyadic_half n hn] at hv
  have hQ : (v:ℚ)≤((2^(n-1)-1:ℕ):ℚ) := by rw [hc]; exact hv
  exact_mod_cast hQ

private theorem adjacent_selector_domain (a b c : ℕ)
    (ha : 2≤a) (hac : a<c) (hcb : c+1<b)
    (hex2 : b=c+2 → ¬(a=2 ∧ c=3) ∧ ¬(a=2 ∧ c=5))
    (hex3 : b=c+3 → ¬(a=2 ∧ c=3)) :
    AdjacentSelector a b c (c+1) := by
  have hx : (4:ℚ)≤(2:ℚ)^a := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) ha using 1 <;> norm_num
  have hz : 2*(2:ℚ)^a≤(2:ℚ)^c := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show a+1≤c by omega)
    simpa only [pow_succ,mul_comm] using h
  by_cases hlow : b=c+2 ∨ b=c+3
  · obtain ⟨v,m,hs⟩ := low_integer_selection a c (b-c) (by omega) ha hac
      (by intro h; apply hex2; omega) (by intro h; apply hex3; omega)
    obtain ⟨hv0Q,hvs,hr⟩ := hs
    have hv0 : (0:ℤ)≤v := by exact_mod_cast hv0Q
    have hm0 : (0:ℤ)≤m := by exact_mod_cast hr.1
    have hq : (4:ℚ)≤(2:ℚ)^(b-c) := by
      convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 2≤b-c by omega) using 1 <;> norm_num
    have hw := windows_of_residual _ _ _ _ _ hx hz hq (common_bounds _ _ _ hx hz hq) hv0Q hr
    have hvn : ((v.toNat:ℕ):ℚ)=(v:ℚ) := by exact_mod_cast Int.toNat_of_nonneg hv0
    have hmn : ((m.toNat:ℕ):ℚ)=(m:ℚ) := by exact_mod_cast Int.toNat_of_nonneg hm0
    refine ⟨v.toNat,m.toNat,?_,?_,?_⟩
    · apply nat_stock_of_rational v c (by omega)
      linarith
    · apply nat_stock_of_rational m b (by omega)
      have hp : (2:ℚ)^(b-c)*(2:ℚ)^c=(2:ℚ)^b := by
        rw [←pow_add,Nat.sub_add_cancel (by omega : c≤b)]
      have hh := hr.2.1
      rw [hp] at hh
      linarith
    · simpa only [hvn,hmn] using hw
  · obtain ⟨m,hm0,hmb,hw⟩ := high_integer_selection a b c ha hac (by omega)
    refine ⟨0,m.toNat,by omega,Int.toNat_le.mpr hmb,?_⟩
    have hmn : ((m.toNat:ℕ):ℚ)=(m:ℚ) := by exact_mod_cast Int.toNat_of_nonneg hm0
    simpa only [Nat.cast_zero,hmn] using hw

private theorem selector_to_physical
    (a b c d : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hdc : d=c+1) (hcb : c<b)
    (hs : AdjacentSelector a b c d) :
    ∃ w : List ℕ, w.Perm (List.range (a+b+c+d)) ∧ d≤a+b+c+d ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 w ∧
      InStrip (newValue a b c d) (sourceMod a b c d) 0
        (insertAt (a+b+c+d) w d) := by
  rcases hs with ⟨v,m,hv,hm,hw⟩
  let x : ℚ := (2:ℚ)^a
  let z : ℚ := (2:ℚ)^c
  let q : ℚ := (2:ℚ)^(b-c)
  have hwin : Windows x z q (v:ℚ) (m:ℚ) := hw
  have hy : (2:ℚ)^b=q*z := by
    dsimp [q,z]
    rw [←pow_add,Nat.sub_add_cancel (by omega : c≤b)]
  have hdpow : (2:ℚ)^d=2*z := by
    rw [hdc,pow_succ]
    dsimp [z]
    ring
  have hA : ((base a b c d 0:ℤ):ℚ)=A x z q := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have hB : ((base a b c d 1:ℤ):ℚ)=B x z q := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have hL : ((base a b c d 2:ℤ):ℚ)=L x z := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have hK : ((base a b c d 3:ℤ):ℚ)=K z q := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have hU : ((newBase a b c d 1:ℤ):ℚ)=SU x z q := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have hV : ((newBase a b c d 2:ℤ):ℚ)=SV x z := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have hW : ((newBase a b c d 3:ℤ):ℚ)=SW z q := by
    norm_num [base,newBase,charge]
    try push_cast
    simp only [hdpow,hy]
    dsimp [x,z,q,A,B,L,K,SU,SV,SW]
    ring
  have ho : let AA := base a b c d 0; let BB := base a b c d 1
      let LL := base a b c d 2; let KK := base a b c d 3
      ∀ r : Fin 3,
      0≤2*(![BB-AA,((v:ℤ)+1)*BB-KK+(m:ℤ)*LL,((v:ℤ)+1)*BB-LL] r) ∧
      2*(![BB-AA,((v:ℤ)+1)*BB-KK+(m:ℤ)*LL,((v:ℤ)+1)*BB-LL] r)≤
        ![BB,AA,KK] r-1 := by
    dsimp
    intro r
    fin_cases r
    · have hh := hwin.1
      rw [←hB,←hA] at hh
      exact_mod_cast hh
    · have hh := hwin.2.2.1
      dsimp only [E] at hh
      rw [←hB,←hA,←hL,←hK] at hh
      exact_mod_cast hh
    · have hh := hwin.2.2.2.2.1
      rw [←hB,←hL,←hK] at hh
      exact_mod_cast hh
  have hn : let AA := base a b c d 0; let UU := newBase a b c d 1
      let VV := newBase a b c d 2; let WW := newBase a b c d 3
      ∀ r : Fin 3,
      0≤2*(![UU-2*AA,((v:ℤ)+1)*UU-WW+(m:ℤ)*VV,((v:ℤ)+1)*UU-VV] r) ∧
      2*(![UU-2*AA,((v:ℤ)+1)*UU-WW+(m:ℤ)*VV,((v:ℤ)+1)*UU-VV] r)≤
        ![UU,AA,WW] r-1 := by
    dsimp
    intro r
    fin_cases r
    · have hh := hwin.2.1
      rw [←hU,←hA] at hh
      exact_mod_cast hh
    · have hh := hwin.2.2.2.1
      dsimp only [F] at hh
      rw [←hU,←hW,←hV,←hA] at hh
      exact_mod_cast hh
    · have hh := hwin.2.2.2.2.2
      rw [←hU,←hV,←hW] at hh
      exact_mod_cast hh
  obtain ⟨w,hwperm,hdk,hold,hnew⟩ := physical_strips a b c d v m ha hb hc hd hv hm ho hn
  exact ⟨w,hwperm,hdk,hold,hnew⟩

/-- Once the arithmetic selector is consumed, the PacketNormalForm equivalence
creates the literal fresh ear and the two complete one-period orders. -/
private theorem adjacent_tail_one_period
    (a b c d : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hdc : d=c+1) (hcb : c<b)
    (hs : AdjacentSelector a b c d) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  obtain ⟨w,hp,hdw,hold,hnew⟩ := selector_to_physical a b c d ha hb hc hd hdc hcb hs
  have hh := (actual_nat_joint_iff a b c d ha hb hc hd).mpr
    ⟨w,by simpa [size] using hp,hold,d,by simpa [size] using hdw,hnew⟩
  exact hh

/-- Full natural repetition/take transport for an already selected adjacent
packet.  The selector remains internal so this theorem is the exact G3/G4
composition boundary used by the final arithmetic selector. -/
private theorem adjacent_tail_all_natural
    (a b c d : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hdc : d=c+1) (hcb : c<b)
    (hs : AdjacentSelector a b c d) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
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
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  obtain ⟨sigma,j,hj,ho,hn⟩ := adjacent_tail_one_period a b c d ha hb hc hd hdc hcb hs
  have eo (r : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 r
  have en (r : ℕ) := zero_period_transport _ _
    (earWord (a+b+c+d) sigma j) hn.2.1 hn.2.2 r
  have half : modulus (a+b+c+d+1)/2=modulus (a+b+c+d) := by
    have hp : (2:ℤ)^(a+b+c+d+1)=2*(2:ℤ)^(a+b+c+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp]
    omega
  exact ⟨sigma,j,hj,ho,hn,
    (fun r n => by simpa only [zero_add,Set.mem_Icc] using (eo r).2 n),
    (fun r n => by simpa only [half,zero_add,Set.mem_Icc] using (en r).2 n),
    (fun r => ⟨(eo r).1,(en r).1⟩)⟩

/-! The three finite strips are consumed here rather than treated as a
numerical appendix.  This is the exact boundary branch of G3; the remaining
selector is the unbounded arithmetic branch above. -/
private theorem boundary_all_natural (r : Fin 3) :
    let b := boundaryB r
    let c := boundaryC r
    let d := c+1
    ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧
      OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧
      OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))
        (earWord (2+b+c+d) sigma j) ∧
      (∀ q n : ℕ, ((((List.replicate q sigma).flatten).take n).map
        (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (2+b+c+d)/2)) ∧
      (∀ q n : ℕ, ((((List.replicate q (earWord (2+b+c+d) sigma j)).flatten).take n).map
        (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (2+b+c+d))) ∧
      (∀ q : ℕ,
        (((List.replicate q sigma).flatten).map
          (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum=0 ∧
        (((List.replicate q (earWord (2+b+c+d) sigma j)).flatten).map
          (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum=0) := by
  let b := boundaryB r
  let c := boundaryC r
  let d := c+1
  have ha : 2≤2 := by omega
  have hb : 2≤b := by fin_cases r <;> simp [b,boundaryB]
  have hc : 2≤c := by fin_cases r <;> simp [c,boundaryC]
  have hd : 2≤d := by dsimp [d]; omega
  obtain ⟨w,hp,hdw,hold,hnew⟩ := boundary_strips r
  have hh := (actual_nat_joint_iff 2 b c d ha hb hc hd).mpr
    ⟨w,by simpa [size,b,c,d] using hp,hold,boundaryCut r,
      by simpa [size,b,c,d] using hdw,hnew⟩
  obtain ⟨sigma,j,hj,ho,hn⟩ := hh
  have eo (q : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 q
  have en (q : ℕ) := zero_period_transport _ _
    (earWord (2+b+c+d) sigma j) hn.2.1 hn.2.2 q
  have half : modulus (2+b+c+d+1)/2=modulus (2+b+c+d) := by
    have hp' : (2:ℤ)^(2+b+c+d+1)=2*(2:ℤ)^(2+b+c+d) := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hp']
    omega
  refine ⟨sigma,j,hj,ho,hn,?_,?_,?_⟩
  · intro q n
    simpa only [zero_add,Set.mem_Icc] using (eo q).2 n
  · intro q n
    simpa only [half,zero_add,Set.mem_Icc] using (en q).2 n
  · intro q
    exact ⟨(eo q).1,(en q).1⟩

/-- Complete adjacent-tail source endpoint.  The three literal exceptional
words are the finite branch; every other point is routed through the integer
dyadic selector and the physical packet composition above. -/
theorem actualSource_second_peak_adjacent_tail_joint_lift
    (a b c d : ℕ) (ha : 2≤a) (hac : a<c)
    (hdc : d=c+1) (hdb : d<b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
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
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  have hb : 2≤b := by omega
  have hc : 2≤c := by omega
  have hd : 2≤d := by omega
  by_cases h1 : a=2 ∧ b=5 ∧ c=3
  · rcases h1 with ⟨rfl,rfl,rfl⟩
    simpa [hdc] using (boundary_all_natural (0 : Fin 3))
  by_cases h2 : a=2 ∧ b=7 ∧ c=5
  · rcases h2 with ⟨rfl,rfl,rfl⟩
    simpa [hdc] using (boundary_all_natural (1 : Fin 3))
  by_cases h3 : a=2 ∧ b=6 ∧ c=3
  · rcases h3 with ⟨rfl,rfl,rfl⟩
    simpa [hdc] using (boundary_all_natural (2 : Fin 3))
  have hs := adjacent_selector_domain a b c ha hac (by omega)
    (by intro hb2; omega) (by intro hb3; omega)
  exact adjacent_tail_all_natural a b c d ha hb hc hd hdc (by omega) (by simpa only [hdc] using hs)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
