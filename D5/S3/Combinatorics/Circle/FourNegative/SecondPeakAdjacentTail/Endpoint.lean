import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Rounding
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PhysicalWord
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.BoundaryWords
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open SourceWidth
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap
open private physical_strips
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PhysicalWord
open private base newBase sourceMod oldValue newValue size
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private boundaryWord boundaryB boundaryC boundaryCut boundary_strips
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.BoundaryWords
open private low_integer_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Selection
open private high_integer_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Rounding
open private common_bounds windows_of_residual
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

/-- The exact selector interface consumed by the physical packet.  It is an
internal arithmetic interface: the final theorem below has no selector
hypothesis once the three dyadic selector families are supplied. -/
private def AdjacentSelector (a b c d : ℕ) : Prop :=
  ∃ v m : ℕ, v≤2^(c-1)-1 ∧ m≤2^(b-1)-1 ∧
    Windows ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c)) (v:ℚ) (m:ℚ)

private theorem adjacent_selector_domain (a b c : ℕ)
    (ha : 2≤a) (hac : a<c) (hcb : c<b)
    (hex2 : b=c+2 → ¬(a=2 ∧ c=3) ∧ ¬(a=2 ∧ c=5))
    (hex3 : b=c+3 → ¬(a=2 ∧ c=3)) :
    AdjacentSelector a b c (c+1) := by
  have hc : 2≤c := by omega
  by_cases hs2 : b=c+2
  · obtain ⟨v,m,hv0,hm0,hr⟩ := low_integer_selection a c 2 (Or.inl rfl) ha hac
      (by simpa [hs2] using hex2) (by intro; omega)
    have hv : 0≤(v:ℚ) := by exact_mod_cast hv0
    have hm : 0≤(m:ℚ) := by exact_mod_cast hm0
    obtain ⟨hvv,hvstock,hr'⟩ := hr
    have hcommon := common_bounds ((2:ℚ)^a) ((2:ℚ)^c) 4
      (by exact_mod_cast (show (4:ℤ)≤2^a by exact pow_le_pow_right₀ (by norm_num) ha))
      (by exact_mod_cast (show 2*(2:ℤ)^a≤(2:ℤ)^c by exact pow_le_pow_right₀ (by norm_num) (by omega)))
      (by norm_num)
    have hw := windows_of_residual ((2:ℚ)^a) ((2:ℚ)^c) 4 (v:ℚ) (m:ℚ)
      (by exact_mod_cast (show (4:ℤ)≤2^a by exact pow_le_pow_right₀ (by norm_num) ha))
      (by exact_mod_cast (show 2*(2:ℤ)^a≤(2:ℤ)^c by exact pow_le_pow_right₀ (by norm_num) (by omega)))
      (by norm_num) hcommon hv hr'
    refine ⟨Int.toNat v,Int.toNat m,?_,?_,?_⟩
    · have : (0:ℤ)≤v := hv0; simpa [Int.toNat_of_nonneg this]
      using hvv
    · have : (0:ℤ)≤m := hm0
      have hbnd : m≤(2:ℤ)^(b-1)-1 := by
        have hh := hm0
        have hs := hr'.2.1
        rw [show (2:ℚ)^c/2*4=(2:ℚ)^c*2 by ring] at hs
        exact_mod_cast (by nlinarith : m≤(2:ℤ)^(b-1)-1)
      simpa [Int.toNat_of_nonneg this] using hbnd
    · simpa [Int.toNat_of_nonneg hv0,Int.toNat_of_nonneg hm0,
        show (2:ℚ)^(b-c)=4 by simp [hs2]] using hw
  · by_cases hs3 : b=c+3
    · obtain ⟨v,m,hh⟩ := low_integer_selection a c 3 (Or.inr rfl) ha hac
        (by simpa [hs3] using hex2) (by simpa using hex3)
      obtain ⟨hv0,hvstock,hr⟩ := hh
      have hcommon := common_bounds ((2:ℚ)^a) ((2:ℚ)^c) 8
        (by exact_mod_cast (show (4:ℤ)≤2^a by exact pow_le_pow_right₀ (by norm_num) ha))
        (by exact_mod_cast (show 2*(2:ℤ)^a≤(2:ℤ)^c by exact pow_le_pow_right₀ (by norm_num) (by omega)))
        (by norm_num)
      have hw := windows_of_residual ((2:ℚ)^a) ((2:ℚ)^c) 8 (v:ℚ) (m:ℚ)
        (by exact_mod_cast (show (4:ℤ)≤2^a by exact pow_le_pow_right₀ (by norm_num) ha))
        (by exact_mod_cast (show 2*(2:ℤ)^a≤(2:ℤ)^c by exact pow_le_pow_right₀ (by norm_num) (by omega)))
        (by norm_num) hcommon (by exact_mod_cast hv0) hr
      refine ⟨Int.toNat v,Int.toNat m,?_,?_,?_⟩
      · exact_mod_cast hv0
      · have hs := hr.2.1; have : m≤(2:ℤ)^(b-1)-1 := by exact_mod_cast (by nlinarith : (m:ℚ)≤(2:ℚ)^(b-1)-1); exact_mod_cast this
      · simpa [Int.toNat_of_nonneg hv0,Int.toNat_of_nonneg (by exact_mod_cast hr.1),
          show (2:ℚ)^(b-c)=8 by simp [hs3]] using hw
    · have hhigh : c+4≤b := by omega
      obtain ⟨m,hm0,hmb,hw⟩ := high_integer_selection a b c ha hac hhigh
      refine ⟨0,Int.toNat m,by norm_num,?_,?_⟩
      · exact_mod_cast hmb
      · simpa [Int.toNat_of_nonneg hm0] using hw

private theorem selector_to_physical
    (a b c d : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hdc : d=c+1) (hcb : c<b)
    (hs : AdjacentSelector a b c d) :
    ∃ w : List ℕ, w.Perm (List.range (a+b+c+d)) ∧ d≤a+b+c+d ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 w ∧
      InStrip (newValue a b c d) (sourceMod a b c d) 0
        (insertAt (a+b+c+d) w d) := by
  subst d
  rcases hs with ⟨v,m,hv,hm,hw⟩
  let x : ℚ := (2:ℚ)^a
  let z : ℚ := (2:ℚ)^c
  let q : ℚ := (2:ℚ)^(b-c)
  have hwin := hw
  have ho : let AA := base a b c d 0; let BB := base a b c d 1
      let LL := base a b c d 2; let KK := base a b c d 3
      ∀ r : Fin 3,
      0≤2*(![BB-AA,((v:ℤ)+1)*BB-KK+(m:ℤ)*LL,((v:ℤ)+1)*BB-LL] r) ∧
      2*(![BB-AA,((v:ℤ)+1)*BB-KK+(m:ℤ)*LL,((v:ℤ)+1)*BB-LL] r)≤
        ![BB,AA,KK] r-1 := by
    dsimp
    intro r
    fin_cases r
    · simpa [x,z,q,A,B,L,K,SU,SV,SW] using hwin.1
    · simpa [x,z,q,A,B,L,K,SU,SV,SW] using hwin.2.2.1
    · simpa [x,z,q,A,B,L,K,SU,SV,SW] using hwin.2.2.2.2.1
  have hn : let AA := base a b c d 0; let UU := newBase a b c d 1
      let VV := newBase a b c d 2; let WW := newBase a b c d 3
      ∀ r : Fin 3,
      0≤2*(![UU-2*AA,((v:ℤ)+1)*UU-WW+(m:ℤ)*VV,((v:ℤ)+1)*UU-VV] r) ∧
      2*(![UU-2*AA,((v:ℤ)+1)*UU-WW+(m:ℤ)*VV,((v:ℤ)+1)*UU-VV] r)≤
        ![UU,AA,WW] r-1 := by
    dsimp
    intro r
    fin_cases r
    · simpa [x,z,q,A,B,L,K,SU,SV,SW] using hwin.2.1
    · simpa [x,z,q,A,B,L,K,SU,SV,SW] using hwin.2.2.2.1
    · simpa [x,z,q,A,B,L,K,SU,SV,SW] using hwin.2.2.2.2.2
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
  exact adjacent_tail_all_natural a b c d ha hb hc hd hdc (by omega) hs

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
