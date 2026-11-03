/- GID: D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Allocation
   generality: I
   mirror-B: none(waiver:consumed-dyadic-allocation)
   mirror-E: none(waiver:consumed-dyadic-allocation)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Constructive floor allocations on all noncritical interior sectors. -/
import D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Critical

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
open private D A B L M eps oldSeam newSeam oldHead newHead Gates Stock
  positive_heads ascending_gates reverse_gates dyadic_split dyadic_four
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Arithmetic
open private reverse_grid
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingArithmetic

private theorem floor_data (X AA : ℤ) (hX : 0≤X) (hA : 0<AA) :
    0≤X/AA ∧ 0≤X-(X/AA)*AA ∧ X-(X/AA)*AA<AA := by
  have h0 := Int.emod_nonneg X (ne_of_gt hA)
  have h1 := Int.emod_lt_of_pos X hA
  have he := Int.emod_add_mul_ediv X AA
  exact ⟨Int.ediv_nonneg hX hA.le,by nlinarith,by nlinarith⟩

set_option maxHeartbeats 2400000 in
private theorem ascending_equal (p y : ℤ) (hp : 4≤p) (hy : 4≤y) :
    ∃ v w : ℤ, Stock true (p*y) y y v w ∧ Gates true (p*y) y y v w := by
  let t := p*y
  let AA := A t y y
  let BB := B t y
  let LL := L t y
  let MM := M t y y
  let DD := D y y
  let P := p-4
  let Y := y-4
  have hP : 0≤P := by dsimp [P]; omega
  have hY : 0≤Y := by dsimp [Y]; omega
  have ep : p=P+4 := by dsimp [P]; ring
  have ey : y=Y+4 := by dsimp [Y]; ring
  have margins : 0<LL-MM ∧ 0<t*AA-2*(LL-MM) ∧
      0<2*(LL-AA)-(BB+DD) ∧ 0<4*(LL-AA)-(2*LL+2*DD-y) ∧ 0<BB-LL := by
    dsimp [AA,BB,LL,MM,DD,t,A,B,L,M,D]
    rw [ep,ey]
    repeat' constructor
    all_goals ring_nf <;> positivity
  have ht : y≤t := by dsimp [t]; nlinarith
  have hpos := positive_heads t y y (by omega) hy hy
  let v := (LL-MM)/AA
  obtain ⟨hv,hr0,hr1⟩ := floor_data (LL-MM) AA (by omega) hpos.1
  have stock : 2*v<t := by
    have h : (2*v)*AA<t*AA := by dsimp [v]; nlinarith [margins.2.1]
    exact (mul_lt_mul_iff_left₀ hpos.1).mp h
  refine ⟨v,0,?_,?_⟩
  · dsimp [Stock]; exact ⟨hv,stock,le_rfl,by omega⟩
  · apply ascending_gates t y y v 0 hy hy ht ht le_rfl
    all_goals dsimp [v] at *
    all_goals nlinarith [margins.2.2.1,margins.2.2.2.1,margins.2.2.2.2]

private theorem ascending_twice (q y : ℤ) (hq : 2≤q) (hy : 4≤y) :
    ∃ v w : ℤ, Stock true (2*q*y) y (2*y) v w ∧
      Gates true (2*q*y) y (2*y) v w := by
  let t := 2*q*y
  let z := 2*y
  let v := q-1
  let H := M t y z+v*A t y z
  let Q := q-2
  let Y := y-4
  have hQ : 0≤Q := by dsimp [Q]; omega
  have hY : 0≤Y := by dsimp [Y]; omega
  have eq : q=Q+2 := by dsimp [Q]; ring
  have ey : y=Y+4 := by dsimp [Y]; ring
  have margins : 0≤2*H-(B t y+D y z) ∧ 0≤B t y-H ∧
      0≤4*H-(2*L t z+2*D y z-z) ∧ 0≤L t z-H ∧ 0<t-2*v := by
    dsimp [H,v,t,z,A,B,L,M,D]
    rw [eq,ey]
    repeat' constructor
    all_goals ring_nf <;> positivity
  refine ⟨v,0,?_,?_⟩
  · dsimp [Stock,v,z]
    exact ⟨by omega,by linarith [margins.2.2.2.2],le_rfl,by omega⟩
  · apply ascending_gates t y z v 0 hy (by dsimp [z]; omega)
      (by dsimp [t]; nlinarith) (by dsimp [t,z]; nlinarith) le_rfl
    all_goals dsimp [H] at margins
    all_goals nlinarith [margins.1,margins.2.1,margins.2.2.1,margins.2.2.2.1]

set_option maxHeartbeats 2400000 in
private theorem ascending_separated (p q y : ℤ)
    (hq : 4≤q) (hp : 2*q≤p) (hy : 4≤y) :
    ∃ v w : ℤ, Stock true (p*y) y (q*y) v w ∧ Gates true (p*y) y (q*y) v w := by
  let t := p*y
  let z := q*y
  let AA := A t y z
  let BB := B t y
  let LL := L t z
  let MM := M t y z
  let DD := D y z
  let Q := q-4
  let P := p-2*q
  let Y := y-4
  have hQ : 0≤Q := by dsimp [Q]; omega
  have hP : 0≤P := by dsimp [P]; omega
  have hY : 0≤Y := by dsimp [Y]; omega
  have eq : q=Q+4 := by dsimp [Q]; ring
  have ep : p=2*(Q+4)+P := by dsimp [P,Q]; ring
  have ey : y=Y+4 := by dsimp [Y]; ring
  have margins : 0<BB-DD-2*AA ∧ 0<t*AA-2*(BB-MM) ∧
      0<LL-2*BB-DD ∧ 0<z*BB-2*LL := by
    dsimp [AA,BB,LL,MM,DD,t,z,A,B,L,M,D]
    rw [ep,eq,ey]
    repeat' constructor
    all_goals ring_nf <;> positivity
  have hyt : y≤t := by dsimp [t]; nlinarith
  have hzt : z≤t := by dsimp [t,z]; nlinarith
  have hz : 4≤z := by dsimp [z]; nlinarith
  have hp0 := positive_heads t y z (by omega) hy hz
  have he : 0≤eps t y z := (by
    have h := mul_nonneg (show 0≤y by omega) (show 0≤t-z by omega)
    have hid : eps t y z=y*(t-z)+(t-y) := by unfold eps A M D; ring
    rw [hid]; omega)
  have hBM : 0≤BB-MM := by dsimp [eps] at he; nlinarith [margins.1,hp0.1]
  let v := (BB-MM)/AA
  obtain ⟨hv,hr0,hr1⟩ := floor_data (BB-MM) AA hBM hp0.1
  let H := MM+v*AA
  have hH : 0≤H ∧ BB-AA<H ∧ H≤BB := by
    dsimp [H]; constructor
    · have hv' : 0 ≤ v := hv
      have hvA : 0 ≤ v * AA := mul_nonneg hv' hp0.1.le
      nlinarith [hp0.2.2.1, hvA]
    · constructor <;> nlinarith
  have hvc : 2*v<t := by
    have h : (2*v)*AA<t*AA := by dsimp [v]; nlinarith [margins.2.1]
    exact (mul_lt_mul_iff_left₀ hp0.1).mp h
  let w := (LL-H)/BB
  have hLH : 0≤LL-H := by nlinarith [margins.2.2.1,hH.2.2,hp0.2.1]
  obtain ⟨hw,hs0,hs1⟩ := floor_data (LL-H) BB hLH hp0.2.1
  have hwc : 2*w<z := by
    have h : (2*w)*BB<z*BB := by dsimp [w]; nlinarith [margins.2.2.2,hH.1]
    exact (mul_lt_mul_iff_left₀ hp0.2.1).mp h
  refine ⟨v,w,⟨hv,hvc,hw,hwc⟩,?_⟩
  apply ascending_gates t y z v w hy hz hyt hzt hw
  · change BB+DD≤2*H
    nlinarith [margins.1,hH.2.1]
  · exact hH.2.2
  · change 2*LL+2*DD-z≤4*H+2*(2*BB-1)*w
    have hh : LL-H-w*BB≤BB-1 := by dsimp [w]; omega
    nlinarith [margins.2.2.1,hwc]
  · change H+w*BB≤LL
    have hs := hs0
    dsimp [w]
    nlinarith [hs]

set_option maxHeartbeats 2400000 in
private theorem descending_wide (p u z : ℤ) (hp : 4≤p) (hu : 2≤u) (hz : 4≤z) :
    ∃ v w : ℤ, Stock false (p*u*z) (u*z) z v w ∧ Gates false (p*u*z) (u*z) z v w := by
  let t := p*u*z
  let y := u*z
  let AA := A t y z
  let BB := B t y
  let LL := L t z
  let MM := M t y z
  let DD := D y z
  let P := p-4
  let U := u-2
  let Z := z-4
  have hP : 0≤P := by dsimp [P]; omega
  have hU : 0≤U := by dsimp [U]; omega
  have hZ : 0≤Z := by dsimp [Z]; omega
  have ep : p=P+4 := by dsimp [P]; ring
  have eu : u=U+2 := by dsimp [U]; ring
  have ez : z=Z+4 := by dsimp [Z]; ring
  have margins : 0<BB-2*LL ∧ 0<LL-MM ∧ 0<LL-DD-2*AA ∧
      0<t*AA-2*BB ∧ 0<AA-MM := by
    dsimp [AA,BB,LL,MM,DD,t,y,A,B,L,M,D]
    rw [ep,eu,ez]
    repeat' constructor
    all_goals ring_nf <;> positivity
  have hy : 4≤y := by dsimp [y]; nlinarith
  have hyt : y≤t := by dsimp [y,t]; nlinarith
  have hzt : z≤t := by dsimp [y,t] at *; nlinarith
  have pos := positive_heads t y z (by omega) hy hz
  have hL : z≤LL := by dsimp [LL,L]; nlinarith [sq_nonneg t]
  obtain ⟨hv,hr,hr1,hgap,hgap1,hlo,hhi,hcap,hfour⟩ :=
    reverse_grid AA BB LL MM DD z t 1 pos.1 pos.2.2.2.1 le_rfl
      (by nlinarith [margins.2.2.2.2]) (by omega) (by omega)
      hL (by dsimp [DD,D]; positivity) (by nlinarith [margins.2.2.1])
      (by nlinarith [margins.2.2.2.1])
  let C := (4*BB-2*LL+z-2*DD-2)/4
  let v := (C-(AA-MM))/AA
  have hv' : 0 ≤ v := by simpa [v,C] using hv
  have hcap' : 2 * v < t := by simpa [v,C] using hcap
  have hRmax := le_antisymm hr1 (le_max_left _ _)
  rw [hRmax] at hlo hhi
  have hlo' : BB-LL < (v+1)*AA-MM := by
    simpa [v,C] using hlo
  have hhi' : (v+1)*AA-MM ≤ C := by
    simpa [v,C] using hhi
  refine ⟨v,0,⟨hv',hcap',le_rfl,by omega⟩,?_⟩
  apply reverse_gates t y z v hy hz hyt hzt (by omega) margins.2.1
  · simpa [AA,BB,LL,MM,DD,t,y] using hlo'
  · nlinarith [hhi',hfour]

private theorem ascending_allocate (a b c : ℕ) (hb : 2≤b) (hbc : b≤c)
    (hca : c<a) (hgap : b+2≤a) :
    ∃ v w : ℤ, Stock true (2^a) (2^b) (2^c) v w ∧
      Gates true (2^a) (2^b) (2^c) v w := by
  have hp : (4:ℤ)≤2^(a-b) := dyadic_four (a-b) (by omega)
  have et := dyadic_split a b (by omega)
  by_cases he : c=b
  · subst c
    rw [et]
    exact ascending_equal (2^(a-b)) (2^b) hp (dyadic_four b hb)
  · by_cases he : c=b+1
    · have ez : (2:ℤ)^c=2*2^b := by rw [he,pow_succ]; ring
      have eq : (2:ℤ)^a=2*2^(a-c)*2^b := by
        rw [dyadic_split a c (by omega),ez]; ring
      rw [eq,ez]
      exact ascending_twice (2^(a-c)) (2^b)
        (by simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤a-c by omega))
        (dyadic_four b hb)
    · have eq : (4:ℤ)≤2^(c-b) := dyadic_four (c-b) (by omega)
      have ep : 2*(2:ℤ)^(c-b)≤2^(a-b) := by
        have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show c-b+1≤a-b by omega)
        simpa [pow_succ,mul_comm] using h
      rw [et,dyadic_split c b hbc]
      exact ascending_separated (2^(a-b)) (2^(c-b)) (2^b) eq ep (dyadic_four b hb)

private theorem descending_allocate (a b c : ℕ) (hc : 2≤c) (hcb : c<b) (hba : b+2≤a) :
    ∃ v w : ℤ, Stock false (2^a) (2^b) (2^c) v w ∧
      Gates false (2^a) (2^b) (2^c) v w := by
  have et : (2:ℤ)^a=2^(a-b)*2^(b-c)*2^c := by
    rw [dyadic_split a b (by omega),dyadic_split b c (by omega)]; ring
  rw [et,dyadic_split b c (by omega)]
  exact descending_wide (2^(a-b)) (2^(b-c)) (2^c)
    (dyadic_four (a-b) (by omega))
    (by simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤b-c by omega))
    (dyadic_four c hc)

end D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
