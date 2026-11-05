/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/LargeP
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/LargeP
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded a2 second peak LargeP construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallWindows
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.LargePContinuous

/-! All-h large-p construction for the unchanged A2 rows. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private basic_positive from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Algebra

open private continuous_cover_all continuous_parameter_bounds_all
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.LargePContinuous

private theorem large_geometry_all (p q h : ℤ) (hp : 64≤p) (hq : 2≤q)
    (hh : 1≤h) :
    31*h*L p q<K p q h ∧ 2*K p q h+A p q h<t p q*A p q h ∧
      62*h<y p q h := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ p=u+64 := ⟨p-64,by omega,by ring⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ q=w+2 := ⟨q-2,by omega,by ring⟩
  obtain ⟨hshift,hhshift,rfl⟩ : ∃ hshift : ℤ, 0≤hshift ∧ h=hshift+1 := ⟨h-1,by omega,by ring⟩
  refine ⟨?_,?_,?_⟩
  all_goals
    apply lt_of_sub_pos
    dsimp [A,K,L,t,y,SecondPeakHighD.A,SecondPeakHighD.K,
      SecondPeakHighD.L,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
    ring_nf
    positivity

private theorem integer_consumer_bounds_all (p q h : ℤ) (hp : 64≤p) (hq : 16≤q)
    (hh : 1≤h) :
    0<D p q h ∧ 0≤1+60*h*Q q ∧
    16*(1+60*h*Q q)≤D p q h ∧ 13*D p q h≤A p q h := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ p=u+64 := ⟨p-64,by omega,by ring⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ q=w+16 := ⟨q-16,by omega,by ring⟩
  obtain ⟨hshift,hhshift,rfl⟩ : ∃ hshift : ℤ, 0≤hshift ∧ h=hshift+1 := ⟨h-1,by omega,by ring⟩
  refine ⟨?_,?_,?_,?_⟩
  · apply lt_of_sub_pos
    dsimp [D,A,L,Q,SecondPeakHighD.A,SecondPeakHighD.L,
      SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
    ring_nf
    positivity
  all_goals
    apply le_of_sub_nonneg
    dsimp [D,A,L,Q,SecondPeakHighD.A,SecondPeakHighD.L,
      SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
    ring_nf
    positivity

private theorem core_to_first_all (p q h v m e : ℤ) (hp : 64≤p) (hq : 2≤q)
    (hh : 1≤h) (hm : 0≤m) (hm' : m≤31*h)
    (he : 4≤e) (hem : 1+4*m*Q q≤e)
    (hc : (e≤8*R p q h v m ∧ 8*R p q h v m≤A p q h-e) ∨
      (3*A p q h+e≤8*R p q h v m ∧ 8*R p q h v m≤4*A p q h-e)) :
    ∃ before : Bool, First p q h v m before := by
  have hmy : 2*m<y p q h := by have := (large_geometry_all p q h hp hq hh).2.2; omega
  have hQ : 0≤Q q := by dsimp [Q]; omega
  rcases hc with hc|hc
  · exact ⟨true,first_of_exact p q h v m true (by omega) hq (by omega) hm hmy
      ⟨by omega,by have := mul_nonneg hm hQ; nlinarith [hc.2]⟩⟩
  · exact ⟨false,first_of_exact p q h v m false (by omega) hq (by omega) hm hmy
      ⟨by omega,by omega⟩⟩

private theorem large_first_integer_all (p q h : ℤ) (hp : 64≤p) (hq : 16≤q)
    (hh : 1≤h) :
    ∃ v m : ℤ, ∃ before : Bool, 0≤m ∧ m≤31*h ∧ First p q h v m before := by
  obtain ⟨hD,he,heD,hDA⟩ := integer_consumer_bounds_all p q h hp hq hh
  obtain ⟨j,v,hj,hj',hc⟩ := sixteen_step_cover (A p q h) (D p q h)
    (1+60*h*Q q) (-8*K p q h) hD he heD hDA
  have hm : 0≤h*j := mul_nonneg (by omega) hj
  have hm' : h*j≤31*h := by
    calc
      h*j≤h*31 := mul_le_mul_of_nonneg_left (by omega) (by omega)
      _=31*h := by ring
  have hQ : 0≤Q q := by dsimp [Q]; omega
  have hem : 1+4*(h*j)*Q q≤1+60*h*Q q := by
    have hj15 : 0≤15-j := by omega
    have hprod := mul_nonneg (by omega : 0≤h) (mul_nonneg hj15 hQ)
    nlinarith only [hprod]
  have hid : -8*K p q h+j*(5*A p q h-D p q h)+8*v*A p q h=
      8*R p q h v (h*j) := by dsimp [D,R]; ring
  rw [hid] at hc
  obtain ⟨before,hbefore⟩ := core_to_first_all p q h v (h*j) (1+60*h*Q q)
    hp (by omega) hh hm hm' (by
      have hq0 : 1≤Q q := by dsimp [Q]; omega
      have hh0 : 0≤h-1 := by omega
      nlinarith [mul_nonneg (show 0≤Q q by omega) hh0]) hem hc
  exact ⟨v,h*j,before,hm,hm',hbefore⟩

private theorem large_first_rational_all (p q h : ℤ) (hp : 64≤p)
    (hq : q=2 ∨ q=4 ∨ q=8) (hh : 1≤h) :
    ∃ v m : ℤ, ∃ before : Bool, 0≤m ∧ m≤31*h ∧ First p q h v m before := by
  have hq2 : 2≤q := by omega
  have hA : 0<A p q h := (basic_positive p q h (by omega) hq2 (by omega)).1
  have h8A : 0<8*A p q h := by omega
  let r := (-8*K p q h) % (8*A p q h)
  let n := (-8*K p q h) / (8*A p q h)
  have hr : 0≤r := Int.emod_nonneg _ (by omega)
  have hr' : r<8*A p q h := Int.emod_lt_of_pos _ h8A
  have hdiv : r+8*A p q h*n = -8*K p q h := Int.emod_add_mul_ediv _ _
  let eps : ℚ := (D p q h:ℚ)/(8*(A p q h:ℚ))
  let e : ℤ := 1+124*h*Q q
  let eta : ℚ := (e:ℚ)/(8*(A p q h:ℚ))
  let x : ℚ := (r:ℚ)/(8*(A p q h:ℚ))
  have hden : (0:ℚ)<8*(A p q h:ℚ) := by exact_mod_cast h8A
  obtain ⟨hel,heu,het⟩ := continuous_parameter_bounds_all p q h hp hq hh
  have hz : (4*(q:ℚ))=8 ∨ (4*(q:ℚ))=16 ∨ (4*(q:ℚ))=32 := by
    rcases hq with rfl|rfl|rfl <;> norm_num
  obtain ⟨j,second,s,hj,hlo,hhi⟩ := continuous_cover_all (4*q) eps eta x hz hel heu het
    (div_nonneg (by exact_mod_cast hr) hden.le)
    (by
      apply (div_le_iff₀ hden).2
      simpa only [one_mul] using (show (r:ℚ)≤8*(A p q h:ℚ) by exact_mod_cast hr'.le))
  let v := -n-s
  let m := h*j
  have hm : 0≤m := by dsimp [m]; positivity
  have hm' : m≤31*h := by
    calc
      m=h*(j:ℤ) := rfl
      _≤h*31 := mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by omega)
      _=31*h := by ring
  have hid : ((8*R p q h v m:ℤ):ℚ)/(8*(A p q h:ℚ))=
      x+(j:ℚ)*(5/8-eps)-s := by
    have hd : (r:ℚ)+8*(A p q h:ℚ)*(n:ℚ) = -8*(K p q h:ℚ) := by exact_mod_cast hdiv
    dsimp [v,m,x,eps,D,R]
    push_cast
    field_simp [show (A p q h:ℚ)≠0 by exact_mod_cast (ne_of_gt hA)]
    nlinarith
  have heta : eta*(8*(A p q h:ℚ))=(e:ℚ) := by
    dsimp [eta]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hc : (e≤8*R p q h v m ∧ 8*R p q h v m≤A p q h-e) ∨
      (3*A p q h+e≤8*R p q h v m ∧ 8*R p q h v m≤4*A p q h-e) := by
    rw [←hid] at hlo hhi
    push_cast at hlo hhi
    cases hs : second
    · left
      simp only [hs,Bool.false_eq_true,ite_false,ite_true] at hlo hhi
      have hl : (e:ℚ)≤8*(R p q h v m:ℚ) := by
        change (e:ℚ)/(8*(A p q h:ℚ))≤_ at hlo
        exact (div_le_div_iff_of_pos_right hden).mp hlo
      have hu : (8*R p q h v m:ℚ)≤(1/8-eta)*(8*(A p q h:ℚ)) :=
        (div_le_iff₀ hden).mp hhi
      have hu' : (8*R p q h v m:ℚ)≤(A p q h:ℚ)-(e:ℚ) := by nlinarith [heta]
      exact ⟨by exact_mod_cast hl,by exact_mod_cast hu'⟩
    · right
      simp only [hs,Bool.false_eq_true,ite_false,ite_true] at hlo hhi
      have hl : (3/8+eta)*(8*(A p q h:ℚ))≤(8*R p q h v m:ℚ) :=
        (le_div_iff₀ hden).mp hlo
      have hu : (8*R p q h v m:ℚ)≤(1/2-eta)*(8*(A p q h:ℚ)) :=
        (div_le_iff₀ hden).mp hhi
      have hl' : 3*(A p q h:ℚ)+(e:ℚ)≤(8*R p q h v m:ℚ) := by nlinarith [heta]
      have hu' : (8*R p q h v m:ℚ)≤4*(A p q h:ℚ)-(e:ℚ) := by nlinarith [heta]
      exact ⟨by exact_mod_cast hl',by exact_mod_cast hu'⟩
  have hQ : 0≤Q q := by dsimp [Q]; omega
  have hem : 1+4*m*Q q≤e := by
    have hm31 : 0≤31*h-m := by omega
    have := mul_nonneg hm31 hQ
    dsimp [e]
    nlinarith
  obtain ⟨before,hf⟩ := core_to_first_all p q h v m e hp hq2 hh hm hm'
    (by have hq0 : 1≤Q q := by dsimp [Q]; omega
        have hh0 : 0≤h-1 := by omega
        nlinarith [mul_nonneg (show 0≤Q q by omega) hh0]) hem hc
  exact ⟨v,m,before,hm,hm',hf⟩

private theorem v_stock_all (p q h v m : ℤ) (before : Bool)
    (hp : 64≤p) (hq : 2≤q) (hh : 1≤h)
    (hm : 0≤m) (hm' : m≤31*h) (hf : First p q h v m before) :
    1≤v ∧ 2*v≤t p q := by
  obtain ⟨hKL,hTK,_⟩ := large_geometry_all p q h hp hq hh
  obtain ⟨hA,hL,_⟩ := basic_positive p q h (by omega) hq (by omega)
  have hm31 : 0≤31*h-m := by omega
  have hml := mul_nonneg hm31 hL.le
  have hml' := mul_nonneg hm hL.le
  dsimp [First,R] at hf
  constructor
  · by_contra hn
    have hvv : v≤0 := by omega
    have hprod := mul_nonpos_of_nonpos_of_nonneg hvv hA.le
    nlinarith [hf.1,hf.2.1]
  · by_contra hn
    have hvv : 0≤2*v-t p q := by omega
    have hprod := mul_nonneg hvv hA.le
    nlinarith [hf.1,hf.2.1]

private theorem round_block_dyadic (k w : ℕ) (hw : 512*(2^k)≤w) :
    ∃ M : ℕ, 31*(2^k)<M ∧
      (4*(2^k:ℤ)≤5*(M:ℤ)-(w:ℤ)) ∧
      (5*(M:ℤ)-(w:ℤ)<164*(2^k:ℤ)) ∧
      (∀ m : ℕ, m<32*(2^k) → SecondPeakHighD.Submask m M) := by
  let h : ℕ := 2^k
  let X : ℕ := w+4*h+5
  let B0 : ℕ := 160*h
  let n : ℕ := (X+B0-1)/B0
  let M : ℕ := 32*h*n-1
  have hh0 : 0<h := by dsimp [h]; positivity
  have hh : 1≤h := by omega
  have hB : 0<B0 := by dsimp [B0]; positivity
  have hX : 0<X := by dsimp [X]; omega
  have hdecomp : B0*n + (X+B0-1)%B0 = X+B0-1 := by
    dsimp [n]
    simpa [Nat.add_comm] using (Nat.mod_add_div (X+B0-1) B0)
  have hrem : (X+B0-1)%B0 < B0 := Nat.mod_lt _ hB
  have hceillo : X≤B0*n := by omega
  have hceilhi : B0*n<X+B0 := by omega
  have hn : 1≤n := by
    apply Nat.pos_of_ne_zero
    intro hn0
    have hbad : X≤0 := by simpa only [hn0,mul_zero] using hceillo
    omega
  have hn0 : 0<n := by omega
  have hprod : 0<32*h*n := by positivity
  have hMsucc : M+1=32*h*n := by dsimp [M]; omega
  have hMcast : (M:ℤ)=32*(h:ℤ)*n-1 := by
    have he : (M:ℤ)+1=32*(h:ℤ)*n := by exact_mod_cast hMsucc
    omega
  have hceilLoZ : (w:ℤ)+4*h+5≤160*(h:ℤ)*n := by
    dsimp [B0,X] at hceillo
    exact_mod_cast hceillo
  have hceilHiZ : 160*(h:ℤ)*n<(w:ℤ)+4*h+5+160*h := by
    dsimp [B0,X] at hceilhi
    exact_mod_cast hceilhi
  have hlo : 4*(h:ℤ)≤5*(M:ℤ)-(w:ℤ) := by rw [hMcast]; nlinarith only [hceilLoZ]
  have hhi : 5*(M:ℤ)-(w:ℤ)<164*(h:ℤ) := by rw [hMcast]; nlinarith only [hceilHiZ]
  refine ⟨M,?_,by simpa only [h,Nat.cast_pow,Nat.cast_ofNat] using hlo,
    by simpa only [h,Nat.cast_pow,Nat.cast_ofNat] using hhi,?_⟩
  · have hwZ : 512*(h:ℤ)≤w := by exact_mod_cast hw
    have hhZ : 1≤(h:ℤ) := by exact_mod_cast hh
    have hmZ : 31*(h:ℤ)<M := by omega
    exact_mod_cast hmZ
  · intro m hm
    have hpow : 32*h=2^(k+5) := by
      simp [h,pow_add,Nat.mul_comm]
    rw [hpow] at hm
    simpa only [M,hpow] using SecondPeakHighD.submask_predecessor (k+5) n m hn hm

/-- The selector's three rows and stock bounds give the physical four-row
predicate. The missing fourth row has zero endpoints but positive heads. -/
private theorem good_of_row_bounds (p q h v m M : ℕ) (before : Bool)
    (hsub : SecondPeakHighD.Submask m M) (hmM : m<M)
    (hbounds : SecondPeakHighD.rowBounds 4 p q h v m M before) :
    SecondPeakA2.Good p q h v m M before := by
  obtain ⟨hrows,hv0,hv,hM0,hM⟩ := hbounds
  have hv0N : 1≤v := by exact_mod_cast hv0
  have hvN : 2*v≤4*p*q := by
    change 2*(v:ℤ)≤4*(p:ℤ)*q at hv
    exact_mod_cast hv
  have hMN : 2*M<8*h*p*q := by
    have evenY : SecondPeakHighD.Y 4 (p:ℤ) q h=
        2*((h:ℤ)*SecondPeakHighD.T 4 (p:ℤ) q) := by
      dsimp [SecondPeakHighD.Y]
      ring
    have hstrict : 2*(M:ℤ)<SecondPeakHighD.Y 4 (p:ℤ) q h := by
      rw [evenY] at hM ⊢
      omega
    have hMi : 2*(M:ℤ)<8*(h:ℤ)*p*q := by
      dsimp [SecondPeakHighD.Y,SecondPeakHighD.T] at hstrict
      nlinarith only [hstrict]
    exact_mod_cast hMi
  have hL : 1≤SecondPeakHighD.L 4 (p:ℤ) q := by
    apply le_of_sub_nonneg
    dsimp [SecondPeakHighD.L,SecondPeakHighD.Z,SecondPeakHighD.T]
    ring_nf
    positivity
  have hSV : 1≤SecondPeakHighD.SV 4 (p:ℤ) q := by
    apply le_of_sub_nonneg
    dsimp [SecondPeakHighD.SV,SecondPeakHighD.L,
      SecondPeakHighD.Z,SecondPeakHighD.T]
    ring_nf
    positivity
  refine ⟨hv0N,hvN,hmM,hMN,hsub,?_⟩
  intro r
  fin_cases r
  · have hr := hrows 0
    exact ⟨⟨hr.1,hr.2.1⟩,hr.2.2⟩
  · have hr := hrows 1
    exact ⟨⟨hr.1,hr.2.1⟩,hr.2.2⟩
  · have hr := hrows 2
    exact ⟨⟨hr.1,hr.2.1⟩,hr.2.2⟩
  · simpa [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,
        SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads] using
      (show (0≤(0:ℤ) ∧ 0≤SecondPeakHighD.L 4 (p:ℤ) q-1) ∧
        (0≤(0:ℤ) ∧ 0≤SecondPeakHighD.SV 4 (p:ℤ) q-1) by omega)

/-- The original first identities retain the late-fresh subtraction of 2A. -/
private theorem first_small_slacks (p q h v m M : ℤ) (before : Bool)
    (hf : First p q h v m before) :
    ∀ r : Fin 4, 0≤smallFirstSlacks p q h v m M before r := by
  have eo : SecondPeakHighD.oldEnds 4 p q h v m M 0=2*R p q h v m := by
    dsimp [SecondPeakHighD.oldEnds,R]
    ring
  have en : SecondPeakHighD.newEnds 4 p q h v m M before 0=
      4*R p q h v m+2*((y p q h-m)*Q q+1)-
        (if before then 0 else 2*A p q h) := by
    cases before <;> dsimp [SecondPeakHighD.newEnds,R,A,L,K,SW,SV,y,Q,
      SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.K,
      SecondPeakHighD.SW,SecondPeakHighD.SV,SecondPeakHighD.Z,
      SecondPeakHighD.T,SecondPeakHighD.Y] <;> ring
  intro r
  fin_cases r
  · change 0≤SecondPeakHighD.oldEnds 4 p q h v m M 0
    rw [eo]
    exact hf.1
  · change 0≤A p q h-1-SecondPeakHighD.oldEnds 4 p q h v m M 0
    rw [eo]
    exact sub_nonneg.mpr hf.2.1
  · change 0≤SecondPeakHighD.newEnds 4 p q h v m M before 0
    rw [en]
    exact hf.2.2.1
  · change 0≤A p q h-1-SecondPeakHighD.newEnds 4 p q h v m M before 0
    rw [en]
    exact sub_nonneg.mpr hf.2.2.2

/-- Complete p>=64 sector, including the three continuous small-z covers. -/
private theorem large_p_allh_good (p q k : ℕ) (hp : 64≤p) (hq : 2≤q) (hk : 2≤k)
    (hqs : q=2 ∨ q=4 ∨ q=8 ∨ 16≤q) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p q (2^k) v m M before := by
  let h : ℕ := 2^k
  have hh4 : 4≤h := by
    dsimp [h]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) hk)
  have hhN : 1≤h := by omega
  change ∃ v m M : ℕ, ∃ before : Bool, Good p q h v m M before
  have hpi : (64:ℤ)≤p := by exact_mod_cast hp
  have hqi : (2:ℤ)≤q := by exact_mod_cast hq
  have hhi : (h:ℤ)≥1 := by exact_mod_cast hhN
  have first : ∃ v m : ℤ, ∃ before : Bool,
      0≤m ∧ m≤31*(h:ℤ) ∧ First p q h v m before := by
    rcases hqs with rfl|rfl|rfl|hq16
    · exact large_first_rational_all p 2 h hpi (Or.inl rfl) hhi
    · exact large_first_rational_all p 4 h hpi (Or.inr (Or.inl rfl)) hhi
    · exact large_first_rational_all p 8 h hpi (Or.inr (Or.inr rfl)) hhi
    · exact large_first_integer_all p q h hpi (by exact_mod_cast hq16) hhi
  obtain ⟨v,m,before,hm,hm',hf⟩ := first
  have hv := v_stock_all p q h v m before hpi hqi hhi hm hm' hf
  lift v to ℕ using (by omega : 0≤v)
  lift m to ℕ using hm
  let w := 8*h*p*(q-1)
  have hw : 512*h≤w := by
    have hmul : 64≤p*(q-1) := le_trans hp (by
      simpa using Nat.mul_le_mul_left p (show 1≤q-1 by omega))
    calc
      512*h=8*h*64 := by ring
      _≤8*h*(p*(q-1)) := Nat.mul_le_mul_left _ hmul
      _=w := by dsimp [w]; ring
  obtain ⟨M,hM,hlo,hhi',hsub⟩ := round_block_dyadic k w hw
  have hhcast : (h:ℤ)=2^k := by simp [h]
  rw [←hhcast] at hlo hhi'
  have heq : (w:ℤ)=y p q h-8*(h:ℤ)*p := by
    dsimp [w,y]
    rw [Nat.cast_sub (by omega : 1≤q)]
    push_cast
    ring
  rw [heq] at hlo hhi'
  have hupper : 5*(M:ℤ)-(y p q h-8*(h:ℤ)*p)≤4*(h:ℤ)*p := by
    have hprod := mul_nonneg (show 0≤(h:ℤ) by omega) (show 0≤(p:ℤ)-41 by omega)
    nlinarith only [hhi',hprod]
  have hy : SecondPeakHighD.Y 4 (p:ℤ) q h=y p q h := by
    dsimp [SecondPeakHighD.Y,SecondPeakHighD.T,y]
    ring
  have hb : SecondPeakHighD.rowBounds 4 p q h v m M before :=
    finish_small_bounds p q h v m M before (by omega) hqi
      (by exact_mod_cast hh4) hv.1
      (by simpa only [t,SecondPeakHighD.T] using hv.2)
      (by simpa only [smallDelta,hy] using hlo)
      (by simpa only [smallDelta,hy] using hupper)
      (first_small_slacks p q h v m M before hf)
  refine ⟨v,m,M,before,good_of_row_bounds p q h v m M before ?_ ?_ hb⟩
  · apply hsub
    have : m≤31*h := by exact_mod_cast hm'
    omega
  · have : m≤31*h := by exact_mod_cast hm'
    omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
