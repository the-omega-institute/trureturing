/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Large
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Large and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.ContinuousCover

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private basic_positive from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Algebra

theorem large_geometry (p q h : ℤ) (hp : 64≤p) (hq : 2≤q)
    (hh : h=1 ∨ h=2) :
    31*h*L p q<K p q h ∧ 2*K p q h+A p q h<t p q*A p q h ∧
    62*h<y p q h := by
  have hp0 : 0≤p-64 := by omega
  have hq0 : 0≤q-2 := by omega
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ p=u+64 := ⟨p-64,hp0,by ring⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ q=w+2 := ⟨q-2,hq0,by ring⟩
  rcases hh with rfl|rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals apply lt_of_sub_pos
  all_goals dsimp [A,L,K,t,y,SecondPeakHighD.A,SecondPeakHighD.L,
    SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring_nf
  all_goals positivity

theorem integer_consumer_bounds (p q h : ℤ) (hp : 64≤p) (hq : 16≤q)
    (hh : h=1 ∨ h=2) :
    0<D p q h ∧ 0≤1+60*h*Q q ∧
    16*(1+60*h*Q q)≤D p q h ∧ 13*D p q h≤A p q h := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ p=u+64 := ⟨p-64,by omega,by ring⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ q=w+16 := ⟨q-16,by omega,by ring⟩
  rcases hh with rfl|rfl
  all_goals refine ⟨?_,?_,?_,?_⟩
  all_goals first
    | (apply le_of_sub_nonneg)
    | (apply lt_of_sub_pos)
  all_goals dsimp [D,A,L,Q,SecondPeakHighD.A,SecondPeakHighD.L,
    SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring_nf
  all_goals positivity

private theorem core_to_first (p q h v m e : ℤ) (hp : 64≤p) (hq : 2≤q)
    (hh : h=1 ∨ h=2) (hm : 0≤m) (hm' : m≤31*h)
    (he : 4≤e) (hem : 1+4*m*Q q≤e)
    (hc : (e≤8*R p q h v m ∧ 8*R p q h v m≤A p q h-e) ∨
      (3*A p q h+e≤8*R p q h v m ∧ 8*R p q h v m≤4*A p q h-e)) :
    ∃ before : Bool, First p q h v m before := by
  have hmy : 2*m<y p q h := by have := (large_geometry p q h hp hq hh).2.2; omega
  have hQ : 0≤Q q := by dsimp [Q]; omega
  rcases hc with hc|hc
  · exact ⟨true,first_of_exact p q h v m true (by omega) hq (by omega) hm hmy
      ⟨by omega,by have := mul_nonneg hm hQ; nlinarith [hc.2]⟩⟩
  · exact ⟨false,first_of_exact p q h v m false (by omega) hq (by omega) hm hmy
      ⟨by omega,by omega⟩⟩

private theorem large_first_integer (p q h : ℤ) (hp : 64≤p) (hq : 16≤q)
    (hh : h=1 ∨ h=2) :
    ∃ v m : ℤ, ∃ before : Bool, 0≤m ∧ m≤31*h ∧ First p q h v m before := by
  obtain ⟨hD,he,heD,hDA⟩ := integer_consumer_bounds p q h hp hq hh
  obtain ⟨j,v,hj,hj',hc⟩ := sixteen_step_cover (A p q h) (D p q h)
    (1+60*h*Q q) (-8*K p q h) hD he heD hDA
  have hm : 0≤h*j := mul_nonneg (by omega) hj
  have hm' : h*j≤31*h := by
    calc
      h*j≤h*31 := mul_le_mul_of_nonneg_left (by omega) (by omega)
      _=31*h := by ring
  have hQ : 0≤Q q := by dsimp [Q]; omega
  have hem : 1+4*(h*j)*Q q≤1+60*h*Q q := by
    have := mul_nonneg (show 0≤15-j by omega) hQ
    rcases hh with rfl|rfl <;> nlinarith
  have hid : -8*K p q h+j*(5*A p q h-D p q h)+8*v*A p q h=
      8*R p q h v (h*j) := by dsimp [D,R]; ring
  rw [hid] at hc
  obtain ⟨before,hbefore⟩ := core_to_first p q h v (h*j) (1+60*h*Q q)
    hp (by omega) hh hm hm' (by rcases hh with rfl|rfl <;> dsimp [Q] <;> omega) hem hc
  exact ⟨v,h*j,before,hm,hm',hbefore⟩

private theorem large_first_rational (p q h : ℤ) (hp : 64≤p)
    (hq : q=2 ∨ q=4 ∨ q=8) (hh : h=1 ∨ h=2) :
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
  obtain ⟨hel,heu,het⟩ := continuous_parameter_bounds p q h hp hq hh
  have hz : (4*(q:ℚ))=8 ∨ (4*(q:ℚ))=16 ∨ (4*(q:ℚ))=32 := by
    rcases hq with rfl|rfl|rfl <;> norm_num
  obtain ⟨j,second,s,hj,hlo,hhi⟩ := continuous_cover (4*q) eps eta x hz hel heu het
    (div_nonneg (by exact_mod_cast hr) hden.le)
    (by
      apply (div_le_iff₀ hden).2
      simpa only [one_mul] using (show (r:ℚ)≤8*(A p q h:ℚ) by exact_mod_cast hr'.le))
  let v := -n-s
  let m := h*j
  have hm : 0≤m := by dsimp [m]; exact mul_nonneg (by omega) (by positivity)
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
    cases hs : second
    · left
      simp only [hs,Bool.false_eq_true,ite_false] at hlo hhi
      have hl : (e:ℚ)≤(8*R p q h v m:ℤ) := by
        change (e:ℚ)/(8*(A p q h:ℚ))≤_ at hlo
        exact (div_le_div_iff_of_pos_right hden).mp hlo
      have hu : ((8*R p q h v m:ℤ):ℚ)≤(1/8-eta)*(8*(A p q h:ℚ)) :=
        (div_le_iff₀ hden).mp hhi
      have hu' : ((8*R p q h v m:ℤ):ℚ)≤(A p q h:ℚ)-(e:ℚ) := by nlinarith [heta]
      exact ⟨by exact_mod_cast hl,by exact_mod_cast hu'⟩
    · right
      simp only [hs,Bool.false_eq_true,ite_true] at hlo hhi
      have hl : (3/8+eta)*(8*(A p q h:ℚ))≤((8*R p q h v m:ℤ):ℚ) :=
        (le_div_iff₀ hden).mp hlo
      have hu : ((8*R p q h v m:ℤ):ℚ)≤(1/2-eta)*(8*(A p q h:ℚ)) :=
        (div_le_iff₀ hden).mp hhi
      have hl' : 3*(A p q h:ℚ)+(e:ℚ)≤((8*R p q h v m:ℤ):ℚ) := by nlinarith [heta]
      have hu' : ((8*R p q h v m:ℤ):ℚ)≤4*(A p q h:ℚ)-(e:ℚ) := by nlinarith [heta]
      exact ⟨by exact_mod_cast hl',by exact_mod_cast hu'⟩
  have hQ : 0≤Q q := by dsimp [Q]; omega
  have hem : 1+4*m*Q q≤e := by
    have := mul_nonneg (show 0≤31*h-m by omega) hQ
    dsimp [e]
    nlinarith
  obtain ⟨before,hf⟩ := core_to_first p q h v m e hp hq2 hh hm hm'
    (by rcases hh with rfl|rfl <;> dsimp [e,Q] <;> omega) hem hc
  exact ⟨v,m,before,hm,hm',hf⟩

private theorem v_stock (p q h v m : ℤ) (before : Bool)
    (hp : 64≤p) (hq : 2≤q) (hh : h=1 ∨ h=2)
    (hm : 0≤m) (hm' : m≤31*h) (hf : First p q h v m before) :
    1≤v ∧ 2*v≤t p q := by
  obtain ⟨hKL,hTK,_⟩ := large_geometry p q h hp hq hh
  obtain ⟨hA,hL,_⟩ := basic_positive p q h (by omega) hq (by omega)
  have hml := mul_nonneg (show 0≤31*h-m by omega) hL.le
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

private theorem round_block (h w : ℕ) (hh : h=1 ∨ h=2) (hw : 512*h≤w) :
    ∃ M : ℕ, 31*h<M ∧
      (2*(h:ℤ)≤5*(M:ℤ)-(w:ℤ)) ∧
      (5*(M:ℤ)-(w:ℤ)<162*(h:ℤ)) ∧
      (∀ m : ℕ, m<32*h → SecondPeakHighD.Submask m M) := by
  let n := (w+162*h+4)/(160*h)
  let M := 32*h*n-1
  have hn : 1≤n := by rcases hh with rfl|rfl <;> dsimp [n] <;> omega
  have hlo : 2*(h:ℤ)≤5*(M:ℤ)-(w:ℤ) := by
    rcases hh with rfl|rfl <;> dsimp [M,n] <;> omega
  have hhi : 5*(M:ℤ)-(w:ℤ)<162*(h:ℤ) := by
    rcases hh with rfl|rfl <;> dsimp [M,n] <;> omega
  refine ⟨M,?_,hlo,hhi,?_⟩
  · rcases hh with rfl|rfl <;> dsimp [M,n] <;> omega
  · intro m hm
    rcases hh with rfl|rfl
    · exact SecondPeakHighD.submask_predecessor 5 n m hn (by norm_num at hm ⊢; omega)
    · exact SecondPeakHighD.submask_predecessor 6 n m hn (by norm_num at hm ⊢; omega)

/-- Complete p>=64 sector, including the three continuous small-z covers. -/
theorem large_exists (p q h : ℕ) (hp : 64≤p) (hq : 2≤q)
    (hqs : q=2 ∨ q=4 ∨ q=8 ∨ 16≤q) (hh : h=1 ∨ h=2) :
    ∃ v m M : ℕ, ∃ before : Bool, Good p q h v m M before := by
  have hpi : (64:ℤ)≤p := by exact_mod_cast hp
  have hqi : (2:ℤ)≤q := by exact_mod_cast hq
  have hhi : (h:ℤ)=1 ∨ (h:ℤ)=2 := by omega
  have first : ∃ v m : ℤ, ∃ before : Bool,
      0≤m ∧ m≤31*(h:ℤ) ∧ First p q h v m before := by
    rcases hqs with rfl|rfl|rfl|hq16
    · exact large_first_rational p 2 h hpi (Or.inl rfl) hhi
    · exact large_first_rational p 4 h hpi (Or.inr (Or.inl rfl)) hhi
    · exact large_first_rational p 8 h hpi (Or.inr (Or.inr rfl)) hhi
    · exact large_first_integer p q h hpi (by exact_mod_cast hq16) hhi
  obtain ⟨v,m,before,hm,hm',hf⟩ := first
  have hv := v_stock p q h v m before hpi hqi hhi hm hm' hf
  lift v to ℕ using (by omega : 0≤v)
  lift m to ℕ using hm
  let w := 8*h*p*(q-1)
  have hw : 512*h≤w := by
    have hmul : 64≤p*(q-1) := le_trans hp (by nlinarith [Nat.mul_le_mul_left p (show 1≤q-1 by omega)])
    rcases hh with rfl|rfl <;> dsimp [w] <;> nlinarith
  obtain ⟨M,hM,hlo,hhi',hsub⟩ := round_block h w hh hw
  have heq : (w:ℤ)=y p q h-8*(h:ℤ)*p := by
    dsimp [w,y]
    push_cast [Nat.cast_sub (by omega : 1≤q)]
    ring
  rw [heq] at hlo hhi'
  have hupper : 5*(M:ℤ)-(y p q h-8*(h:ℤ)*p)≤4*(h:ℤ)*p := by nlinarith
  have hsecond := second_windows p q h M (by omega) hqi hhi hlo hupper
  refine ⟨v,m,M,before,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hv.1
  · dsimp [t] at hv
    exact_mod_cast hv.2
  · exact_mod_cast (show (m:ℤ)<M by omega)
  · dsimp [y] at hsecond
    exact_mod_cast hsecond.2.1
  · apply hsub
    have : m≤31*h := by exact_mod_cast hm'
    rcases hh with rfl|rfl <;> omega
  · exact windows_of_first p q h v m M before (by omega) hqi hhi hf hlo hupper

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
