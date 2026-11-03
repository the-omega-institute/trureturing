import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Selection

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open private ceilDiv ceilDiv_spec ceilDiv_unique ceilDiv_stock residual_identity windows_of_residual
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
open private common_bounds continuous_second_bound
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Selection
open private high_periodic_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Selection

/-- Continuous second-window proof after the integer ceiling has been bounded.
The stock and ceiling hypotheses here are the input interface of the rounding
lemma, not hypotheses of a claimed original-domain physical endpoint. -/
private theorem high_continuous_windows (x z q m : ℚ)
    (hx : 4≤x) (hz : 2*x≤z) (hq : 16≤q)
    (hlarge : 32≤q ∨ (8≤x ∧ 16≤q))
    (hm : 0≤m) (hstock : m≤q*z/2-1)
    (he : 0≤E x z q 0 m) (hecap : E x z q 0 m≤L x z-1) :
    Windows x z q 0 m := by
  have hc := common_bounds x z q hx hz (by linarith)
  have hbound := continuous_second_bound x z q hx hz hlarge
  have hz0 : 0≤z := by linarith
  have hy : 0≤q*z := mul_nonneg (by linarith) hz0
  have hleft : 0≤q*z-m := by linarith
  have hprod : 0≤(q*z-m)*(z+1) := mul_nonneg hleft (by linarith)
  have hsub : 0≤m*(z+1) := mul_nonneg hm (by linarith)
  have hidentity := residual_identity x z q 0 m
  simp only [sub_zero] at hidentity
  have hf : 0≤F x z q 0 m := by linarith
  have hfcap : 2*F x z q 0 m≤A x z q-1 := by nlinarith
  have hecap' : 2*E x z q 0 m≤A x z q-1 := by linarith
  have hr : Residual x z q 0 m := by
    obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hc
    refine ⟨hm,by linarith,he,by linarith,by linarith,hf,by linarith,?_,?_⟩
    · simpa using h4
    · simpa using h5
  exact windows_of_residual x z q 0 m hx hz (by linarith) hc le_rfl hr

/-- The discrete arithmetic used by every proposed low-b mask, with no guessed ceil. -/
private theorem exact_ceiling_of_residual (BB KK LL vv mm : ℤ)
    (hL : 0<LL) (he : 0≤(vv+1)*BB-KK+mm*LL)
    (hc : (vv+1)*BB-KK+mm*LL≤LL-1) :
    mm=ceilDiv (KK-(vv+1)*BB) LL := by
  apply ceilDiv_unique _ _ _ hL <;> linarith

/-- A bounded ceiling exists on the common domain, using integer heads and stock. -/
private theorem bounded_ceiling (D LL stock : ℤ) (hL : 0<LL)
    (hD : 0<D) (hstock : D≤stock*LL) :
    ∃ mm : ℤ, 1≤mm ∧ mm≤stock ∧ 0≤mm*LL-D ∧ mm*LL-D≤LL-1 ∧
      mm=ceilDiv D LL := by
  obtain ⟨hlo,hhi⟩ := ceilDiv_stock D LL stock hL hD hstock
  obtain ⟨he,hec⟩ := ceilDiv_spec D LL hL
  exact ⟨ceilDiv D LL,hlo,hhi,he,hec,rfl⟩

/-! The integer ceiling is now consumed by the actual window interface.  The
three equalities below are deliberately explicit: they are the bridge from
the integer source heads to the rational polynomial notation used by the
certificate families. -/
private theorem continuous_integer_windows
    (x z q : ℚ) (D LL stock : ℤ)
    (hx : 4≤x) (hz : 2*x≤z) (hq : 16≤q)
    (hlarge : 32≤q ∨ (8≤x ∧ 16≤q))
    (hD : (D:ℚ)=K z q-B x z q) (hLL : (LL:ℚ)=L x z)
    (hstock : (D:ℚ)≤(stock:ℚ)*(LL:ℚ))
    (hstockcap : (stock:ℚ)≤q*z/2-1)
    (hDpos : 0<D) (hLLpos : 0<LL) :
    ∃ m : ℤ, 0≤m ∧ m≤stock ∧ Windows x z q 0 (m:ℚ) := by
  obtain ⟨m,hm1,hmstock,hme,hmec,hmceil⟩ :=
    bounded_ceiling D LL stock hLLpos hDpos hstock
  have hm0 : 0≤(m:ℚ) := by exact_mod_cast (show 0≤m by omega)
  have hms : (m:ℚ)≤q*z/2-1 := by
    have hs : m≤stock := hmstock
    have hsQ : (m:ℚ)≤(stock:ℚ) := by exact_mod_cast hs
    linarith
  have he : 0≤E x z q 0 (m:ℚ) := by
    rw [hD] at *
    dsimp [E]
    linarith
  have hecap : E x z q 0 (m:ℚ)≤L x z-1 := by
    rw [hD,hLL] at *
    dsimp [E]
    linarith
  refine ⟨m,by omega,hmstock,?_⟩
  exact high_continuous_windows x z q (m:ℚ) hx hz hq hlarge hm0 hms he hecap

private theorem periodic_integer_windows (x z : ℚ) (m : ℤ)
    (hx : x=4) (hz : 8≤z)
    (hm : HighResidual z (m:ℚ)) : Windows x z 16 0 (m:ℚ) := by
  have hc := common_bounds x z 16 (by linarith [show (0:ℚ)≤z by positivity])
      (by linarith) (by norm_num)
  obtain ⟨hm0,hmstock,he,hec,heo,hf,hfo⟩ := hm
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hc
  have hr : Residual x z 16 0 (m:ℚ) := by
    subst x
    refine ⟨hm0,by linarith,he,hec,heo,hf,hfo,?_,?_⟩
    · simpa [SU,SV,SW] using h4
    · simpa [SU,SV,SW] using h5
  exact windows_of_residual x z 16 0 (m:ℚ) (by norm_num)
    (by linarith [show (0:ℚ)≤z by positivity]) (by norm_num) hc
    (by norm_num) hr

private theorem high_integer_selection (a b c : ℕ)
    (ha : 2≤a) (hac : a<c) (hcb4 : c+4≤b) :
    ∃ m : ℤ, 0≤m ∧ m≤(2:ℤ)^(b-1)-1 ∧
      Windows ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c)) 0 (m:ℚ) := by
  let xI : ℤ := 2^a
  let zI : ℤ := 2^c
  let qI : ℤ := 2^(b-c)
  let DI : ℤ := (1+qI*zI+(qI*zI)*zI+2*(qI*zI)*zI^2) -
    (1+xI+xI*(qI*zI)+xI*(qI*zI)*zI)
  let LI : ℤ := 1+zI+2*zI^2*(1+xI)
  let SI : ℤ := 2^(b-1)-1
  have hx : (4:ℚ)≤(2:ℚ)^a := by exact_mod_cast (show (4:ℤ)≤xI by dsimp [xI]; exact pow_le_pow_right₀ (by norm_num) ha)
  have hz : 2*(2:ℚ)^a≤(2:ℚ)^c := by exact_mod_cast (show 2*xI≤zI by dsimp [xI,zI]; exact pow_le_pow_right₀ (by norm_num) (by omega))
  have hq : (16:ℚ)≤(2:ℚ)^(b-c) := by exact_mod_cast (show (16:ℤ)≤qI by dsimp [qI]; exact pow_le_pow_right₀ (by norm_num) (by omega))
  have hD : (DI:ℚ)=K ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c))-
      B ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c)) := by
    dsimp [DI,K,B,xI,zI,qI]
    push_cast
    rw [← pow_add,← pow_add]
    ring
  have hL : (LI:ℚ)=L ((2:ℚ)^a) ((2:ℚ)^c) := by
    dsimp [LI,L,xI,zI]
    push_cast
    ring
  have hstockcap : (SI:ℚ)=(2:ℚ)^(b-c)*(2:ℚ)^c/2-1 := by
    dsimp [SI]
    rw [show b=(b-1)+1 by omega,show (2:ℚ)^((b-c)+c)=(2:ℚ)^b by rw [← pow_add]; congr 1 <;> omega]
    norm_num
  have hcommon := common_bounds ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c)) hx hz (by linarith)
  have hDpos : 0<DI := by
    have hh := hcommon.2.2.2.2.2.1
    rw [hD] at hh
    exact_mod_cast (show (0:ℚ)<K ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c))-
      B ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c)) by linarith)
  have hLpos : 0<LI := by
    dsimp [LI]
    positivity
  by_cases hcont : 32≤(2:ℚ)^(b-c) ∨ ((8:ℚ)≤(2:ℚ)^a ∧ 16≤(2:ℚ)^(b-c))
  · have hstock : (DI:ℚ)≤(SI:ℚ)*(LI:ℚ) := by
      have hh := hcommon.2.2.2.2.2.2
      rw [hD,hL,hstockcap] at hh
      linarith
    obtain ⟨m,hm1,hmstock,hw⟩ := continuous_integer_windows ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^(b-c))
      DI LI SI hx hz hq hcont hD hL hstock hstockcap hDpos hLpos
    exact ⟨m,by omega,hmstock,hw⟩
  · have ha2 : a=2 := by
      by_contra hne
      have ha8 : (8:ℚ)≤(2:ℚ)^a := by exact_mod_cast (show (8:ℤ)≤xI by dsimp [xI]; exact pow_le_pow_right₀ (by norm_num) (by omega))
      omega
    have hq16 : b=c+4 := by
      have : (b-c)=4 := by omega
      omega
    subst a
    subst b
    obtain ⟨m,hm⟩ := high_periodic_selection c (by omega)
    have hmb : m≤(2:ℤ)^(b-1)-1 := by
      have hh := hm.2
      omega
    exact ⟨m,hm.1,hmb,periodic_integer_windows (2:ℚ) ((2:ℚ)^c) m rfl
      (by exact_mod_cast (show (8:ℤ)≤(2:ℤ)^c by exact pow_le_pow_right₀ (by norm_num) (by omega))) hm⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
