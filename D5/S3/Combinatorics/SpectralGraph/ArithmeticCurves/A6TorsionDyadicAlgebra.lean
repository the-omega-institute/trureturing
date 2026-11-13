/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionDyadicAlgebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionDyadicAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact full dyadic duplication and triplication inputs for received torsion groups -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuadraticDescent
/-! Original complete S.torsion at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02,
Ma/Nikandish/Zhang. This is task-local alternative proof engineering for the full
received rational and quadratic torsion conclusions. Original reduction counts and
prime-to-p reduction argument remain source evidence; no proof hole is imported. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6TorsionDyadicAlgebra
open Polynomial
private instance : Fact (Nat.Prime 2):=⟨by decide⟩
private abbrev v (x : ℚ) : ℤ:=padicValRat 2 x
private theorem val_literal (n : ℤ) (k : ℕ) (a : ℤ)
    (he : n=2^k*a) (ha : ¬(2:ℤ)∣a) : v (n:ℚ)=(k:ℤ) := by
  have han : a≠0 := by intro h;simp [h] at ha
  have ha0 : padicValRat 2 (a:ℚ)=0 := by
    rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd ha]
    rfl
  dsimp [v]
  rw [he,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (by exact_mod_cast han),
    padicValRat.pow,ha0]
  have hv2 : padicValRat 2 (2:ℚ)=1 := by
    simpa only [Nat.cast_ofNat] using (padicValRat.self (p:=2) (by decide))
  rw [hv2]
  simp

@[simp] private theorem pv_1 : padicValRat 2 (1:ℚ)=0 :=
  val_literal (1) 0 (1) (by norm_num) (by norm_num)
@[simp] private theorem pv_2 : padicValRat 2 (2:ℚ)=1 :=
  val_literal (2) 1 (1) (by norm_num) (by norm_num)
@[simp] private theorem pv_3 : padicValRat 2 (3:ℚ)=0 :=
  val_literal (3) 0 (3) (by norm_num) (by norm_num)
@[simp] private theorem pv_4 : padicValRat 2 (4:ℚ)=2 :=
  val_literal (4) 2 (1) (by norm_num) (by norm_num)
@[simp] private theorem pv_5 : padicValRat 2 (5:ℚ)=0 :=
  val_literal (5) 0 (5) (by norm_num) (by norm_num)
@[simp] private theorem pv_6 : padicValRat 2 (6:ℚ)=1 :=
  val_literal (6) 1 (3) (by norm_num) (by norm_num)
@[simp] private theorem pv_8 : padicValRat 2 (8:ℚ)=3 :=
  val_literal (8) 3 (1) (by norm_num) (by norm_num)
@[simp] private theorem pv_12 : padicValRat 2 (12:ℚ)=2 :=
  val_literal (12) 2 (3) (by norm_num) (by norm_num)
@[simp] private theorem pv_20 : padicValRat 2 (20:ℚ)=2 :=
  val_literal (20) 2 (5) (by norm_num) (by norm_num)
@[simp] private theorem pv_neg2 : padicValRat 2 (-2:ℚ)=1 :=
  val_literal (-2) 1 (-1) (by norm_num) (by norm_num)
@[simp] private theorem pv_neg8 : padicValRat 2 (-8:ℚ)=3 :=
  val_literal (-8) 3 (-1) (by norm_num) (by norm_num)

private def VB (n : ℤ) (x : ℚ) : Prop:=x≠0 → n≤v x
private theorem vb_weaken {n m : ℤ} {x : ℚ} (h : VB m x) (hn : n≤m) : VB n x :=
  fun hx=>hn.trans (h hx)
private theorem vb_add {n : ℤ} {x y : ℚ} (hx : VB n x) (hy : VB n y) : VB n (x+y) := by
  intro hxy
  by_cases hx0 : x=0
  · simpa [hx0] using hy (by simpa [hx0] using hxy)
  by_cases hy0 : y=0
  · simpa [hy0] using hx hx0
  exact (le_min (hx hx0) (hy hy0)).trans (padicValRat.min_le_padicValRat_add hxy)
private theorem vb_neg {n : ℤ} {x : ℚ} (hx : VB n x) : VB n (-x) := by
  intro hn
  simpa only [v,padicValRat.neg] using hx (neg_ne_zero.mp hn)
private theorem vb_sub {n : ℤ} {x y : ℚ} (hx : VB n x) (hy : VB n y) : VB n (x-y) := by
  simpa only [sub_eq_add_neg] using vb_add hx (vb_neg hy)
private theorem vb_mul {n m : ℤ} {x y : ℚ} (hx : VB n x) (hy : VB m y) : VB (n+m) (x*y) := by
  intro hxy
  obtain ⟨hx0,hy0⟩:=mul_ne_zero_iff.mp hxy
  dsimp [v]
  rw [padicValRat.mul hx0 hy0]
  exact add_le_add (hx hx0) (hy hy0)
private theorem vb_pow {m : ℤ} {x : ℚ} (hx : VB m x) (n : ℕ) : VB ((n:ℤ)*m) (x^n) := by
  cases n with
  | zero => simp [VB,v]
  | succ n =>
    intro hn
    have hx0 : x≠0 := by intro hz;simp [hz] at hn
    dsimp [v]
    rw [padicValRat.pow x]
    exact mul_le_mul_of_nonneg_left (hx hx0) (by positivity)
private theorem vb_exact {n : ℤ} {x : ℚ} (h : v x=n) : VB n x := fun _=>le_of_eq h.symm
private theorem term_bound (A B c x : ℚ) (i j k : ℕ) (m vc : ℤ)
    (hA : v A=2) (hB : v B=0) (hc : v c=vc) (hx : VB m x) :
    VB (vc+2*i+k*m) (c*A^i*B^j*x^k) := by
  convert vb_mul (vb_mul (vb_mul (vb_exact hc) (vb_pow (vb_exact hA) i))
    (vb_pow (vb_exact hB) j)) (vb_pow hx k) using 1 <;> ring
private theorem dominant (a b : ℚ) (m : ℤ) (ha : a≠0) (hb : VB m b)
    (hv : v a<m) : a+b≠0 ∧ v (a+b)=v a := by
  by_cases hb0 : b=0
  · simp [hb0,ha]
  have hlt : v a<v b := hv.trans_le (hb hb0)
  have hn : a+b≠0 := by
    intro he
    have he' : b= -a := by linarith
    simp only [he',v,padicValRat.neg] at hlt
    omega
  exact ⟨hn,padicValRat.add_eq_of_lt hn ha hb0 hlt⟩

private theorem term_exact (A B c x : ℚ) (i j k : ℕ) (vc : ℤ)
    (hA : v A=2) (hB : v B=0) (hc : v c=vc)
    (hAn : A≠0) (hBn : B≠0) (hcn : c≠0) (hxn : x≠0) :
    v (c*A^i*B^j*x^k)=vc+2*i+k*v x := by
  dsimp [v]
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero hcn (pow_ne_zero i hAn)) (pow_ne_zero j hBn)) (pow_ne_zero k hxn),
    padicValRat.mul (mul_ne_zero hcn (pow_ne_zero i hAn)) (pow_ne_zero j hBn),
    padicValRat.mul hcn (pow_ne_zero i hAn),
    padicValRat.pow A,padicValRat.pow B,padicValRat.pow x]
  change v c+(i:ℤ)*v A+(j:ℤ)*v B+(k:ℤ)*v x=vc+2*i+k*v x
  rw [hc,hA,hB]
  ring

def cubic (A B x : ℚ) : ℚ:=x^3+A*x+B
def numerator (A B x : ℚ) : ℚ:=x^4-2*A*x^2-8*B*x+A^2
def psi3 (A B x : ℚ) : ℚ:=3*x^4+6*A*x^2+12*B*x-A^2
def quartic4 (A B x : ℚ) : ℚ:=
  x^6+5*A*x^4+20*B*x^3-5*A^2*x^2-4*A*B*x-8*B^2-A^3
def doubleX (A B x : ℚ) : ℚ:=numerator A B x/(4*cubic A B x)
def tripleX (A B x : ℚ) : ℚ:=x-8*cubic A B x*quartic4 A B x/(psi3 A B x)^2

/-- The entire scaled monic three-division quartic has no root modulo11. -/
theorem mod11_psi3_E (z : ZMod 11) : z^4+18*2*z^2+108*5*z-27*2^2≠0 := by
  revert z
  decide
/-- The same complete no-root statement for the actual received twist. -/
theorem mod11_psi3_twist (z : ZMod 11) : z^4+18*7*z^2+108*8*z-27*7^2≠0 := by
  revert z
  decide

private def monic3 (A B : ℤ) : Polynomial ℤ :=
  .X^4+(.C (18*A)*.X^2+.C (108*B)*.X+.C (-27*A^2))
private theorem monic3_monic (A B : ℤ) : (monic3 A B).Monic := by
  unfold monic3
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt_iff.mpr
  constructor
  · apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt_iff.mpr
    constructor
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by norm_num)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

private theorem psi3_no_root (A B : ℤ)
    (hmod : ∀ z : ZMod 11,z^4+18*(A:ZMod 11)*z^2+108*(B:ZMod 11)*z-27*(A:ZMod 11)^2≠0)
    (x : ℚ) : psi3 A B x≠0 := by
  intro he
  have hr : Polynomial.aeval (3*x) (monic3 A B)=0 := by
    simp only [monic3,map_add,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
    norm_num
    dsimp [psi3] at he
    linear_combination 27*he
  obtain ⟨z,hz,_⟩:=exists_integer_of_is_root_of_monic (monic3_monic A B) hr
  change 3*x=(z:ℚ) at hz
  have hzQ : (z:ℚ)^4+18*A*(z:ℚ)^2+108*B*z-27*(A:ℚ)^2=0 := by
    rw [←hz]
    dsimp [psi3] at he
    linear_combination 27*he
  have hzZ : z^4+18*A*z^2+108*B*z-27*A^2=0 := by exact_mod_cast hzQ
  have hz11:=congrArg (Int.castRingHom (ZMod 11)) hzZ
  exact hmod (z:ZMod 11) (by simpa using hz11)

theorem E_psi3_no_root (x : ℚ) : psi3 (-78162568812) 8433576786332241 x≠0 := by
  apply psi3_no_root (-78162568812) 8433576786332241
  intro z
  have hA : ((-78162568812:ℤ):ZMod 11)=2 := by decide
  have hB : ((8433576786332241:ℤ):ZMod 11)=5 := by decide
  rw [hA,hB]
  exact mod11_psi3_E z

theorem twist_psi3_no_root (x : ℚ) :
    psi3 (43645^2*(-78162568812)) (43645^3*8433576786332241) x≠0 := by
  have h:=psi3_no_root (43645^2*(-78162568812)) (43645^3*8433576786332241) ?_ x
  · simpa only [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_ofNat] using h
  intro z
  have hA : ((43645^2*(-78162568812):ℤ):ZMod 11)=7 := by decide
  have hB : ((43645^3*8433576786332241:ℤ):ZMod 11)=8 := by decide
  rw [hA,hB]
  exact mod11_psi3_twist z

private theorem coefficient_ne (A : ℚ) (hA : v A=2) : A≠0 := by
  intro ha
  simp [ha,v] at hA

/-- The complete even-horizontal region, including x=0. -/
private theorem even_basic (A B x : ℚ) (hA : v A=2) (hB : v B=0)
    (hBn : B≠0) (hx : VB 1 x) :
    cubic A B x≠0 ∧ v (cubic A B x)=0 ∧
      quartic4 A B x≠0 ∧ v (quartic4 A B x)=3 := by
  have hAn:=coefficient_ne A hA
  have hf3 : VB 3 (x^3) := by
    convert term_bound A B (1) x 0 0 3 1 (0) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hfax : VB 3 (A*x) := by
    convert term_bound A B (1) x 1 0 1 1 (0) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  obtain ⟨hf,hfv⟩:=dominant B (x^3+A*x) 3 hBn (vb_add hf3 hfax) (by omega)
  have hfEq : cubic A B x=B+(x^3+A*x) := by dsimp [cubic];ring
  rw [hfEq]
  refine ⟨hf,by omega,?_⟩
  have hh6 : VB 6 (x^6) := by
    convert term_bound A B (1) x 0 0 6 1 (0) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hh6b : VB 5 (x^6) := vb_weaken hh6 (by omega)
  have hh4 : VB 6 (5*A*x^4) := by
    convert term_bound A B (5) x 1 0 4 1 (0) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hh4b : VB 5 (5*A*x^4) := vb_weaken hh4 (by omega)
  have hh3 : VB 5 (20*B*x^3) := by
    convert term_bound A B (20) x 0 1 3 1 (2) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hh2 : VB 6 (5*A^2*x^2) := by
    convert term_bound A B (5) x 2 0 2 1 (0) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hh2b : VB 5 (5*A^2*x^2) := vb_weaken hh2 (by omega)
  have hh1 : VB 5 (4*A*B*x) := by
    convert term_bound A B (4) x 1 1 1 1 (2) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hh0 : VB 6 (A^3) := by
    convert term_bound A B (1) x 3 0 0 1 (0) hA hB (by norm_num [v]) hx using 1 <;> norm_num <;> ring
  have hh0b : VB 5 (A^3) := vb_weaken hh0 (by omega)
  have hr : VB 5 (x^6+5*A*x^4+20*B*x^3-5*A^2*x^2-4*A*B*x-A^3) :=
    vb_sub (vb_sub (vb_sub (vb_add (vb_add hh6b hh4b) hh3) hh2b) hh1) hh0b
  have hlead : v (-8*B^2)=3 := by
    simpa using term_exact A B (-8) 1 0 2 0 3 hA hB
      (by norm_num [v]) hAn hBn (by norm_num) (by norm_num)
  have hleadn : -8*B^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hBn)
  obtain ⟨hh,hhv⟩:=dominant (-8*B^2)
    (x^6+5*A*x^4+20*B*x^3-5*A^2*x^2-4*A*B*x-A^3) 5 hleadn hr (by omega)
  have hhEq : quartic4 A B x= -8*B^2+
      (x^6+5*A*x^4+20*B*x^3-5*A^2*x^2-4*A*B*x-A^3) := by dsimp [quartic4];ring
  rw [hhEq]
  exact ⟨hh,by omega⟩

/-- The full negative-horizontal region has strictly descending duplication valuation. -/
theorem double_negative (A B x : ℚ) (hA : v A=2) (hB : v B=0) (hx : v x<0) :
    doubleX A B x≠0 ∧ v (doubleX A B x)=v x-2 := by
  have hxn : x≠0 := by intro h;simp [h,v] at hx
  have hxb : VB (v x) x := fun _=>le_rfl
  have h3 : v (x^3)=3*v x := by dsimp [v];rw [padicValRat.pow];norm_num
  have h4 : v (x^4)=4*v x := by dsimp [v];rw [padicValRat.pow];norm_num
  have hAx : VB (2+v x) (A*x) := by
    convert term_bound A B 1 x 1 0 1 (v x) 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hBb : VB 0 B := vb_exact hB
  have hfrest : VB (3*v x+1) (A*x+B) :=
    vb_add (vb_weaken hAx (by omega)) (vb_weaken hBb (by omega))
  obtain ⟨hfn,hfv⟩:=dominant (x^3) (A*x+B) (3*v x+1) (pow_ne_zero 3 hxn) hfrest (by omega)
  have hfEq : cubic A B x=x^3+(A*x+B) := by dsimp [cubic];ring
  rw [←hfEq] at hfn hfv
  have hn2 : VB (1+2+2*v x) (-2*A*x^2) := by
    convert term_bound A B (-2) x 1 0 2 (v x) 1 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hn1 : VB (3+0+1*v x) (-8*B*x) := by
    convert term_bound A B (-8) x 0 1 1 (v x) 3 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hn0 : VB (0+4+0*v x) (A^2) := by
    convert term_bound A B (1) x 2 0 0 (v x) 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hnrest : VB (4*v x+1) (-2*A*x^2-8*B*x+A^2) := by
    convert vb_add (vb_add (vb_weaken hn2 (by omega : 4*v x+1≤1+2+2*v x))
      (vb_weaken hn1 (by omega : 4*v x+1≤3+0+1*v x)))
      (vb_weaken hn0 (by omega : 4*v x+1≤0+4+0*v x)) using 1 <;> ring
  obtain ⟨hnn,hnv⟩:=dominant (x^4) (-2*A*x^2-8*B*x+A^2)
    (4*v x+1) (pow_ne_zero 4 hxn) hnrest (by omega)
  have hnEq : numerator A B x=x^4+(-2*A*x^2-8*B*x+A^2) := by dsimp [numerator];ring
  rw [←hnEq] at hnn hnv
  have hden : 4*cubic A B x≠0 := mul_ne_zero (by norm_num) hfn
  refine ⟨div_ne_zero hnn hden,?_⟩
  dsimp [doubleX,v]
  rw [padicValRat.div hnn hden,padicValRat.mul (by norm_num : (4:ℚ)≠0) hfn]
  change v (numerator A B x)-(v 4+v (cubic A B x))=v x-2
  have hv4 : v 4=2 := by norm_num [v]
  rw [hnv,hfv,h4,h3,hv4]
  omega

/-- Unit horizontal points duplicate to the full negative-horizontal region. -/
theorem double_unit (A B x : ℚ) (hA : v A=2) (hB : v B=0)
    (hxn : x≠0) (hx : v x=0) (hfn : cubic A B x≠0) :
    doubleX A B x≠0 ∧ v (doubleX A B x)<0 := by
  have hxb : VB 0 x := vb_exact hx
  have hf3 : VB 0 (x^3) := by
    convert term_bound A B (1) x 0 0 3 0 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hf1 : VB 2 (A*x) := by
    convert term_bound A B (1) x 1 0 1 0 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hn2 : VB 3 (-2*A*x^2) := by
    convert term_bound A B (-2) x 1 0 2 0 1 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hn1 : VB 3 (-8*B*x) := by
    convert term_bound A B (-8) x 0 1 1 0 3 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hn0 : VB 4 (A^2) := by
    convert term_bound A B (1) x 2 0 0 0 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
  have hfb : VB 0 (cubic A B x) :=
    vb_add (vb_add hf3 (vb_weaken hf1 (by omega))) (vb_exact hB)
  have hfv : 0≤v (cubic A B x) := hfb hfn
  have hnrest : VB 3 (-2*A*x^2-8*B*x+A^2) := by
    convert vb_add (vb_add hn2 hn1) (vb_weaken hn0 (by omega)) using 1 <;> ring
  have h4 : v (x^4)=0 := by dsimp [v];rw [padicValRat.pow];change 4*v x=0;rw [hx];norm_num
  obtain ⟨hnn,hnv⟩:=dominant (x^4) (-2*A*x^2-8*B*x+A^2) 3 (pow_ne_zero 4 hxn) hnrest (by omega)
  have hnEq : numerator A B x=x^4+(-2*A*x^2-8*B*x+A^2) := by dsimp [numerator];ring
  rw [←hnEq] at hnn hnv
  have hden : 4*cubic A B x≠0 := mul_ne_zero (by norm_num) hfn
  refine ⟨div_ne_zero hnn hden,?_⟩
  dsimp [doubleX,v]
  rw [padicValRat.div hnn hden,padicValRat.mul (by norm_num : (4:ℚ)≠0) hfn]
  change v (numerator A B x)-(v 4+v (cubic A B x))<0
  have hv4 : v 4=2 := by norm_num [v]
  rw [hnv,h4,hv4]
  omega

/-- Every point in the entire even-horizontal region triples to a nonzero
horizontal value of nonpositive valuation, unless the three-division polynomial vanishes. -/
theorem even_triple_nonpositive (A B x : ℚ) (hA : v A=2) (hB : v B=0)
    (hBn : B≠0) (hx : x=0 ∨ 0<v x) (hDn : psi3 A B x≠0) :
    tripleX A B x≠0 ∧ v (tripleX A B x)≤0 := by
  have hAn:=coefficient_ne A hA
  have hxb : VB 1 x := by
    intro hxn
    rcases hx with hx|hx
    · exact False.elim (hxn hx)
    · omega
  obtain ⟨hfn,hfv,hhn,hhv⟩:=even_basic A B x hA hB hBn hxb
  have hNn : 8*cubic A B x*quartic4 A B x≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hfn) hhn
  have hNv : v (8*cubic A B x*quartic4 A B x)=6 := by
    dsimp [v]
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hfn) hhn,
      padicValRat.mul (by norm_num : (8:ℚ)≠0) hfn]
    change v 8+v (cubic A B x)+v (quartic4 A B x)=6
    rw [hfv,hhv]
    norm_num [v]
  let q : ℚ:=8*cubic A B x*quartic4 A B x/(psi3 A B x)^2
  have hqn : q≠0 := div_ne_zero hNn (pow_ne_zero 2 hDn)
  have hqv : v q=6-2*v (psi3 A B x) := by
    dsimp [q,v]
    rw [padicValRat.div hNn (pow_ne_zero 2 hDn),padicValRat.pow]
    change v (8*cubic A B x*quartic4 A B x)-2*v (psi3 A B x)=_
    rw [hNv]
  have hnq : v (-q)=v q := padicValRat.neg q
  by_cases hx1 : x≠0 ∧ v x=1
  · have hleadn : 12*B*x≠0 := mul_ne_zero (mul_ne_zero (by norm_num) hBn) hx1.1
    have hleadv : v (12*B*x)=3 := by
      simpa [hx1.2] using term_exact A B 12 x 0 1 1 2 hA hB
        (by norm_num [v]) hAn hBn (by norm_num) hx1.1
    have hd4 : VB 4 (3*x^4) := by
      convert term_bound A B (3) x 0 0 4 1 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
    have hd2 : VB 5 (6*A*x^2) := by
      convert term_bound A B (6) x 1 0 2 1 1 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
    have hd0 : VB 4 (A^2) := by
      convert term_bound A B (1) x 2 0 0 1 0 hA hB (by norm_num [v]) hxb using 1 <;> norm_num <;> ring
    have hr : VB 4 (3*x^4+6*A*x^2-A^2) := vb_sub (vb_add hd4 (vb_weaken hd2 (by omega))) hd0
    obtain ⟨hdn,hdv⟩:=dominant (12*B*x) (3*x^4+6*A*x^2-A^2) 4 hleadn hr (by omega)
    have hdEq : psi3 A B x=12*B*x+(3*x^4+6*A*x^2-A^2) := by dsimp [psi3];ring
    rw [←hdEq] at hdv
    have hqe : v q=0 := by omega
    obtain ⟨h3n,h3v⟩:=dominant (-q) x 1 (neg_ne_zero.mpr hqn) hxb (by omega)
    change x-q≠0 ∧ v (x-q)≤0
    rw [show x-q= -q+x by ring]
    exact ⟨h3n,by omega⟩
  · have hxb2 : VB 2 x := by
      intro hxn
      have hvx:=hxb hxn
      by_contra hlt
      have he : v x=1 := by omega
      exact hx1 ⟨hxn,he⟩
    have hd4 : VB 8 (3*x^4) := by
      convert term_bound A B (3) x 0 0 4 2 0 hA hB (by norm_num [v]) hxb2 using 1 <;> norm_num <;> ring
    have hd2 : VB 7 (6*A*x^2) := by
      convert term_bound A B (6) x 1 0 2 2 1 hA hB (by norm_num [v]) hxb2 using 1 <;> norm_num <;> ring
    have hd1 : VB 4 (12*B*x) := by
      convert term_bound A B (12) x 0 1 1 2 2 hA hB (by norm_num [v]) hxb2 using 1 <;> norm_num <;> ring
    have hd0 : VB 4 (A^2) := by
      convert term_bound A B (1) x 2 0 0 2 0 hA hB (by norm_num [v]) hxb2 using 1 <;> norm_num <;> ring
    have hDb : VB 4 (psi3 A B x) :=
      vb_sub (vb_add (vb_add (vb_weaken hd4 (by omega)) (vb_weaken hd2 (by omega))) hd1) hd0
    have hDv : 4≤v (psi3 A B x) := hDb hDn
    obtain ⟨h3n,h3v⟩:=dominant (-q) x 2 (neg_ne_zero.mpr hqn) hxb2 (by omega)
    change x-q≠0 ∧ v (x-q)≤0
    rw [show x-q= -q+x by ring]
    exact ⟨h3n,by omega⟩

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6TorsionDyadicAlgebra
