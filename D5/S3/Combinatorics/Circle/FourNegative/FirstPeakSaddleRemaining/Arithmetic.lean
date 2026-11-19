/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:consumed-arithmetic-selection)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Native integer selection interface for three strict saddle chambers. -/
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-! Source preparation only. No elaboration, kernel or official acceptance claim.
The coordinates below are the literal powers of the four original gaps.
Only arithmetic is supplied here; permutation, cut and prefix transport belong
in the caller's existing physical bridge. All declarations are consumed helpers.
The unbounded certificate proofs use ring identities and positivity, not an
external certificate verdict. Attribution: caller-derived saddle construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

private def rectangle (t z x y g q r h v : ℤ) : Fin 4 → ℤ :=
  let D := y*(z+1)+1
  let A := x*D+1
  let L := x*z*t+z*t+z+1
  let M := t*y*z+D
  let Mn := 2*M-D
  let Ln := 2*L-z-1
  let C := A+L-2*g*M
  let E := (t-2*v)*A-2*(q+r)*M+2*h*L
  let H := (t-2*v)*A-2*q*M-r*Mn+h*Ln
  ![E+C,A-1-E,H-A+q*D,L-C-H]

/-- Integer-scaled auxiliary residue margins; no division by W or e. -/
private def scaled_margin (t z x y g q r h scale ps js : ℤ) : Fin 4 → ℤ :=
  let D := y*(z+1)+1
  let A := x*D+1
  let L := x*z*t+z*t+z+1
  let M := t*y*z+D
  let Mn := 2*M-D
  let Ln := 2*L-z-1
  let C := A+L-2*g*M
  let E0 := t*A-2*(q+r)*M+2*h*L
  let H0 := t*A-2*q*M-r*Mn+h*Ln
  let Re := scale*(z+1)*E0-A*ps
  let Rh := scale*(z+1)*H0-A*ps
  ![A*js+Re+scale*(z+1)*C,scale*(z+1)*(A-1)-A*js-Re,
    A*js+Rh-scale*(z+1)*(A-q*D),scale*(z+1)*(L-C)-A*js-Rh]

private theorem scaled_to_rectangle (t z x y g q r h scale ps js v : ℤ)
    (hs : 0<scale) (hz : 0<z+1)
    (hv : ps-js=2*scale*(z+1)*v)
    (hm : ∀ i, 0≤scaled_margin t z x y g q r h scale ps js i) :
    ∀ i, 0≤rectangle t z x y g q r h v i := by
  intro i
  have hi := hm i
  have hp := congrArg (fun u : ℤ => (x*(y*(z+1)+1)+1)*u) hv
  have he : scaled_margin t z x y g q r h scale ps js i =
      scale*(z+1)*rectangle t z x y g q r h v i := by
    fin_cases i <;> dsimp [scaled_margin,rectangle] <;> nlinarith only [hp]
  rw [he] at hi
  exact nonneg_of_mul_nonneg_right hi (mul_pos hs hz)

private def grain_q (K J t : ℤ) : ℤ := 2*K*J*t-4*K*J

private structure ArithmeticSelection (t z K J : ℤ) where
  r : ℤ
  h : ℤ
  v : ℤ
  r_bounds : 1≤r ∧ r≤4*K*J
  h_bounds : 0≤h ∧ 2*z*h<2*K*t
  v_bounds : 0≤v ∧ 2*v≤t-2
  good : ∀ i, 0≤rectangle t z (4*K*J*t) (2*K*t) (4*K*J)
    (grain_q K J t) r h v i

private structure NativeChoice (a b c d : ℕ) where
  s : ℕ
  r : ℕ
  h : ℕ
  v : ℕ
  bounds : 1≤r ∧ r≤s ∧ s≤2^(a-1) ∧ v<2^(d-1) ∧ h<2^(b-c-1)
  grain_bound : r≤2^(a-d)
  anchor : s=2^(a-d)*(2^(d-1)-1)+r
  submask : ∀ e, (r-1).testBit e=true → (s-1).testBit e=true
  good : ∀ i, 0≤rectangle (2^d) (2^c) (2^a) (2^b) (2^(a-d))
    ((s:ℤ)-(r:ℤ)) r h v i

private theorem ratio_identities (a b d : ℕ) (hdb : d<b) (hba : b<a) :
    (2:ℤ)^b=2*(2:ℤ)^(b-d-1)*2^d ∧
    (2:ℤ)^a=4*(2:ℤ)^(b-d-1)*2^(a-b-1)*2^d ∧
    (2:ℤ)^(a-d)=4*(2:ℤ)^(b-d-1)*2^(a-b-1) := by
  have hb : b=(b-d-1)+d+1 := by omega
  have ha : a=(b-d-1)+(a-b-1)+d+2 := by omega
  have hg : a-d=(b-d-1)+(a-b-1)+2 := by omega
  constructor
  · conv_lhs => rw [hb]
    simp only [pow_add,pow_one]
    ring
  constructor
  · conv_lhs => rw [ha]
    simp only [pow_add]
    norm_num <;> ring
  · conv_lhs => rw [hg]
    simp only [pow_add]
    norm_num <;> ring

/-- Internal conversion, consumed only after each chamber proves its capacities. -/
private noncomputable def native_of_selection (a b c d : ℕ)
    (hc : 2≤c) (hcd : c<d) (hdb : d<b) (hba : b<a)
    (sel : ArithmeticSelection (2^d) (2^c) (2^(b-d-1)) (2^(a-b-1))) :
    NativeChoice a b c d := by
  let l := a-d
  let g : ℕ := 2^l
  let Q : ℕ := 2^(d-1)-1
  let rn := sel.r.toNat
  let hn := sel.h.toNat
  let vn := sel.v.toNat
  let sn := g*Q+rn
  obtain ⟨hy,hx,hg⟩ := ratio_identities a b d hdb hba
  have ht := half_power d (by omega)
  have hax := half_power a (by omega)
  have hQ : (Q:ℤ)=(2:ℤ)^(d-1)-1 := by
    dsimp [Q]
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_cast
  have hgg : (g:ℤ)=4*(2:ℤ)^(b-d-1)*2^(a-b-1) := by
    dsimp [g,l]
    exact_mod_cast hg
  have hr : (rn:ℤ)=sel.r := Int.toNat_of_nonneg (by have := sel.r_bounds; omega)
  have hh : (hn:ℤ)=sel.h := Int.toNat_of_nonneg sel.h_bounds.1
  have hv : (vn:ℤ)=sel.v := Int.toNat_of_nonneg sel.v_bounds.1
  have hs : (sn:ℤ)=(g:ℤ)*((2:ℤ)^(d-1)-1)+sel.r := by
    dsimp [sn]
    push_cast
    rw [hQ,hr]
  have hsource : (2:ℤ)^a=(g:ℤ)*2^d := by rw [hgg,hx]
  have hcap : (g:ℤ)*(2:ℤ)^(d-1)=(2:ℤ)^(a-1) := by
    rw [ht,hax] at hsource
    nlinarith only [hsource]
  have hrn : 1≤rn ∧ rn≤g := by
    have := sel.r_bounds
    rw [←hgg,←hr] at this
    exact_mod_cast this
  have hrs : rn≤sn := by dsimp [sn]; omega
  have hsc : sn≤2^(a-1) := by
    have he : (sn:ℤ)≤2^(a-1) := by
      rw [hs,←hcap]
      have := sel.r_bounds.2
      rw [←hgg] at this
      nlinarith only [this]
    exact_mod_cast he
  have hvc : vn<2^(d-1) := by
    have he : (vn:ℤ)<2^(d-1) := by
      rw [hv]
      have := sel.v_bounds.2
      omega
    exact_mod_cast he
  have hbc : (2:ℤ)^b=2*(2:ℤ)^c*2^(b-c-1) := by
    have he : b=c+(b-c-1)+1 := by omega
    conv_lhs => rw [he]
    simp only [pow_add,pow_one]
    ring
  have hhc : hn<2^(b-c-1) := by
    have he : (hn:ℤ)<2^(b-c-1) := by
      rw [hh]
      have hh0 := sel.h_bounds.2
      rw [←hy,hbc] at hh0
      have hz : (0:ℤ)<2^c := by positivity
      by_contra hbad
      have hp := mul_nonneg hz.le (show 0≤sel.h-(2:ℤ)^(b-c-1) by omega)
      nlinarith only [hh0,hp]
    exact_mod_cast he
  refine ⟨sn,rn,hn,vn,⟨hrn.1,hrs,hsc,hvc,hhc⟩,?_,?_,?_,?_⟩
  · simpa only [g,l] using hrn.2
  · rfl
  · intro e heb
    have hu : rn-1<2^l := by dsimp [g] at hrn; omega
    have hse : sn-1=2^l*Q+(rn-1) := by dsimp [sn,g]; omega
    rw [hse]
    by_cases he : e<l
    · rw [Nat.testBit_two_pow_mul_add Q hu e]
      simpa [he] using heb
    · have hp := Nat.pow_le_pow_right (by decide : 0<2) (show l≤e by omega)
      have hf := Nat.testBit_eq_false_of_lt (hu.trans_le hp)
      rw [hf] at heb
      contradiction
  · have hq : (sn:ℤ)-(rn:ℤ)=grain_q (2^(b-d-1)) (2^(a-b-1)) (2^d) := by
      calc
        (sn:ℤ)-(rn:ℤ) = (g:ℤ)*((2:ℤ)^(d-1)-1) := by rw [hs,hr]; ring
        _ = grain_q (2^(b-d-1)) (2^(a-b-1)) (2^d) := by
          rw [hgg]
          dsimp [grain_q]
          rw [ht]
          ring
    intro i
    rw [hq,hr,hh,hv,hx,hy,hg]
    exact sel.good i

/-- High-middle scaled integer j and p, affine in the physical h. -/
private def high_margin (W J z t h : ℤ) : Fin 4 → ℤ :=
  scaled_margin t z (4*z*W*J*t) (2*z*W*t) (4*z*W*J)
    (grain_q (z*W) J t) J h (2*W)
    (2*W*(t+z-1)+2*h-1) (2*W*(z-1)-1)

/-- Half-step margins, affine separately in h and r with no hr term. -/
private def half_margin (K F e t h r : ℤ) : Fin 4 → ℤ :=
  scaled_margin t (2*K*F) (4*K*(F*e)*t) (2*K*t) (4*K*(F*e))
    (grain_q K (F*e) t) r h e
    (e*(t+2*K*F-1)+(2*(F*e)*h-r)) (e*(2*K*F-2))

private def quarter_margin (K F f t r h v : ℤ) : Fin 9 → ℤ :=
  let J := 2*F*f
  let g := 4*K*J
  let m := rectangle t 4 (g*t) (2*K*t) g (grain_q K J t) r h v
  ![m 0,m 1,m 2,m 3,r-1,g-r,v,t-2*v-2,K*t-4*(h+1)]

private theorem dyadic_time_cases (c d : ℕ) (hcd : c<d) :
    (2:ℤ)^d=2*(2:ℤ)^c ∨ 4*(2:ℤ)^c≤2^d := by
  by_cases he : d=c+1
  · left
    rw [he,pow_succ]
    ring
  · right
    calc
      4*(2:ℤ)^c = (2:ℤ)^(c+2) := by rw [pow_add]; ring
      _ ≤ (2:ℤ)^d := pow_le_pow_right₀ (by norm_num) (by omega)

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
