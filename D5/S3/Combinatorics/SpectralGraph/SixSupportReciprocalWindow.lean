/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportReciprocalWindow
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportReciprocalWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict reciprocal divisor window for the complete endpoint-one spectrum. -/
import D5.S3.Combinatorics.SpectralGraph.SixSupportMiddleSpectrum

/-! Source: the revised endpoint-one-divisor-window corollary in PR3,
revision b93becea662a746badeadba42fdc3d3eb3db9382, original endpoint
spectrum blob b61e5619a508f11c7df335dd468ce61e2aa60000. The argument
uses all four actual residual roots. The theorem is proved on the full
ordered real minimum-four domain; the source integer divisor test is
its specialization. A window, or one surviving divisor, does not prove
integrality and does not bound the unbounded exponent surface. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportReciprocalWindow
open Polynomial
open D5.S3.Combinatorics.SpectralGraph
open SixSupportClassificationAlgebra SixSupportEndpointOneArithmetic

def remainderBound (a b c : ℝ) : ℝ :=
  2/(a+b+c)+1/(coefficientA a b c-min c (a+b)-2*(a+b+c))

private theorem pair_inverse (s x y : ℝ) (hs : 0 < s)
    (hx : s < x) (hy : s < y) :
    1/x+1/y < 1/s+1/(x+y-s) := by
  have hx0 : 0 < x := hs.trans hx
  have hy0 : 0 < y := hs.trans hy
  have hz : 0 < x+y-s := by linarith
  have hid : 1/s+1/(x+y-s)-(1/x+1/y) =
      (x+y)*(x-s)*(y-s)/(s*x*y*(x+y-s)) := by
    field_simp
    <;> ring
  have hp : 0 < (x+y)*(x-s)*(y-s)/(s*x*y*(x+y-s)) := by
    apply div_pos <;> positivity
  linarith [hid]

/-- The strict three-root reciprocal bound, including repeated roots.
Only their strict separation from the threshold matters. -/
theorem three_reciprocals (s x y z : ℝ) (hs : 0 < s)
    (hx : s < x) (hy : s < y) (hz : s < z) :
    0 < 1/x+1/y+1/z ∧
    1/x+1/y+1/z < 2/s+1/(x+y+z-2*s) := by
  have hxy := pair_inverse s x y hs hx hy
  have hxy' : s < x+y-s := by linarith
  have hxyz := pair_inverse s (x+y-s) z hs hxy' hz
  have he : x+y-s+z-s = x+y+z-2*s := by ring
  rw [he] at hxyz
  constructor
  · have hx0 : 0 < x := hs.trans hx
    have hy0 : 0 < y := hs.trans hy
    have hz0 : 0 < z := hs.trans hz
    positivity
  · simp only [div_eq_mul_inv, one_mul] at hxy hxyz ⊢
    linarith

private theorem coefficients (a b c μ x y z : ℝ)
    (hf : quartic a b c = (X-C μ)*(X-C x)*(X-C y)*(X-C z)) :
    constant a b c = μ*x*y*z ∧
    coefficientA a b c = μ+x+y+z ∧
    coefficientD a b c = x*y*z+μ*y*z+μ*x*z+μ*x*y := by
  have hexpand : (X-C μ)*(X-C x)*(X-C y)*(X-C z) =
      X^4-C (μ+x+y+z)*X^3+
      C (μ*x+μ*y+μ*z+x*y+x*z+y*z)*X^2-
      C (x*y*z+μ*y*z+μ*x*z+μ*x*y)*X+C (μ*x*y*z) := by
    simp only [map_add, map_mul]
    ring
  rw [hexpand] at hf
  have h0 := congrArg (fun f : ℝ[X] => f.coeff 0) hf
  have h3 := congrArg (fun f : ℝ[X] => f.coeff 3) hf
  have h1 := congrArg (fun f : ℝ[X] => f.coeff 1) hf
  simp only [quartic, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow,
    coeff_X, coeff_C] at h0 h3 h1
  norm_num at h0 h3 h1
  exact ⟨by nlinarith only [h0],by linarith only [h3],by linarith only [h1]⟩

private theorem coefficient_margin (a b c : ℝ)
    (ha : 4 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    0 < constant a b c ∧
    0 < remainderBound a b c ∧ remainderBound a b c < 3/(a+b+c) ∧
    0 < coefficientD a b c-constant a b c*remainderBound a b c := by
  let s := a+b+c
  let p := a*b+a*c+b*c
  let r := a*b*c
  let U := min c (a+b)
  have hb : 4 ≤ b := ha.trans hab
  have hc : 4 ≤ c := hb.trans hbc
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hN : 0 < constant a b c := by unfold constant; positivity
  have hab16 : 16 ≤ a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hac : 4*c ≤ a*c := by nlinarith
  have hbc0 : 0 ≤ b*c := (mul_pos hb0 hc0).le
  have hUp : U+1 < p := by
    have hUc : U ≤ c := min_le_left c (a+b)
    dsimp [p]
    linarith
  have hq : s < coefficientA a b c-U-2*s := by
    dsimp [coefficientA,s,p] at *
    linarith
  have hq0 : 0 < coefficientA a b c-U-2*s := hs.trans hq
  have hR0 : 0 < remainderBound a b c := by
    change 0 < 2/s+1/(coefficientA a b c-U-2*s)
    positivity
  have hR : remainderBound a b c < 3/s := by
    have hi := one_div_lt_one_div_of_lt hs hq
    change 2/s+1/(coefficientA a b c-U-2*s) < 3/s
    simp only [div_eq_mul_inv, one_mul] at hi ⊢
    linarith
  have hrs : 4*s < r := by
    have hm : 0 ≤ a-4 := by linarith
    have hn : 0 ≤ b-4 := by linarith
    have ht : 0 ≤ c-4 := by linarith
    have hid : r-4*s = (a-4)*(b-4)*(c-4)+4*(a-4)*(b-4)+
        4*(a-4)*(c-4)+4*(b-4)*(c-4)+12*(a-4)+12*(b-4)+12*(c-4)+16 := by
      dsimp [r,s]
      ring
    have hh : 0 < r-4*s := by rw [hid]; positivity
    linarith
  have hsp : 0 ≤ s^2-3*p := by
    dsimp [s,p]
    nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
  have hs1 : 0 < s-1 := by dsimp [s]; linarith
  have hD : 0 < coefficientD a b c-3*constant a b c/s := by
    have he : coefficientD a b c-3*constant a b c/s =
        r*(r-4*s)+r*(s^2-3*p+1)+s^2*p+p^2+(s-1)^3 := by
      dsimp [coefficientD,constant,s,p,r]
      field_simp
      <;> ring
    rw [he]
    have hr4 : 0 < r-4*s := by linarith
    have hsp1 : 0 < s^2-3*p+1 := by linarith
    positivity
  have hNR := mul_lt_mul_of_pos_left hR hN
  have hNR' : constant a b c*remainderBound a b c < 3*constant a b c/s := by
    convert hNR using 1 <;> ring
  exact ⟨hN,hR0,hR,by linarith⟩

/-- The complete strict window for the smallest of the four actual
residual roots. Positivity of the upper denominator is proved before
inversion; no integral splitting or selected subfamily is assumed. -/
theorem result (a b c : ℝ) (ha : 4 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (h1 : h a b c 1 = 0) :
    0 < coefficientD a b c-constant a b c*remainderBound a b c ∧
    ∃ μ x y z : ℝ,
      quartic a b c = (X-C μ)*(X-C x)*(X-C y)*(X-C z) ∧
      a < μ ∧ μ < min c (a+b) ∧
      a+b+c < x ∧ a+b+c < y ∧ a+b+c < z ∧
      constant a b c/coefficientD a b c < μ ∧
      μ < constant a b c/(coefficientD a b c-constant a b c*remainderBound a b c) := by
  have hsqrt : Real.sqrt (3 : ℝ) < 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  obtain ⟨μ,x,y,z,hf,hμa,hμU,hx,hy,hz⟩ :=
    SixSupportMiddleSpectrum.factor_roots a b c (by linarith) hab hbc h1
  have hs : 0 < a+b+c := by linarith
  have hμ0 : 0 < μ := by linarith
  have hx0 : 0 < x := hs.trans hx
  have hy0 : 0 < y := hs.trans hy
  have hz0 : 0 < z := hs.trans hz
  obtain ⟨hN,hR0,hR,hmargin⟩ := coefficient_margin a b c ha hab hbc
  obtain ⟨hconst,hA,hD⟩ := coefficients a b c μ x y z hf
  obtain ⟨hrec0,hrec⟩ := three_reciprocals (a+b+c) x y z hs hx hy hz
  have hden : 0 < coefficientA a b c-min c (a+b)-2*(a+b+c) := by
    rw [hA]
    have hU : min c (a+b) ≤ c := min_le_left _ _
    -- Its positivity follows independently from the same coefficient margin.
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := ha0.trans_le hab
    have hc0 : 0 < c := hb0.trans_le hbc
    have hp : min c (a+b)+1 < a*b+a*c+b*c := by
      have hab16 : 16 ≤ a*b := by
        have hb4 : 4 ≤ b := ha.trans hab
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb4)]
      have hac : 4*c ≤ a*c := by nlinarith
      have hbc0 : 0 ≤ b*c := (mul_pos hb0 hc0).le
      linarith
    rw [← hA]
    dsimp [coefficientA]
    linarith
  have hsum : coefficientA a b c-min c (a+b)-2*(a+b+c) <
      x+y+z-2*(a+b+c) := by rw [hA]; linarith
  have hrecR : 1/x+1/y+1/z < remainderBound a b c := by
    have hi := one_div_lt_one_div_of_lt hden hsum
    dsimp [remainderBound]
    linarith
  have hvieta : coefficientD a b c/constant a b c = 1/μ+(1/x+1/y+1/z) := by
    rw [hconst,hD]
    field_simp
    <;> ring
  have hD0 : 0 < coefficientD a b c := by
    have hNR : 0 < constant a b c*remainderBound a b c := mul_pos hN hR0
    linarith
  have hlow : constant a b c/coefficientD a b c < μ := by
    apply (div_lt_iff₀ hD0).mpr
    have hi : 1/μ < coefficientD a b c/constant a b c := by linarith
    have hi' := (div_lt_div_iff₀ hμ0 hN).mp hi
    nlinarith only [hi']
  have hupp : μ < constant a b c/
      (coefficientD a b c-constant a b c*remainderBound a b c) := by
    apply (lt_div_iff₀ hmargin).mpr
    have hi : coefficientD a b c/constant a b c-remainderBound a b c < 1/μ := by
      linarith
    have he : coefficientD a b c/constant a b c-remainderBound a b c =
        (coefficientD a b c-constant a b c*remainderBound a b c)/constant a b c := by
      field_simp
    rw [he] at hi
    have hi' := (div_lt_div_iff₀ hN hμ0).mp hi
    nlinarith only [hi']
  exact ⟨hmargin,μ,x,y,z,hf,hμa,hμU,hx,hy,hz,hlow,hupp⟩

/-- The received necessary integer-spectrum test on the full exponent
domain. Integrality is required for every actual quartic root; it is not
inferred from a surviving divisor. The three high integer roots retain
their separate lower bounds. -/
theorem integer_candidates (a b c : ℤ) (ha : 4 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (h1 : h (a : ℝ) b c 1 = 0)
    (integral : ∀ t : ℝ, (quartic (a : ℝ) b c).eval t = 0 →
      ∃ d : ℤ, t = (d : ℝ)) :
    ∃ d e f g : ℤ,
      quartic (a : ℝ) b c =
        (X-C (d : ℝ))*(X-C (e : ℝ))*(X-C (f : ℝ))*(X-C (g : ℝ)) ∧
      0 < d ∧ d ∣ constant a b c ∧ (quartic a b c).eval d = 0 ∧
      max (a : ℝ) (constant (a : ℝ) b c/coefficientD (a : ℝ) b c) < (d : ℝ) ∧
      (d : ℝ) < min (min (c : ℝ) ((a : ℝ)+b))
        (constant (a : ℝ) b c/(coefficientD (a : ℝ) b c-
          constant (a : ℝ) b c*remainderBound (a : ℝ) b c)) ∧
      a+b+c+1 ≤ e ∧ a+b+c+1 ≤ f ∧ a+b+c+1 ≤ g := by
  obtain ⟨_,μ,x,y,z,hf,hμa,hμU,hx,hy,hz,hlow,hupp⟩ :=
    result a b c (by exact_mod_cast ha) (by exact_mod_cast hab)
      (by exact_mod_cast hbc) h1
  have hμ : (quartic (a : ℝ) b c).eval μ = 0 := by rw [hf]; simp
  have hxroot : (quartic (a : ℝ) b c).eval x = 0 := by rw [hf]; simp
  have hyroot : (quartic (a : ℝ) b c).eval y = 0 := by rw [hf]; simp
  have hzroot : (quartic (a : ℝ) b c).eval z = 0 := by rw [hf]; simp
  obtain ⟨d,rfl⟩ := integral μ hμ
  obtain ⟨e,rfl⟩ := integral x hxroot
  obtain ⟨f,rfl⟩ := integral y hyroot
  obtain ⟨g,rfl⟩ := integral z hzroot
  have hcast : (((quartic a b c).eval d : ℤ) : ℝ) =
      (quartic (a : ℝ) b c).eval (d : ℝ) := by
    simp [quartic,coefficientA,coefficientB,coefficientD,constant]
  have hdroot : (quartic a b c).eval d = 0 := by
    exact_mod_cast hcast.trans hμ
  have had : a < d := by exact_mod_cast hμa
  have hxe : a+b+c < e := by exact_mod_cast hx
  have hyf : a+b+c < f := by exact_mod_cast hy
  have hzg : a+b+c < g := by exact_mod_cast hz
  exact ⟨d,e,f,g,hf,by omega,(root_coefficients a b c d hdroot).1,
    hdroot,max_lt hμa hlow,lt_min hμU hupp,by omega,by omega,by omega⟩

#print axioms result
#print axioms integer_candidates
end D5.S3.Combinatorics.SpectralGraph.SixSupportReciprocalWindow
