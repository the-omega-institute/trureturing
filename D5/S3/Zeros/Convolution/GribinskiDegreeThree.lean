/- GID: D5/S3/Zeros/Convolution/GribinskiDegreeThree
   generality: I
   mirror-B: D5/B/S3/Zeros/Convolution/GribinskiDegreeThree
   mirror-E: none(waiver:symbolic-real-parameter-proof)
   anchors: []
   utility: none
   digest: Fixed-degree-three generalized rectangular convolution. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic
import D5.S3.Zeros.Convolution.GribinskiDegreeThreeDiscriminant
import D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeSix

/-!
Definition 3.10 of Campbell, Morales, and Perales, arXiv:2502.00254v2,
specialized to m=3. The weight is the PRODUCT of two falling factorials.
The coefficient definition applies to arbitrary input polynomials before
specialization to root triples. The consistency theorem checks k=0,1,2,3.

This is a symbolic real-parameter development, not a finite enumeration or
an assertion about general m. See docs/reports/convolution/gribinski-m3-0909.md
for the first bind-only attempt, declaration classifications, and measurements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Polynomial

namespace D5.S3.Zeros.Convolution.GribinskiDegreeThree

/-- The signed coefficient convention in fixed degree three. -/
def elementaryCoeff (p : Real[X]) (k : Nat) : Real :=
  (-1) ^ k * p.coeff (3 - k)

/-- The product prefactor from Definition 3.10, with m=3. -/
def weight (alpha : Real) (k : Nat) : Real :=
  (descPochhammer Real k).eval 3 * (descPochhammer Real k).eval (3 + alpha)

def normalizedCoeff (alpha : Real) (p : Real[X]) (k : Nat) : Real :=
  elementaryCoeff p k / weight alpha k

/-- The sum over i+j=k, indexed by i=0,...,k. -/
def convolutionCoeff (alpha : Real) (p q : Real[X]) (k : Nat) : Real :=
  weight alpha k * ((Finset.range (k + 1)).sum fun i =>
    normalizedCoeff alpha p i * normalizedCoeff alpha q (k - i))

/-- General degree-three coefficient convolution. -/
def boxplus3 (alpha : Real) (p q : Real[X]) : Real[X] :=
  C (convolutionCoeff alpha p q 0) * X ^ 3 -
    C (convolutionCoeff alpha p q 1) * X ^ 2 +
    C (convolutionCoeff alpha p q 2) * X - C (convolutionCoeff alpha p q 3)

def rootTriple (a b c : Real) : Real[X] := (X - C a) * (X - C b) * (X - C c)

/-- All four signed output coefficients agree with the defining convolution. -/
theorem definition_consistency (alpha : Real) (p q : Real[X]) (k : Nat) (hk : k <= 3) :
    elementaryCoeff (boxplus3 alpha p q) k = convolutionCoeff alpha p q k := by
  interval_cases k <;> norm_num [elementaryCoeff, boxplus3]

/-- The cross weight for the second elementary coefficient. -/
def kappa (alpha : Real) : Real := 2 * (alpha + 2) / (3 * (alpha + 3))

/-- The cross weight for the third elementary coefficient. -/
def rho (alpha : Real) : Real := (alpha + 1) / (3 * (alpha + 3))

private theorem weight_values (alpha : Real) :
    weight alpha 0 = 1 /\ weight alpha 1 = 3 * (alpha + 3) /\
      weight alpha 2 = 6 * (alpha + 3) * (alpha + 2) /\
      weight alpha 3 = 6 * (alpha + 3) * (alpha + 2) * (alpha + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [weight, descPochhammer_succ_eval] <;> ring

private theorem rootTriple_coefficients (a b c : Real) :
    elementaryCoeff (rootTriple a b c) 0 = 1 /\
      elementaryCoeff (rootTriple a b c) 1 = a + b + c /\
      elementaryCoeff (rootTriple a b c) 2 = a * b + a * c + b * c /\
      elementaryCoeff (rootTriple a b c) 3 = a * b * c := by
  unfold rootTriple
  rw [Cubic.prod_X_sub_C_eq]
  norm_num [elementaryCoeff]

/-- Substitution of the two root triples into all four defining coefficient sums. -/
theorem convolution_coefficients (alpha a b c d e f : Real)
    (h1 : alpha ≠ -1) (h2 : alpha ≠ -2) (h3 : alpha ≠ -3) :
    convolutionCoeff alpha (rootTriple a b c) (rootTriple d e f) 0 = 1 /\
      convolutionCoeff alpha (rootTriple a b c) (rootTriple d e f) 1 =
        a + b + c + (d + e + f) /\
      convolutionCoeff alpha (rootTriple a b c) (rootTriple d e f) 2 =
        a * b + a * c + b * c + (d * e + d * f + e * f) +
          kappa alpha * (a + b + c) * (d + e + f) /\
      convolutionCoeff alpha (rootTriple a b c) (rootTriple d e f) 3 =
        a * b * c + d * e * f + rho alpha *
          ((a + b + c) * (d * e + d * f + e * f) +
            (a * b + a * c + b * c) * (d + e + f)) := by
  have ha1 : alpha + 1 ≠ 0 := by intro h; apply h1; linarith only [h]
  have ha2 : alpha + 2 ≠ 0 := by intro h; apply h2; linarith only [h]
  have ha3 : alpha + 3 ≠ 0 := by intro h; apply h3; linarith only [h]
  rcases weight_values alpha with ⟨w0, w1, w2, w3⟩
  rcases rootTriple_coefficients a b c with ⟨p0, p1, p2, p3⟩
  rcases rootTriple_coefficients d e f with ⟨q0, q1, q2, q3⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [convolutionCoeff, Finset.sum_range_succ, Finset.sum_range_zero,
      normalizedCoeff, p0, p1, p2, p3, q0, q1, q2, q3, w0, w1, w2, w3] <;>
    norm_num [kappa, rho] <;> field_simp <;> ring

/-- The explicit cubic follows from the general Definition 3.10 coefficient operation. -/
theorem m3_explicit_coefficients (alpha a b c d e f : Real)
    (h1 : alpha ≠ -1) (h2 : alpha ≠ -2) (h3 : alpha ≠ -3) :
    boxplus3 alpha (rootTriple a b c) (rootTriple d e f) =
      X ^ 3 - C (a + b + c + (d + e + f)) * X ^ 2 +
        C (a * b + a * c + b * c + (d * e + d * f + e * f) +
          kappa alpha * (a + b + c) * (d + e + f)) * X -
        C (a * b * c + d * e * f + rho alpha *
          ((a + b + c) * (d * e + d * f + e * f) +
            (a * b + a * c + b * c) * (d + e + f))) := by
  rcases convolution_coefficients alpha a b c d e f h1 h2 h3 with ⟨h0, he1, he2, he3⟩
  simp [boxplus3, h0, he1, he2, he3]

/-- Every defining weight is positive on the entire requested parameter range. -/
theorem weight_pos (alpha : Real) (halpha : -1 < alpha) (k : Nat) (hk : k <= 3) :
    0 < weight alpha k := by
  have hk' : (k : Real) <= 3 := by exact_mod_cast hk
  exact mul_pos (descPochhammer_pos (by linarith only [hk']))
    (descPochhammer_pos (by linarith only [hk', halpha]))

/-- The three output elementary coefficients are nonnegative for nonnegative input roots. -/
theorem m3_nonnegative_coefficients (alpha a b c d e f : Real) (halpha : -1 < alpha)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hd : 0 <= d) (he : 0 <= e) (hf : 0 <= f) :
    0 <= elementaryCoeff (boxplus3 alpha (rootTriple a b c) (rootTriple d e f)) 1 /\
      0 <= elementaryCoeff (boxplus3 alpha (rootTriple a b c) (rootTriple d e f)) 2 /\
      0 <= elementaryCoeff (boxplus3 alpha (rootTriple a b c) (rootTriple d e f)) 3 := by
  rw [definition_consistency _ _ _ 1 (by norm_num),
    definition_consistency _ _ _ 2 (by norm_num),
    definition_consistency _ _ _ 3 (by norm_num)]
  rcases convolution_coefficients alpha a b c d e f
    (by linarith only [halpha]) (by linarith only [halpha])
    (by linarith only [halpha]) with ⟨_, h1, h2, h3⟩
  rw [h1, h2, h3]
  have hden : 0 < 3 * (alpha + 3) := by linarith only [halpha]
  have hk : 0 < kappa alpha := div_pos (by linarith only [halpha]) hden
  have hr : 0 < rho alpha := div_pos (by linarith only [halpha]) hden
  exact ⟨by positivity, by positivity, by positivity⟩

/-- The monic cubic discriminant in the signed coefficient convention. -/
def discriminant (p : Real[X]) : Real :=
  let S := elementaryCoeff p 1
  let T := elementaryCoeff p 2
  let U := elementaryCoeff p 3
  S^2*T^2 - 4*T^3 - 4*S^3*U - 27*U^2 + 18*S*T*U

/-- Every nonnegative root triple has ordered nonnegative gap coordinates,
with the same polynomial, including repeated and zero roots. -/
theorem nonnegative_rootTriple_coordinates (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    ∃ x u v : Real, 0 <= x ∧ 0 <= u ∧ 0 <= v ∧
      rootTriple a b c = rootTriple x (x+u) (x+u+v) := by
  suffices ∃ r s t : Real, 0 <= r ∧ r <= s ∧ s <= t ∧
      rootTriple a b c = rootTriple r s t by
    obtain ⟨r, s, t, hr, hrs, hst, hpoly⟩ := this
    refine ⟨r, s-r, t-s, hr, sub_nonneg.mpr hrs, sub_nonneg.mpr hst, ?_⟩
    convert hpoly using 1
    congr 1 <;> ring
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ⟨a, b, c, ha, hab, hbc, rfl⟩
    · rcases le_total a c with hac | hca
      · refine ⟨a, c, b, ha, hac, hcb, ?_⟩
        unfold rootTriple
        ring
      · refine ⟨c, a, b, hc, hca, hab, ?_⟩
        unfold rootTriple
        ring
  · rcases le_total a c with hac | hca
    · refine ⟨b, a, c, hb, hba, hac, ?_⟩
      unfold rootTriple
      ring
    · rcases le_total b c with hbc | hcb
      · refine ⟨b, c, a, hb, hbc, hca, ?_⟩
        unfold rootTriple
        ring
      · refine ⟨c, b, a, hc, hcb, hba, ?_⟩
        unfold rootTriple
        ring

private theorem discriminant_numerator (alpha S P Q R V : Real) (halpha : -1 < alpha) :
    let T := P + kappa alpha * Q
    let U := R + rho alpha * V
    27*(alpha+3)^3 * (S^2*T^2 - 4*T^3 - 4*S^3*U - 27*U^2 + 18*S*T*U) =
      GribinskiDegreeThreeDiscriminant.numerator (alpha+1) S
        (6*P+2*Q) (3*P+2*Q) (6*R) (3*R+V) := by
  have hden : alpha + 3 ≠ 0 := by linarith only [halpha]
  dsimp only
  unfold kappa rho GribinskiDegreeThreeDiscriminant.numerator
  field_simp
  ring

private theorem ordered_output_discriminant (alpha x u v y w z : Real)
    (halpha : -1 < alpha) (hx : 0 <= x) (hu : 0 <= u) (hv : 0 <= v)
    (hy : 0 <= y) (hw : 0 <= w) (hz : 0 <= z) :
    0 <= discriminant (boxplus3 alpha
      (rootTriple x (x+u) (x+u+v)) (rootTriple y (y+w) (y+w+z))) := by
  have hnum := GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg
    (alpha+1) x u v y w z (by linarith only [halpha]) hx hu hv hy hw hz
  dsimp only at hnum
  simp only [mul_assoc, add_assoc] at hnum
  rw [← discriminant_numerator alpha _ _ _ _ _ halpha] at hnum
  have hscale : 0 < 27*(alpha+3)^3 := by
    have : 0 < alpha+3 := by linarith only [halpha]
    positivity
  have hdisc := nonneg_of_mul_nonneg_right hnum hscale
  dsimp only [discriminant]
  rw [definition_consistency _ _ _ 1 (by norm_num),
    definition_consistency _ _ _ 2 (by norm_num),
    definition_consistency _ _ _ 3 (by norm_num)]
  obtain ⟨_, h1, h2, h3⟩ := convolution_coefficients alpha x (x+u) (x+u+v)
    y (y+w) (y+w+z) (by linarith only [halpha]) (by linarith only [halpha])
    (by linarith only [halpha])
  rw [h1, h2, h3]
  simpa only [mul_assoc, add_assoc] using hdisc

/-- The cubic discriminant is nonnegative on the entire six-root domain. -/
theorem m3_discriminant_nonneg (alpha a b c d e f : Real) (halpha : -1 < alpha)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hd : 0 <= d) (he : 0 <= e) (hf : 0 <= f) :
    0 <= discriminant (boxplus3 alpha (rootTriple a b c) (rootTriple d e f)) := by
  obtain ⟨x, u, v, hx, hu, hv, hp⟩ := nonnegative_rootTriple_coordinates a b c ha hb hc
  obtain ⟨y, w, z, hy, hw, hz, hq⟩ := nonnegative_rootTriple_coordinates d e f hd he hf
  rw [hp, hq]
  exact ordered_output_discriminant alpha x u v y w z halpha hx hu hv hy hw hz

/-- Degree-three generalized rectangular convolution preserves nonnegative
real roots for every alpha > -1, with multiplicities retained. -/
theorem m3_nonnegative_roots (alpha a b c d e f : Real) (halpha : -1 < alpha)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hd : 0 <= d) (he : 0 <= e) (hf : 0 <= f) :
    ∃ r s t : Real, 0 <= r ∧ 0 <= s ∧ 0 <= t ∧
      boxplus3 alpha (rootTriple a b c) (rootTriple d e f) = rootTriple r s t := by
  have hsign := m3_nonnegative_coefficients alpha a b c d e f halpha ha hb hc hd he hf
  have hdisc := m3_discriminant_nonneg alpha a b c d e f halpha ha hb hc hd he hf
  obtain ⟨r, s, t, hr, hs, ht, hfactor⟩ :=
    FiniteFreeCommutatorDegreeSix.cubic_nonnegative_factorization _ _ _
      hsign.1 hsign.2.1 hsign.2.2 hdisc
  refine ⟨r, s, t, hr, hs, ht, ?_⟩
  change boxplus3 alpha (rootTriple a b c) (rootTriple d e f) =
    (X-C r)*(X-C s)*(X-C t)
  rw [← hfactor]
  rw [definition_consistency _ _ _ 1 (by norm_num),
    definition_consistency _ _ _ 2 (by norm_num),
    definition_consistency _ _ _ 3 (by norm_num)]
  have h0 := (convolution_coefficients alpha a b c d e f
    (by linarith only [halpha]) (by linarith only [halpha])
    (by linarith only [halpha])).1
  simp only [boxplus3, h0, C_1, one_mul]

#print axioms definition_consistency
#print axioms convolution_coefficients
#print axioms m3_explicit_coefficients
#print axioms weight_pos
#print axioms m3_nonnegative_coefficients
#print axioms nonnegative_rootTriple_coordinates
#print axioms discriminant_numerator
#print axioms ordered_output_discriminant
#print axioms m3_discriminant_nonneg
#print axioms m3_nonnegative_roots
#print axioms weight_values
#print axioms rootTriple_coefficients

end D5.S3.Zeros.Convolution.GribinskiDegreeThree
