/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Boundary and middle envelopes lie below the naturally rounded bulk maximum. -/

import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators
open Finset Matrix
noncomputable section

def bulkIndex (N : ℕ) : ℕ := (3 * N + 4) / 8
def bulkValue (N j : ℝ) : ℝ := (9*N + 16*j) / (3*N + 2*j)^2
def boundaryEnvelope (N : ℝ) : ℝ := (N+11)/(N+3)^2
def middleEnvelope₁ (N : ℝ) : ℝ := 25/(24*(N-1))
def middleEnvelope₂ (N : ℝ) : ℝ := 36/(35*N-80)
def commonEnvelope (N : ℝ) : ℝ := 16*(15*N-8)/(15*N-4)^2

private lemma scalar_denominators (N : ℝ) (hN : 67 ≤ N) :
    0 < N+3 ∧ 0 < 24*(N-1) ∧ 0 < 35*N-80 ∧ 0 < 15*N-4 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private lemma bulk_denominator (N j : ℝ) (hN : 67 ≤ N) (hj : 0 ≤ j) :
    0 < 3*N+2*j := by linarith

private lemma bulk_index_bounds (N : ℕ) (hN : 67 ≤ N) :
    6 ≤ bulkIndex N ∧ bulkIndex N ≤ N-10 ∧
      3*N ≤ 8*bulkIndex N+3 ∧ 8*bulkIndex N ≤ 3*N+4 := by
  dsimp [bulkIndex]
  omega

private lemma bulk_rounding_bounds (N : ℕ) (hN : 67 ≤ N) :
    -4 ≤ 3*(N : ℝ)-8*(bulkIndex N : ℝ) ∧
      3*(N : ℝ)-8*(bulkIndex N : ℝ) ≤ 3 := by
  obtain ⟨_, _, hl, hu⟩ := bulk_index_bounds N hN
  have hlR : 3*(N : ℝ) ≤ 8*(bulkIndex N : ℝ)+3 := by exact_mod_cast hl
  have huR : 8*(bulkIndex N : ℝ) ≤ 3*(N : ℝ)+4 := by exact_mod_cast hu
  constructor <;> linarith

/- The next certificate is the THREE shifted quadratic coefficients, with no
   division by u: this also covers the rays attaining H_N exactly. -/
def boundaryCertificate (u c C : ℝ) : Prop :=
  0 ≤ 2*u*c+5*u^2-C ∧
  0 ≤ 134*(2*u*c+5*u^2-C)+(c^2+22*u*c-9*u^2-6*C) ∧
  0 ≤ 4489*(2*u*c+5*u^2-C)+67*(c^2+22*u*c-9*u^2-6*C)+(11*c^2-9*C)

lemma boundary_ray_bound (N u c C : ℝ) (hN : 67 ≤ N)
    (hM : 0 < u*N+c) (hc : boundaryCertificate u c C) :
    (u^2*N+C)/(u*N+c)^2 ≤ boundaryEnvelope N := by
  obtain ⟨h2, h1, h0⟩ := hc
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  have hp : 0 ≤ (N+11)*(u*N+c)^2-(u^2*N+C)*(N+3)^2 := by
    calc
      _ = (2*u*c+5*u^2-C)*(N-67)^2 +
          (134*(2*u*c+5*u^2-C)+(c^2+22*u*c-9*u^2-6*C))*(N-67) +
          (4489*(2*u*c+5*u^2-C)+67*(c^2+22*u*c-9*u^2-6*C)+(11*c^2-9*C)) := by ring
      _ ≥ 0 := add_nonneg (add_nonneg (mul_nonneg h2 (sq_nonneg _))
        (mul_nonneg h1 hx)) h0
  exact (div_le_div_iff₀ (sq_pos_of_pos hM)
    (sq_pos_of_pos (scalar_denominators N hN).1)).2 (sub_nonneg.mp hp)

/- For k/(a*N+b), the only ray-specific envelope witnesses are the slope
   and value at N=67. For E1 use (k,a,b)=(25,24,-24); for E2=(36,35,-80). -/
def middleCertificate (k a b u v c C : ℝ) : Prop :=
  0 ≤ 4*k*u*(u+v)-a*(2*u+v)^2 ∧
  0 ≤ 4*k*(67*u*(u+v)+(2*u+v)*c-C)-(67*a+b)*(2*u+v)^2

lemma middle_ray_envelope (N j k a b u v c C : ℝ) (hN : 67 ≤ N)
    (hk : 0 < k) (hD : 0 < a*N+b) (hh : 0 < 2*u+v)
    (hM : 0 < u*N+v*j+c) (hc : middleCertificate k a b u v c C) :
    (u^2*N+(v^2+2*u*v)*j+C)/(u*N+v*j+c)^2 ≤ k/(a*N+b) := by
  let h := 2*u+v
  let S := u*N+v*j+c
  let Q := u^2*N+(v^2+2*u*v)*j+C
  let K := u*(u+v)*N+h*c-C
  obtain ⟨hα, hβ⟩ := hc
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  have hline : 0 ≤ 4*k*K-(a*N+b)*h^2 := by
    calc
      _ = (4*k*u*(u+v)-a*(2*u+v)^2)*(N-67) +
          (4*k*(67*u*(u+v)+(2*u+v)*c-C)-(67*a+b)*(2*u+v)^2) := by dsimp [K,h]; ring
      _ ≥ 0 := add_nonneg (mul_nonneg hα hx) hβ
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  have hK : 0 < K := by
    have hpos := mul_pos hD hh2
    have hkK : 0 < 4*k*K := lt_of_lt_of_le hpos (sub_nonneg.mp hline)
    by_contra hnot
    have hnon : 4*k*K ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (le_of_not_gt hnot)
    linarith
  have hQ : Q = h*S-K := by dsimp [Q,h,S,K]; ring
  have hsquare : Q/S^2 ≤ h^2/(4*K) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hM) (by positivity : 0 < 4*K)).2
    rw [hQ]
    nlinarith only [sq_nonneg (h*S-2*K)]
  have hinverse : h^2/(4*K) ≤ k/(a*N+b) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*K) hD).2
    nlinarith only [hline]
  exact hsquare.trans hinverse

lemma boundary_envelope_le_common (N : ℝ) (hN : 67 ≤ N) :
    boundaryEnvelope N ≤ commonEnvelope N := by
  obtain ⟨hH, _, _, hB⟩ := scalar_denominators N hN
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  apply (div_le_div_iff₀ (sq_pos_of_pos hH) (sq_pos_of_pos hB)).2
  apply sub_nonneg.mp
  calc
    _ = 15*(N-67)^3+1972*(N-67)^2+64939*(N-67)+8722 := by ring
    _ ≥ 0 := by positivity

lemma middle_envelope₁_le_common (N : ℝ) (hN : 67 ≤ N) :
    middleEnvelope₁ N ≤ commonEnvelope N := by
  obtain ⟨_, hE, _, hB⟩ := scalar_denominators N hN
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  apply (div_le_div_iff₀ hE (sq_pos_of_pos hB)).2
  apply sub_nonneg.mp
  calc
    _ = 135*(N-67)^2+12258*(N-67)+217943 := by ring
    _ ≥ 0 := by positivity

lemma middle_envelope₂_le_common (N : ℝ) (hN : 67 ≤ N) :
    middleEnvelope₂ N ≤ commonEnvelope N := by
  obtain ⟨_, _, hE, hB⟩ := scalar_denominators N hN
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  apply (div_le_div_iff₀ hE (sq_pos_of_pos hB)).2
  apply sub_nonneg.mp
  calc
    _ = 300*(N-67)^2+20840*(N-67)+59244 := by ring
    _ ≥ 0 := by positivity

private lemma common_le_bulk_of_rounding (N t : ℝ) (hN : 67 ≤ N)
    (hl : -4 ≤ 8*t-3*N) (hu : 8*t-3*N ≤ 4) :
    commonEnvelope N ≤ bulkValue N t := by
  let z := 8*t-3*N
  have hB := (scalar_denominators N hN).2.2.2
  have hD : 0 < 3*N+2*t := by linarith
  have hA : 0 ≤ 15*N-8 := by linarith
  have hleft : 0 ≤ z+4 := by dsimp [z]; linarith
  have hright : 0 ≤ (15*N-8)*(4-z)+32 :=
    add_nonneg (mul_nonneg hA (by dsimp [z]; linarith)) (by norm_num)
  apply (div_le_div_iff₀ (sq_pos_of_pos hB) (sq_pos_of_pos hD)).2
  apply sub_nonneg.mp
  calc
    _ = (z+4)*((15*N-8)*(4-z)+32) := by dsimp [z]; ring
    _ ≥ 0 := mul_nonneg hleft hright

lemma common_le_integer_bulk (N : ℕ) (hN : 67 ≤ N) :
    commonEnvelope (N : ℝ) ≤ bulkValue (N : ℝ) (bulkIndex N : ℝ) := by
  obtain ⟨hl, hu⟩ := bulk_rounding_bounds N hN
  apply common_le_bulk_of_rounding _ _ (by exact_mod_cast hN) <;> linarith

/- Strict optimality over ALL natural j, hence over 6 <= j <= N-10.
   d=-4 is included: the left-neighbor bracket is exactly 16, so the
   half-integer continuous tie is resolved in favor of this t. -/
private lemma bulk_integer_strict (N j : ℕ) (hN : 67 ≤ N) (hne : j ≠ bulkIndex N) :
    bulkValue (N : ℝ) (j : ℝ) < bulkValue (N : ℝ) (bulkIndex N : ℝ) := by
  let n : ℝ := N
  let t : ℝ := bulkIndex N
  let d : ℝ := 3*n-8*t
  let R (x : ℝ) := 36*n^2-36*n*(t+x)-64*t*x
  have hn : 67 ≤ n := by dsimp [n]; exact_mod_cast hN
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hround : -4 ≤ d ∧ d ≤ 3 := bulk_rounding_bounds N hN
  have hcoef : 0 ≤ 36*n+64*t := by linarith
  have hleft : 0 < R (t-1) := by
    have hp : 0 ≤ (d+4)*(15*n-(d+4)) := mul_nonneg (by linarith [hround.1])
      (by linarith [hround.2])
    have he : R (t-1) = 16+(d+4)*(15*n-(d+4)) := by dsimp [R,d]; ring
    rw [he]
    linarith
  have hright : R (t+1) < 0 := by
    have hp : 0 ≤ 15*n*((4-d)-1) := mul_nonneg (by linarith) (by linarith [hround.2])
    have he : R (t+1) = 16-(4-d)^2-15*n*(4-d) := by dsimp [R,d]; ring
    rw [he]
    nlinarith only [hp, hn, sq_nonneg (4-d)]
  have hprod : 0 < (t-(j : ℝ))*R (j : ℝ) := by
    rcases lt_or_gt_of_ne hne with hj | hj
    · have hdist : (j : ℝ)+1 ≤ t := by
        dsimp [t]
        exact_mod_cast (show j+1 ≤ bulkIndex N by omega)
      have hp : 0 ≤ (36*n+64*t)*(t-1-(j : ℝ)) := mul_nonneg hcoef (by linarith)
      have he : R (j : ℝ) = R (t-1)+(36*n+64*t)*(t-1-(j : ℝ)) := by dsimp [R]; ring
      apply mul_pos (by linarith)
      rw [he]
      linarith
    · have hdist : t+1 ≤ (j : ℝ) := by
        dsimp [t]
        exact_mod_cast (show bulkIndex N+1 ≤ j by omega)
      have hp : 0 ≤ (36*n+64*t)*((j : ℝ)-(t+1)) := mul_nonneg hcoef (by linarith)
      have he : R (j : ℝ) = R (t+1)-(36*n+64*t)*((j : ℝ)-(t+1)) := by dsimp [R]; ring
      apply mul_pos_of_neg_of_neg (by linarith)
      rw [he]
      linarith
  have hjD := bulk_denominator n (j : ℝ) hn (Nat.cast_nonneg _)
  have htD := bulk_denominator n t hn ht
  apply (div_lt_div_iff₀ (sq_pos_of_pos hjD) (sq_pos_of_pos htD)).2
  apply sub_pos.mp
  calc
    _ = (t-(j : ℝ))*R (j : ℝ) := by dsimp [R]; ring
    _ > 0 := hprod

lemma bulk_integer_maximum (N j : ℕ) (hN : 67 ≤ N) :
    bulkValue (N : ℝ) (j : ℝ) ≤ bulkValue (N : ℝ) (bulkIndex N : ℝ) := by
  by_cases hj : j = bulkIndex N
  · simp [hj]
  · exact (bulk_integer_strict N j hN hj).le

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
