/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSharpMiddle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSharpMiddle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original sharp real endpoint-two middle cutoff and its unique equality case. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! The complete PR3 sharp-alpha statement. Its boundary equality is retained;
the integer endpoint-two completion is a distinct spectral assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportSharpMiddle
open SixSupportClassificationAlgebra

private def P (a : ℝ) : ℝ := 3*a^2-14*a+12
private def A (a u : ℝ) : ℝ := 2*u^2+7*(a-2)*u+2*P a
private def B (a u : ℝ) : ℝ :=
  (a+2)*u^3+(4*a^2+10*a-12)*u^2+(4*a^3+25*a^2-48*a+12)*u+
    2*(13*a^3-28*a^2+8*a+8)
private def B' (a u : ℝ) : ℝ :=
  3*(a+2)*u^2+2*(4*a^2+10*a-12)*u+(4*a^3+25*a^2-48*a+12)
private def K (a u : ℝ) : ℝ := (4*u+7*(a-2))*B a u+A a u*B' a u
private def D (a u : ℝ) : ℝ :=
  2*(a-2)*(9*a^3+24*a^2-56*a+16)+(33*a^3+20*a^2-208*a+136)*u+
    (20*a^2+23*a-62)*u^2+4*(a+2)*u^3
private def E (a u : ℝ) : ℝ :=
  2*(3*a^3-a^2-8*a+4)+(5*a^2+3*a-10)*u+(a+2)*u^2

private theorem identity (a u v : ℝ) :
    h a (2*a-2+u) (2*a-2+u+v) 2 =
      A a u*B a u+K a u*v/2+D a u*v^2+E a u*v^3 := by
  rw [h_eq_value]
  dsimp [value,A,B,K,B',D,E,P]
  ring

private theorem positive_coefficients (m u : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) :
    0 < B (3+m) u ∧ 0 < B' (3+m) u ∧ 0 < D (3+m) u ∧ 0 < E (3+m) u := by
  dsimp [B,B',D,E]
  constructor
  · ring_nf; positivity
  · constructor
    · ring_nf; positivity
    · constructor <;> ring_nf <;> positivity

private theorem nonnegative_zero (a u v : ℝ) (ha : 3 ≤ a)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ P a) :
    0 ≤ h a (2*a-2+u) (2*a-2+u+v) 2 ∧
      (h a (2*a-2+u) (2*a-2+u+v) 2 = 0 ↔ P a = 0 ∧ u = 0 ∧ v = 0) := by
  have hpos := positive_coefficients (a-3) u (by linarith) hu
  have harepr : 3+(a-3) = a := by ring
  rw [harepr] at hpos
  obtain ⟨hB,hB',hD,hE⟩ := hpos
  have ha2 : 0 < a-2 := by linarith
  have hA : 0 ≤ A a u := by dsimp [A]; positivity
  have hAprime : 0 < 4*u+7*(a-2) := by positivity
  have hK : 0 < K a u := by dsimp [K]; positivity
  have hAB : 0 ≤ A a u*B a u := mul_nonneg hA hB.le
  have hKv : 0 ≤ K a u*v := mul_nonneg hK.le hv
  have hDv : 0 ≤ D a u*v^2 := mul_nonneg hD.le (sq_nonneg _)
  have hEv : 0 ≤ E a u*v^3 := mul_nonneg hE.le (pow_nonneg hv _)
  constructor
  · rw [identity]
    positivity
  · constructor
    · intro hz
      have hi := identity a u v
      rw [hz] at hi
      have hAB0 : A a u*B a u = 0 := by nlinarith only [hi,hAB,hKv,hDv,hEv]
      have hKv0 : K a u*v = 0 := by nlinarith only [hi,hAB,hKv,hDv,hEv]
      have hA0 : A a u = 0 := (mul_eq_zero.mp hAB0).resolve_right hB.ne'
      have hv0 : v = 0 := (mul_eq_zero.mp hKv0).resolve_left hK.ne'
      have hlin : 0 ≤ 7*(a-2)*u := by positivity
      have hu0 : u = 0 := by dsimp [A] at hA0; nlinarith only [hA0,hlin,hp,sq_nonneg u]
      have hp0 : P a = 0 := by simpa [A,hu0] using hA0
      exact ⟨hp0,hu0,hv0⟩
    · rintro ⟨hp0,rfl,rfl⟩
      rw [identity]
      simp [A,hp0]

/-- The original exact sharp real cutoff. -/
def alpha : ℝ := (7+Real.sqrt 13)/3

/-- The sharp threshold exceeds three, with no numerical approximation. -/
theorem alpha_gt_three : 3 < alpha := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  have h2 : (2 : ℝ) < Real.sqrt 13 := by nlinarith
  dsimp [alpha]
  linarith

private theorem threshold (a : ℝ) (ha : alpha ≤ a) :
    0 ≤ P a ∧ (P a = 0 ↔ a = alpha) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  have hsr : 0 < Real.sqrt (13 : ℝ) := by nlinarith
  have hl : 0 ≤ 3*a-7-Real.sqrt 13 := by dsimp [alpha] at ha; linarith
  have hr : 0 < 3*a-7+Real.sqrt 13 := by linarith
  have hi : 3*P a = (3*a-7-Real.sqrt 13)*(3*a-7+Real.sqrt 13) := by
    dsimp [P]
    nlinarith only [hs]
  have hprod := mul_nonneg hl hr.le
  constructor
  · nlinarith only [hi,hprod]
  · constructor
    · intro hp
      have hz : (3*a-7-Real.sqrt 13)*(3*a-7+Real.sqrt 13) = 0 := by rw [← hi,hp]; ring
      have hz' := (mul_eq_zero.mp hz).resolve_right hr.ne'
      dsimp [alpha]
      linarith
    · intro h
      have hz : 3*a-7-Real.sqrt 13 = 0 := by rw [h]; dsimp [alpha]; ring
      rw [hz,zero_mul] at hi
      linarith

/-- For all ordered real parameters at the source's sharp middle bound,
the endpoint is nonnegative and equality occurs at exactly the source boundary. -/
theorem result (a b c : ℝ) (ha : alpha ≤ a) (hb : 2*a-2 ≤ b) (hbc : b ≤ c) :
    0 ≤ h a b c 2 ∧
      (h a b c 2 = 0 ↔ a = alpha ∧ b = 2*a-2 ∧ c = b) := by
  have ha3 : 3 ≤ a := alpha_gt_three.le.trans ha
  have hu : 0 ≤ b-(2*a-2) := by linarith
  have hv : 0 ≤ c-b := by linarith
  have ht := threshold a ha
  have hh := nonnegative_zero a (b-(2*a-2)) (c-b) ha3 hu hv ht.1
  have hbrepr : 2*a-2+(b-(2*a-2)) = b := by ring
  have hcrepr : 2*a-2+(b-(2*a-2))+(c-b) = c := by ring
  rw [hcrepr,hbrepr] at hh
  refine ⟨hh.1,?_⟩
  rw [hh.2,ht.2]
  constructor
  · rintro ⟨ha,hb,hc⟩
    exact ⟨ha,by linarith,by linarith⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨ha,by linarith,by linarith⟩

/-- Above the threshold the entire zero surface lies strictly below the bound. -/
theorem zero_middle_bound (a b c : ℝ) (ha : alpha < a) (hbc : b ≤ c)
    (hz : h a b c 2 = 0) : b < 2*a-2 := by
  by_contra hn
  have he := (result a b c ha.le (by linarith) hbc).2.mp hz
  linarith [he.1]

#print axioms result
#print axioms zero_middle_bound
end D5.S3.Combinatorics.SpectralGraph.SixSupportSharpMiddle
