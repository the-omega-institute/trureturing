/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairFourEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairFourEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete unbounded endpoint exclusions for the repeated exponent four. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Source: four-prime-pair-four, supplied PR9 source revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The full endpoint-two
reduction retains all sixteen strict nonsquare rows and all factorization
rows. It is not a rectangular exponent scan or a new integrality criterion. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.SpectralGraph.PairFourEndpoints
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

def P2 {R : Type*} [CommRing R] (b c : R) : R :=
  -9*b^2*c^2+120*b^2*c-15*b^2+120*b*c^2+1014*b*c+306*b-15*c^2+306*c+189

def P3 {R : Type*} [CommRing R] (b c : R) : R :=
  -54*b^2*c^2+30*b^2*c-60*b^2+30*b*c^2+540*b*c+96*b-60*c^2+96*c+48

theorem determinant_two {R : Type*} [CommRing R] (b c : R) :
    (tensorK 4 b c-(2:R) • 1).det = P2 b c := by
  rw [det_tensorK_sub_scalar]
  unfold P2
  ring

theorem determinant_three {R : Type*} [CommRing R] (b c : R) :
    (tensorK 4 b c-(3:R) • 1).det = P3 b c := by
  rw [det_tensorK_sub_scalar]
  unfold P3
  ring

private theorem P2_symm {R : Type*} [CommRing R] (b c : R) : P2 b c=P2 c b := by
  unfold P2; ring
private theorem P3_symm {R : Type*} [CommRing R] (b c : R) : P3 b c=P3 c b := by
  unfold P3; ring

private theorem square_gap (z H : ℤ) (hH : 0 ≤ H)
    (hl : H^2 < z^2) (hu : z^2 < (H+1)^2) : False := by
  by_cases hz : 0 ≤ z
  · have hlo : H < z := by nlinarith
    have hhi : z < H+1 := by nlinarith
    omega
  · have hlo : H < -z := by nlinarith
    have hhi : -z < H+1 := by nlinarith
    omega

theorem quadratic_gap (A B C c H : ℤ)
    (hl : H^2 < B^2-4*A*C) (hu : B^2-4*A*C < (H+1)^2)
    (hH : 0 ≤ H) : A*c^2+B*c+C ≠ 0 := by
  intro hz
  have hs : (2*A*c+B)^2 = B^2-4*A*C := by
    linear_combination 4*A*hz
  exact square_gap (2*A*c+B) H hH (by rwa [hs]) (by rwa [hs])

private theorem P2_tail (b c : ℤ) (hb : 32 ≤ b) (hc : 32 ≤ c) : P2 b c < 0 := by
  let u := b-32
  let v := c-32
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have he : -P2 b c =
      9*u^2*v^2+456*u^2*v+5391*u^2+456*u*v^2+20490*u*v+
      189390*u+5391*v^2+189390*v+545475 := by dsimp [u,v,P2]; ring
  have hp : 0 < -P2 b c := by rw [he]; positivity
  linarith

private theorem P2_small (b c : ℤ) (hb : 2 ≤ b) (hb13 : b ≤ 13)
    (hc : 0 < c) : 0 < P2 b c := by
  let A := -9*b^2+120*b-15
  let B := 120*b^2+1014*b+306
  let C := -15*b^2+306*b+189
  have hp : 0 ≤ (b-2)*(13-b) := mul_nonneg (by omega) (by omega)
  have hA : 0 < A := by dsimp [A]; nlinarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; nlinarith
  have he : P2 b c = A*c^2+B*c+C := by dsimp [P2,A,B,C]; ring
  rw [he]
  positivity

private theorem P2_ordered (b c : ℤ) (hb : 2 ≤ b) (hbc : b ≤ c) : P2 b c ≠ 0 := by
  by_cases h32 : 32 ≤ b
  · exact (P2_tail b c h32 (by omega)).ne
  by_cases h13 : b ≤ 13
  · exact (P2_small b c hb h13 (by omega)).ne'
  have h14 : 14 ≤ b := by omega
  have h31 : b ≤ 31 := by omega
  by_cases h21 : b=21
  · rw [h21]
    have he : P2 21 c = -24*c*(61*c-3105) := by unfold P2; ring
    rw [he]
    intro hz
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h <;> omega
    · omega
  by_cases h27 : b=27
  · rw [h27]
    have he : P2 27 c = -12*(2*c-69)*(139*c-3) := by unfold P2; ring
    rw [he]
    intro hz
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h <;> omega
    · omega
  have he : P2 b c = (-9*b^2+120*b-15)*c^2+(120*b^2+1014*b+306)*c+
      (-15*b^2+306*b+189) := by unfold P2; ring
  rw [he]
  interval_cases b
  · exact quadratic_gap _ _ _ c 38029 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 42531 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 47271 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 52247 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 57460 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 62910 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 68596 (by norm_num) (by norm_num) (by norm_num)
  · contradiction
  · exact quadratic_gap _ _ _ c 80679 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 87075 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 93707 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 100575 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 107679 (by norm_num) (by norm_num) (by norm_num)
  · contradiction
  · exact quadratic_gap _ _ _ c 122596 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 130408 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 138456 (by norm_num) (by norm_num) (by norm_num)
  · exact quadratic_gap _ _ _ c 146740 (by norm_num) (by norm_num) (by norm_num)

/-- No integer tails at least two have the endpoint-two eigenvalue. -/
theorem two_nonzero (b c : ℤ) (hb : 2 ≤ b) (hc : 2 ≤ c) : P2 b c ≠ 0 := by
  rcases le_total b c with h | h
  · exact P2_ordered b c hb h
  · rw [P2_symm]; exact P2_ordered c b hc h

private theorem P3_tail (b c : ℤ) (hb : 4 ≤ b) (hc : 4 ≤ c) : P3 b c < 0 := by
  let u := b-4
  let v := c-4
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have he : -P3 b c =
      54*u^2*v^2+402*u^2*v+804*u^2+402*u*v^2+2436*u*v+
      3696*u+804*v^2+3696*v+2448 := by dsimp [u,v,P3]; ring
  have hp : 0 < -P3 b c := by rw [he]; positivity
  linarith

private theorem P3_ordered (b c : ℤ) (hb : 2 ≤ b) (hbc : b ≤ c)
    (hz : P3 b c=0) : b=2 ∧ c=6 := by
  by_cases h4 : 4 ≤ b
  · exact ((P3_tail b c h4 (by omega)).ne hz).elim
  have hb3 : b≤3 := by omega
  interval_cases b
  · have he : P3 2 c = -216*c*(c-6) := by unfold P3; ring
    rw [he] at hz
    have hh : c-6=0 := (mul_eq_zero.mp hz).resolve_left (by omega)
    exact ⟨rfl,by omega⟩
  · have he : P3 3 c = -6*(4*c-17)*(19*c-2) := by unfold P3; ring
    rw [he] at hz
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h <;> omega
    · omega

/-- Exactly the exchanged tails two and six admit endpoint three. -/
theorem three_zero_iff (b c : ℤ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    P3 b c=0 ↔ (b=2 ∧ c=6) ∨ (b=6 ∧ c=2) := by
  constructor
  · intro hz
    rcases le_total b c with h | h
    · exact Or.inl (P3_ordered b c hb h hz)
    · obtain ⟨h1,h2⟩ := P3_ordered c b hc h (by rwa [P3_symm])
      exact Or.inr ⟨h2,h1⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num [P3]

end D5.S3.Combinatorics.SpectralGraph.PairFourEndpoints
