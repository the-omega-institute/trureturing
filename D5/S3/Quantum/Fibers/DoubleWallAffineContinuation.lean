/- GID: D5 / S3 / Quantum / Fibers / DoubleWallAffineContinuation
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/DoubleWallAffineContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lawful probability commands have no fixed affine response update. -/

import D5.S3.Quantum.Fibers.OriginalControlComposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
noncomputable section
open Set
open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.OriginalControlComposition
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Fibers.DoubleWallAffineContinuation
abbrev Response := Fin 4 → ℝ
def response (r Z k alpha beta : ℝ) : Response :=
  ![2 * Real.sqrt (k * (r / 2 - k)) * Real.cos alpha,
    2 * Real.sqrt (k * (r / 2 - k)) * Real.sin alpha,
    2 * Real.sqrt (k * Z) * Real.cos beta,
    2 * Real.sqrt (k * Z) * Real.sin beta]
private def middleAxis : Response := ![0, 0, 1, 0]

private theorem response_antipodes (r Z k alpha : ℝ) :
    response r Z k alpha 0 - response r Z k alpha Real.pi =
      (4 * Real.sqrt (k * Z)) • middleAxis := by
  ext i
  fin_cases i <;> simp [response, middleAxis] <;> ring

/-- No affine map updates the four responses for one nonzero displacement on a legal open interval. -/
private theorem nonaffine_response
    (r Z s a b : ℝ) (hZ : 0 < Z) (hs : s ≠ 0) (hab : a < b)
    (legal : ∀ k ∈ Ioo a b, 0 < k ∧ k < r / 2 ∧ 0 < k + s ∧ k + s < r / 2) :
    ¬ ∃ (D : Response →ₗ[ℝ] Response) (c : Response),
      ∀ k ∈ Ioo a b, ∀ alpha beta : ℝ,
        response r Z (k + s) alpha beta = c + D (response r Z k alpha beta) := by
  rintro ⟨D, c, hD⟩
  have gain (k : ℝ) (hk : k ∈ Ioo a b) :
      Real.sqrt ((k + s) * Z) = Real.sqrt (k * Z) * (D middleAxis 2) := by
    have he := congrArg (fun v : Response => v 2)
      (show response r Z (k + s) 0 0 - response r Z (k + s) 0 Real.pi =
        D (response r Z k 0 0 - response r Z k 0 Real.pi) by
          rw [hD k hk 0 0, hD k hk 0 Real.pi, map_sub]; abel)
    rw [response_antipodes, response_antipodes, map_smul] at he
    have hm : middleAxis 2 = 1 := rfl
    simp only [Pi.smul_apply, smul_eq_mul, hm, mul_one] at he
    nlinarith
  have squared (k : ℝ) (hk : k ∈ Ioo a b) :
      (k + s) * Z = k * Z * (D middleAxis 2)^2 := by
    have hl := legal k hk
    have h0 := Real.sq_sqrt (le_of_lt (mul_pos hl.1 hZ))
    have h1 := Real.sq_sqrt (le_of_lt (mul_pos hl.2.2.1 hZ))
    rw [gain k hk] at h1
    nlinarith [sq_nonneg (D middleAxis 2)]
  let k := (2 * a + b) / 3
  let l := (a + 2 * b) / 3
  have hk : k ∈ Ioo a b := by dsimp [k]; constructor <;> linarith
  have hl : l ∈ Ioo a b := by dsimp [l]; constructor <;> linarith
  have hkl : k < l := by dsimp [k, l]; linarith
  have e1 := squared k hk
  have e2 := squared l hl
  have hq : (D middleAxis 2)^2 = 1 := by
    have hz : (k - l) * Z * ((D middleAxis 2)^2 - 1) = 0 := by nlinarith [e1, e2]
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact (ne_of_lt hkl (sub_eq_zero.mp hz)).elim
      · exact (ne_of_gt hZ hz).elim
    · linarith
  rw [hq] at e1
  have : s * Z = 0 := by nlinarith [e1]
  exact hs ((mul_eq_zero.mp this).resolve_right (ne_of_gt hZ))

private theorem probability_command (Z k s chi0 : ℝ)
    (hk : 0 < k ∧ k < (1 - Z) / 2) (hks : 0 < k + s ∧ k + s < (1 - Z) / 2) :
    OriginalControl ((1 - Z) / 2, (1 - Z) / 2, Z) 1
      (fun t => k + s * t) (fun _ => chi0) := by
  have hka : AbsolutelyContinuousOnInterval (fun t : ℝ => k + s * t) 0 1 :=
    by
      have he : (fun t : ℝ => k + s * t) = AffineMap.lineMap k (k + s) := by
        funext t
        simp [AffineMap.lineMap_apply]
        ring
      rw [he]
      exact (lipschitzWith_lineMap k (k + s)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hca : AbsolutelyContinuousOnInterval (fun _ : ℝ => chi0) 0 1 := (LipschitzWith.const chi0).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨by norm_num, by fun_prop, continuousOn_const, ?_, hca.boundedVariationOn, Or.inl ⟨hka, hca⟩⟩
  intro t ht
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  have hlo : 0 < k + s * t := by
    by_cases hs : 0 ≤ s
    · nlinarith [mul_nonneg hs ht.1]
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hs) (sub_nonpos.mpr ht.2)]
  have hhi : k + s * t < (1 - Z) / 2 := by
    by_cases hs : 0 ≤ s
    · nlinarith [mul_nonneg hs (sub_nonneg.mpr ht.2)]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) ht.1]
  simp only [lower, upper, min_self]
  rw [show (1 - Z) / 2 + (1 - Z) / 2 - (1 - Z) = 0 by ring]
  simpa using And.intro hlo hhi
/-- One common pure probability command is lawful at every legal starting height, but no
fixed affine map updates the original four doubled response coordinates on a nonempty open interval. -/
theorem lawful_probability_continuation_not_affine
    (Z s a b : ℝ) (hZ : 0 < Z) (hZ1 : Z < 1) (hs : s ≠ 0) (hab : a < b)
    (legal : ∀ k ∈ Ioo a b,
      0 < k ∧ k < (1 - Z) / 2 ∧ 0 < k + s ∧ k + s < (1 - Z) / 2) :
    ValidBase ((1 - Z) / 2, (1 - Z) / 2, Z) ∧
    (∀ k ∈ Ioo a b, ∀ (chi0 : ℝ) (theta : Vec),
      OriginalControl ((1 - Z) / 2, (1 - Z) / 2, Z) 1
        (fun t => k + s * t) (fun _ => chi0) ∧
      Admissible ((1 - Z) / 2, (1 - Z) / 2, Z) 1
        (polygon [(k, chi0, theta), (k + s, chi0, theta)]) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        polygon [(k, chi0, theta), (k + s, chi0, theta)] t = (k + s * t, chi0, theta)) ∧
      (∀ t : ℝ, HasDerivAt (fun x : ℝ => k + s * x) s t ∧
        HasDerivAt (fun _ : ℝ => chi0) 0 t)) ∧
    ¬ (∃ (D : Response →ₗ[ℝ] Response) (c : Response),
      ∀ k ∈ Ioo a b, ∀ alpha beta : ℝ,
        response (1 - Z) Z (k + s) alpha beta =
          c + D (response (1 - Z) Z k alpha beta)) := by
  have hbase : ValidBase ((1 - Z) / 2, (1 - Z) / 2, Z) := by
    dsimp [ValidBase]
    exact ⟨hZ, hZ1, by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨hbase, ?_, nonaffine_response (1 - Z) Z s a b hZ hs hab legal⟩
  intro k hk chi0 theta
  have hlegal := legal k hk
  have hinside (j : ℝ) (hj : 0 < j ∧ j < (1 - Z) / 2) :
      j ∈ Ioo (lower ((1 - Z) / 2, (1 - Z) / 2, Z)) (upper ((1 - Z) / 2, (1 - Z) / 2, Z)) := by
    simp only [lower, upper, min_self]
    rw [show (1 - Z) / 2 + (1 - Z) / 2 - (1 - Z) = 0 by ring]
    simpa using hj
  have hleg : LawfulLeg (phaseWeight ((1 - Z) / 2, (1 - Z) / 2, Z))
      (lower ((1 - Z) / 2, (1 - Z) / 2, Z)) (upper ((1 - Z) / 2, (1 - Z) / 2, Z))
      (k, chi0, theta) (k + s, chi0, theta) := by
    refine ⟨hinside k ⟨hlegal.1, hlegal.2.1⟩,
      hinside (k + s) hlegal.2.2, ?_⟩
    intro t ht i
    simp
  refine ⟨probability_command Z k s chi0 ⟨hlegal.1, hlegal.2.1⟩ hlegal.2.2,
    ?_, ?_, ?_⟩
  · simpa using polygon_admissible ((1 - Z) / 2, (1 - Z) / 2, Z) (k, chi0, theta)
      [(k + s, chi0, theta)] (hinside k ⟨hlegal.1, hlegal.2.1⟩)
      (by simpa using hleg)
  · intro t ht
    simp only [polygon, if_pos ht.2]
    ext i <;> simp [AffineMap.lineMap_apply] <;> ring
  · intro t
    constructor
    · simpa using (hasDerivAt_const_mul s).const_add k
    · exact hasDerivAt_const t chi0

#print axioms lawful_probability_continuation_not_affine
end D5.S3.Quantum.Fibers.DoubleWallAffineContinuation
