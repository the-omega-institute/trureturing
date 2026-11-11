/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Literal six-row APPT supplies the full scalar hypothesis on one original ordered spectrum. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowPhysicalMoments
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowCoupling
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowScalarData
import Mathlib.Tactic

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowPhysicalExtraction
open QutritPerturbationAttainment

/-- The literal diagonal supplies positivity of its bottom-pool scale, both
actual zero slots, and the full scalar hypothesis for its normalized moments.
The head/tail coupling uses exactly the same spectrum and labelling. -/
theorem literal_physical (n : ℕ) (hn : 23 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (ho : Antitone l) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1)
    (happt : APPT (diagonal (fun z => (l (e z) : ℂ)))) :
    let hN : 36 ≤ 6*n := by omega
    let U := SixRowPhysicalMoments.u hN l
    let r := SixRowPhysicalMoments.v hN l/U
    let h : Fin 15 → ℝ := fun i => SixRowPhysicalMoments.heads hN l i/U
    let d : Fin 21 → ℝ := fun i => SixRowPhysicalMoments.tails hN l i/U
    0 < U ∧ h 14 = 0 ∧ d 0 = 0 ∧ SixRowScalarData.PhysicalScalarHyp r
      (∑ i, h i) (∑ i, d i) (∑ i, (h i)^2) (∑ i, (d i)^2) := by
  let hN : 36 ≤ 6*n := by omega
  let U := SixRowPhysicalMoments.u hN l
  let r := SixRowPhysicalMoments.v hN l/U
  let h : Fin 15 → ℝ := fun i => SixRowPhysicalMoments.heads hN l i/U
  let d : Fin 21 → ℝ := fun i => SixRowPhysicalMoments.tails hN l i/U
  let H : ℝ := ∑ i, h i
  let D : ℝ := ∑ i, d i
  let a : ℝ := ∑ i, (h i)^2
  let q : ℝ := ∑ i, (d i)^2
  change 0 < U ∧ h 14 = 0 ∧ d 0 = 0 ∧ SixRowScalarData.PhysicalScalarHyp r H D a q
  have hMoments : 0 < U ∧ SixRowPhysicalMoments.Constraints r h d :=
    SixRowPhysicalMoments.literal_moments n hn e l ho hl hs happt
  obtain ⟨hU, hm⟩ := hMoments
  have hUraw : 0 < l ⟨6*n-21, by omega⟩ := hU
  have hSame : Real.sqrt (∑ i, (r+h i)^2)+q/2 ≤ 2 ∧
      a+2*r*H+15*r^2 ≤ (2-q/2)^2 := by
    simpa only [U, r, h, d, H, a, q, SixRowPhysicalMoments.u,
      SixRowPhysicalMoments.v, SixRowPhysicalMoments.heads, SixRowPhysicalMoments.tails] using
      (SixRowCoupling.literal_coupled n hn e l ho hl happt hUraw)
  have hCap : SixRowPhysicalMoments.cap r =
      SixRowMiddlePolynomial.cn r / SixRowMiddlePolynomial.den r := by
    unfold SixRowPhysicalMoments.cap SixRowMiddlePolynomial.cn SixRowMiddlePolynomial.den
    congr 1 <;> ring
  have hHeadCap : a ≤ (SixRowMiddlePolynomial.cn r / SixRowMiddlePolynomial.den r)*H := by
    rw [← hCap]
    exact hm.head_cap
  have hHeadBox : a ≤ (H-SixRowMiddlePolynomial.cn r / SixRowMiddlePolynomial.den r)^2+
      (SixRowMiddlePolynomial.cn r / SixRowMiddlePolynomial.den r)^2 := by
    rw [← hCap]
    exact hm.head_box
  let s := SixRowMiddlePolynomial.slack r H D
  have hSlack : s = 6-15*r-H-D := rfl
  have hMass : 0 ≤ s := by
    rw [hSlack]
    exact hm.mass
  have hVariance : (5/7)*(a-H^2/15)+(q-D^2/21) ≤ 4*s-s^2/3 := by
    rw [hSlack]
    exact hm.variance
  have hMiddle : SixRowMiddleScalar.Hyp6 r H D a q := by
    constructor <;> first
    | exact hm.H_nonneg
    | exact hm.D_nonneg
    | exact hm.q_nonneg
    | exact hMass
    | exact hm.q_box
    | exact hm.q_mass
    | exact hm.tail_cap
    | exact hm.head_sq
    | exact hHeadCap
    | exact hHeadBox
    | exact hSame.2
    | exact hVariance
  refine ⟨hU, hm.h_zero, hm.d_zero, ?_⟩
  exact {
    toHyp6 := hMiddle
    r_nonneg := hm.r_nonneg
    r_le := hm.r_le
    a_nonneg := hm.a_nonneg
    head_cauchy := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 14)).2
      rw [mul_comm a 14]
      exact hm.head_cauchy
    tail_cauchy := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 20)).2
      rw [mul_comm q 20]
      exact hm.tail_cauchy }

end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowPhysicalExtraction
