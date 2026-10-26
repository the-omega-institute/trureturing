/- GID: D5/S3/Observer/Linear/GainRaySuccessPolynomial
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRaySuccessPolynomial
   mirror-E: none(waiver:actual-chart-success-polynomials)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Funext]
   utility: none
   digest: Denominator-cleared native chart wedges contain all actual successes and detect failure of universal collinearity. -/

import D5.S3.Observer.Linear.GainRaySources
import Mathlib.Algebra.MvPolynomial.Funext
import D5.S3.Quantum.Algebra.GenericLieLength

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

abbrev ChartPolynomial (d : ℕ) := MvPolynomial (Fin (d+4)) ℝ

/-- Coordinates are x,r, the d+1 ordinary coefficients, and the drift. -/
def chartParameters (d : ℕ) (x r : ℝ) (β : Coeff d) (δ : ℝ) : Fin (d+4) → ℝ :=
  fun i => if h : i.val < 2 then (if i.val = 0 then x else r)
    else if h' : i.val < d+3 then β ⟨i.val-2, by omega⟩ else δ

def chartDenominator (d : ℕ) : ChartPolynomial d :=
  1 + MvPolynomial.X 0 * MvPolynomial.X 1

def chartTracePolynomial (d : ℕ) (A : Mat) : ChartPolynomial d :=
  MvPolynomial.C (A 0 0) + MvPolynomial.C (A 0 1) * MvPolynomial.X 0 +
    MvPolynomial.C (A 1 0) * MvPolynomial.X 1 +
    MvPolynomial.C (A 1 1) * MvPolynomial.X 0 * MvPolynomial.X 1

def chartReadPolynomial (d : ℕ) (w : List Bool) (i : Fin (w.length+1)) : ChartPolynomial d :=
  (∑ k : Fin (d+1), MvPolynomial.C ((i.val : ℝ)^k.val) *
      MvPolynomial.X ⟨k.val+2, by omega⟩) *
    chartTracePolynomial d (acquisition (w.take i.val)) +
      MvPolynomial.X ⟨d+3, by omega⟩ * chartDenominator d

def chartOutputPolynomial (d : ℕ) (w : List Bool) (C : Readout d w)
    (k : Fin (d+1)) : ChartPolynomial d :=
  ∑ i : Fin (w.length+1), MvPolynomial.C (C k i) * chartReadPolynomial d w i

/-- The polynomial is the actual output wedge multiplied by the positive source denominator. -/
def chartWedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (j k : Fin (d+1)) : ChartPolynomial d :=
  MvPolynomial.X ⟨j.val+2, by omega⟩ * chartOutputPolynomial d w C k -
    MvPolynomial.X ⟨k.val+2, by omega⟩ * chartOutputPolynomial d w C j

private theorem parameter_coeff (d : ℕ) (x r : ℝ) (β : Coeff d) (δ : ℝ)
    (k : Fin (d+1)) : chartParameters d x r β δ ⟨k.val+2, by omega⟩ = β k := by
  simp [chartParameters, show ¬k.val+2 < 2 by omega, show k.val+2 < d+3 by omega]

private theorem eval_chart_trace (d : ℕ) (A : Mat) (x r : ℝ) (β : Coeff d) (δ : ℝ) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartTracePolynomial d A) =
      Matrix.trace (A * !![1,r;x,x*r]) := by
  simp [chartTracePolynomial, chartParameters, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem eval_chart_read (d : ℕ) (w : List Bool) (x r : ℝ)
    (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hn : β ≠ 0) (δ : ℝ)
    (i : Fin (w.length+1)) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartReadPolynomial d w i) =
      (1+x*r) * readings (chartWorld d x r hx hr β hn δ) w i := by
  have hd : 1+x*r ≠ 0 := ne_of_gt (show 0 < 1+x*r by positivity)
  simp only [chartReadPolynomial, map_add, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, parameter_coeff, eval_chart_trace]
  have hp : chartParameters d x r β δ ⟨d+3, by omega⟩ = δ := by simp [chartParameters]
  have he : MvPolynomial.eval (chartParameters d x r β δ) (chartDenominator d) = 1+x*r := by
    simp [chartDenominator, chartParameters]
  rw [hp, he]
  simp only [readings, readAt, chartWorld, sourceChart, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, gain, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  rw [show (∑ k : Fin (d+1), (i.val : ℝ)^k.val * β k) =
      ∑ k : Fin (d+1), β k * (i.val : ℝ)^k.val by
        apply Finset.sum_congr rfl; intro k _; ring]
  field_simp
  <;> ring

/-- Evaluation agrees with the literal native output at every legal positive chart point. -/
theorem eval_chart_wedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hn : β ≠ 0) (δ : ℝ)
    (j k : Fin (d+1)) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) =
      (1+x*r) * (β j * C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) k -
        β k * C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) j) := by
  simp only [chartWedge, map_sub, map_mul, MvPolynomial.eval_X, parameter_coeff,
    chartOutputPolynomial, map_sum, MvPolynomial.eval_C,
    eval_chart_read d w x r hx hr β hn δ]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [← mul_assoc, mul_comm _ (1+x*r), mul_assoc, ← Finset.mul_sum]
  ring

theorem collinear_of_wedges {d : ℕ} (β v : Coeff d) (hn : β ≠ 0)
    (h : ∀ j k, β j * v k - β k * v j = 0) : Collinear β v := by
  have hex : ∃ j, β j ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hn (funext hh)
  obtain ⟨j, hj⟩ := hex
  refine ⟨v j / β j, ?_⟩
  ext k
  have hh := h j k
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  nlinarith

/-- A nonzero wedge exists precisely when whole-domain universal collinearity fails. -/
theorem chart_wedge_nonzero_iff (d : ℕ) (w : List Bool) (C : Readout d w) :
    (∃ j k, chartWedge d w C j k ≠ 0) ↔
      ¬ (∀ W : World d, Collinear W.coeff (C.mulVec (readings W w))) := by
  constructor
  · rintro ⟨j,k,hp⟩ hall
    apply hp
    apply MvPolynomial.funext_set
      (fun i : Fin (d+4) => if i.val < 2 then Set.Ioi 0 else Set.univ)
      (fun i => by
        split_ifs
        · exact Set.Ioi_infinite 0
        · exact Set.infinite_univ)
    intro a ha
    let x := a 0
    let r := a 1
    let β : Coeff d := fun k => a ⟨k.val+2, by omega⟩
    let δ := a ⟨d+3, by omega⟩
    have hx : 0 < x := by simpa [x] using ha 0 (Set.mem_univ _)
    have hr : 0 < r := by simpa [r] using ha 1 (Set.mem_univ _)
    have he : chartParameters d x r β δ = a := by
      ext i
      dsimp [chartParameters, x, r, β, δ]
      split_ifs with hi hz hi'
      · congr; exact Fin.ext hz.symm
      · have hv : i.val = 1 := by omega
        congr; exact Fin.ext hv.symm
      · exact congrArg a (Fin.ext (by dsimp; omega))
      · exact congrArg a (Fin.ext (by dsimp; omega))
    by_cases hn : β = 0
    · have hj : a ⟨j.val+2, by omega⟩ = 0 := congrFun hn j
      have hk : a ⟨k.val+2, by omega⟩ = 0 := congrFun hn k
      simp [chartWedge, hj, hk]
    · rw [← he, eval_chart_wedge d w C x r hx hr β hn δ]
      obtain ⟨s, hs⟩ := hall (chartWorld d x r hx hr β hn δ)
      change C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) = s • β at hs
      simp only [hs, Pi.smul_apply, smul_eq_mul, map_zero]
      ring
  · intro hn
    by_contra hh
    push_neg at hh
    apply hn
    intro W
    obtain ⟨x,r,hx,hr,he,-,-⟩ := source_chart_exact W.source W.legal
    have hw : W = chartWorld d x r hx hr W.coeff W.nonzero W.drift := by
      cases W
      simp_all [chartWorld]
    rw [hw]
    apply collinear_of_wedges _ _ W.nonzero
    intro j k
    have hv := eval_chart_wedge d w C x r hx hr W.coeff W.nonzero W.drift j k
    rw [hh j k, map_zero] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_left (ne_of_gt (by positivity))

/-- Every actual nonzero success, of either sign, lies in each chart wedge zero set. -/
theorem success_chart_wedge_zero (d : ℕ) (w : List Bool) (C : Readout d w)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hn : β ≠ 0) (δ : ℝ)
    (hs : Succeeds (chartWorld d x r hx hr β hn δ) w C) (j k : Fin (d+1)) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) = 0 := by
  rw [eval_chart_wedge d w C x r hx hr β hn δ]
  obtain ⟨s, -, hs⟩ := hs
  change C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) = s • β at hs
  simp only [hs, Pi.smul_apply, smul_eq_mul]
  ring

/-- Actual chart success is contained in a nonzero polynomial zero set of ambient measure zero. -/
theorem chart_success_certificate (d : ℕ) (w : List Bool) (C : Readout d w)
    (hu : ¬ (∀ W : World d, Collinear W.coeff (C.mulVec (readings W w)))) :
    ∃ j k : Fin (d+1), chartWedge d w C j k ≠ 0 ∧
      (∀ x r : ℝ, ∀ hx : 0 < x, ∀ hr : 0 < r, ∀ β : Coeff d, ∀ hn : β ≠ 0,
        ∀ δ : ℝ, Succeeds (chartWorld d x r hx hr β hn δ) w C →
          MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) = 0) ∧
      (∀ᵐ a : Fin (d+4) → ℝ ∂MeasureTheory.volume,
        MvPolynomial.eval a (chartWedge d w C j k) ≠ 0) := by
  obtain ⟨j,k,hp⟩ := (chart_wedge_nonzero_iff d w C).mpr hu
  exact ⟨j,k,hp,fun x r hx hr β hn δ hs =>
      success_chart_wedge_zero d w C x r hx hr β hn δ hs j k,
    D5.S3.Quantum.Algebra.GenericLieLength.ae_mvPolynomial_ne_zero (d+4) _ hp⟩

#print axioms chart_success_certificate
#print axioms chart_wedge_nonzero_iff
#print axioms success_chart_wedge_zero
end D5.S3.Observer.Linear.GainRay
