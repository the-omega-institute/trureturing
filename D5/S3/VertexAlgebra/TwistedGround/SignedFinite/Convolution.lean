/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/Convolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/Convolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rectangular convolution and its associative scalar-series realization. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.JointSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Nat

noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite

/-- Every sum is finite, even when source indices later increase in J inversion. -/
def conv (a b : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
    a i j * b (p-i) (q-j)

private def series (a : ℕ → ℕ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun p => PowerSeries.mk (a p)

private theorem series_injective : Function.Injective series := by
  intro a b he
  funext p q
  have hh := congrArg (fun s => PowerSeries.coeff q (PowerSeries.coeff p s)) he
  simpa [series] using hh

private theorem series_conv (a b : ℕ → ℕ → ℂ) : series (conv a b) = series a * series b := by
  apply PowerSeries.ext
  intro p
  apply PowerSeries.ext
  intro q
  simp only [series, PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum]
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

theorem conv_assoc (a b c : ℕ → ℕ → ℂ) : conv (conv a b) c = conv a (conv b c) := by
  apply series_injective
  simp only [series_conv, mul_assoc]

theorem conv_comm (a b : ℕ → ℕ → ℂ) : conv a b = conv b a := by
  apply series_injective
  simp only [series_conv, mul_comm]

theorem conv_atom (i j : ℕ) (c : ℂ) (a : ℕ → ℕ → ℂ) :
    conv (atom i j c) a = fun p q => c * shift i j a p q := by
  funext p q
  by_cases hi : i ≤ p
  · by_cases hj : j ≤ q
    · simp [conv, atom, shift, ite_and, hi, hj, Finset.sum_ite_irrel,
        Finset.mem_range.mpr (show i < p+1 by omega),
        Finset.mem_range.mpr (show j < q+1 by omega)]
    · simp [conv, atom, shift, ite_and, hj, Finset.sum_ite_irrel,
        show ¬j < q+1 by omega]
  · simp [conv, atom, shift, ite_and, hi, Finset.sum_ite_irrel,
      show ¬i < p+1 by omega]

theorem conv_one (a : ℕ → ℕ → ℂ) : conv (atom 0 0 1) a = a := by
  simpa [shift] using conv_atom 0 0 1 a

theorem conv_add (a b c : ℕ → ℕ → ℂ) :
    conv (fun p q => a p q + b p q) c = fun p q => conv a c p q + conv b c p q := by
  funext p q
  simp [conv, add_mul, Finset.sum_add_distrib]

theorem conv_scale (z : ℂ) (a b : ℕ → ℕ → ℂ) :
    conv (fun p q => z * a p q) b = fun p q => z * conv a b p q := by
  funext p q
  simp [conv, Finset.mul_sum, mul_assoc]

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
