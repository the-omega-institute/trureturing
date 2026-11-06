import D5.S3.Arith.Robin.OriginalLocalA

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open D5.S3.Weil.ZeroSum
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Arith.Robin.PrimeFiberPropagation

example (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hγ : 0 < ρ.im) :
    let δ := ρ.re - 1 / 2
    let D := ρ.im + 10
    let m₀ := 100 * D ^ 2 / δ ^ 2
    let m₁ := 500 * D ^ 4 / δ ^ 2
    let B₀ := Real.exp (4 * (28 * m₁ + 20) ^ 2)
    ∃ A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
      Real.sqrt A * (4 * Real.log A + 9) < U A ∧
      ∃ t ∈ Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)),
        let N := Nat.lcmUpto ⌊t⌋₊
        5040 < N ∧
        divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) ∧
        (N : ℝ) ≤ Real.exp (B₀ * Real.log B₀) := by
  exact D5.S3.Arith.Robin.OriginalLocalA.original_zero_robin5040_localA ρ hρ hβ hγ

#print axioms D5.S3.Arith.Robin.OriginalLocalA.original_zero_robin5040_localA
end
