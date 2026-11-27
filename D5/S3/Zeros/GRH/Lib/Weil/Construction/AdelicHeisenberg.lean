/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/AdelicHeisenberg
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/AdelicHeisenberg
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.AdelicHeisenberg. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/AdelicHeisenberg.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.UpsilonValues
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdeleSelfDual
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.ElementOfMatrix
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Adelic vacuum function and Heisenberg cocycle of the standard hermitian form. -/

open Matrix Real WeilData

/-- The vacuum on adelic vectors: exp(−π ∑_{i,τ} Im(τȷ)|x_{i,τ}|²) times ψ_f(½c₀ȷ x_f*x_f) if
the finite part x_f lies in αÔ^n, and 0 otherwise. -/
noncomputable def vacuumFn {E} [Field E] [CMType E]
  [WeilData E] {n} [Fintype n] (x : n → 𝔸 E) := (-∑ i, ∑ w, π * (Φ w j).im * ‖(x i).1 w‖ ^ 2).exp *
  ite (∀ i, α⁻¹.1 * (x i).2 ∈ Ô E) (ψf E ((traceOne * j / 2 : E) * ∑ i, star (x i).2 * (x i).2)).1 0

/-- The Heisenberg datum on adelic n-space with bicharacter β(x,y)=ψ(½ȷ h(y,x)), h being the
standard hermitian form of signs s. -/
noncomputable def adelicHeis E [Field E] [CMType E]
    [WeilData E] {n} [Fintype n] (s : n → ℤˣ) : Heisenberg (n → 𝔸 E) := by refine ⟨fun x y ↦
  stdAddChar E (toAdele (j / 2) * star y ⬝ᵥ stdForm E s *ᵥ x), ?_, ?_, fun x ↦
  stdAddChar_half (_ : 𝔸 E) ▸ ?_, ?_, .subtype_val (by fun_prop)⟩ <;> simp [mul_add, neg_div,
  AddChar.map_add_eq_mul, ← star_dotProduct, star_mulVec_dotProduct, Circle.norm_coe]
