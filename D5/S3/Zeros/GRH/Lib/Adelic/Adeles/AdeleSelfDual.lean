/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdeleSelfDual
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Adeles/AdeleSelfDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Adeles.AdeleSelfDual. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Adeles/AdeleSelfDual.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdditiveCharBasic
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Self-duality of a number field in its adeles; strong approximation; Poisson inequality
(known result; see Lib.Adelic.Adeles.OneSidedPoisson).

This file: Rational scalars and matrices are their own annihilators in the adeles. -/

open NumberField Matrix Circle


variable {E m n : Type _} [Field E] [NumberField E]
attribute [local simp] AddChar.map_add_eq_mul norm_coe coe_eq_one add_mul mul_add ratAdeles
  ratMatrices trace single_apply ite_and
attribute [local simp ←] map_mul map_sum
seal stdAddChar

lemma ψf_half [IsCMField E] x : ψf E ((2⁻¹ : E) * (x + star x)) = ψf E x := by
  simpa [ψf_star (_ * star _)] using congr(ψf E ($(add_halves (1 : E)) * x))

lemma stdAddChar_half {E : Type _} [Field E] [CMType E]
    x : stdAddChar E (toAdele 2⁻¹ * (x + star x)) =
  stdAddChar E x := by simp [stdAddChar, ψf_half, -mul_add, ← two_mul, map_ofNat]

variable [IsTotallyComplex E] [PlaceEmbedding E] [Fintype m] [Fintype n]

/-- Self-duality of the adeles (Tate): a ↦ (x ↦ ψ(ax)) is an injective homomorphism from E to
continuous unitary characters of the adeles trivial on E, and the common kernel lies in E.

Known result: self-duality of a number field in its adeles. -/
instance isDualFamily_ratAdeles : IsDualFamily (ratAdeles E) (stdAddChar E <| toAdele · * ·) := by
  refine' {eq_zero_of_forall_eq_one a h := (map_eq_zero
    toAdele).1 (eq_zero_of_forall_stdAddChar_eq_one _), periodic _ := ⟨by fun_prop, _⟩, ..}
    <;> simp_all [↓mem_ratAdeles_of_psi, mul_comm]

instance isDualFamily_ratMatrices :
  IsDualFamily (ratMatrices E m n) (stdAddChar E <| trace <| @map n m E _ · toAdele * ·) := by
  refine' {periodic _ := ⟨by fun_prop, _⟩, mem_of_forall_eq_one x h := mem_ratMatrices.2 fun i j ↦
    mem_ratAdeles_of_psi _, eq_zero_of_forall_eq_one a h := ext fun i j ↦
    isDualFamily_ratAdeles.6 _ _, ..} <;> try simp [mul_apply]
  all_goals simpa [mul_apply] using (h <| .single j i ·)
