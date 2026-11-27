/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/FiniteHeisenberg
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/FiniteHeisenberg
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.FiniteHeisenberg. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/FiniteHeisenberg.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Construction.AdelicHeisenberg
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Finite adelic Heisenberg group, self-dual lattice, additive character, semicharacter and
vacuum. -/

noncomputable section

namespace stdLattice

open NumberField Matrix AddChar Circle WeilData
variable (E ι : Type _) [Field E] [CMType E] [WeilData E] [Fintype ι]

/-- The standard lattice Ô^ι, as an additive subgroup of the finite adelic vectors indexed by ι. -/
def _root_.stdLattice (E ι : Type _) [Field E] [NumberField E] :
    AddSubgroup (ι → 𝔸f E) := (intVectors (Ô E) ι).toAddSubgroup

/-- The complex-valued additive character u ↦ ψ_f(ȷαᾱu) of the finite adeles of E, with ȷ and α
from the Weil data. -/
def psi₀ := coeHom.compAddChar ((ψf E).mulShift (algebraMap E _ j * α.1 * star α.1))

variable {E ι}

/-- The integer c₀ of the Weil data (c₀ + c̄₀ = 1), viewed as a finite adele of E. -/
def traceOneAdele : 𝔸f E := (WeilData.traceOne : E)

/-- The number ½, viewed as a finite adele of E. -/
def half {E : Type _} [Field E] [NumberField E] : 𝔸f E := (2⁻¹ : E)

lemma psi₀_apply z : psi₀ E z = ψf E (algebraMap E _ j * α.1 * star α.1 * z) := rfl

@[simp] lemma norm_psi₀ z : ‖psi₀ E z‖ = 1 := norm_coe _

@[fun_prop] lemma continuous_psi₀ : Continuous (psi₀ E) :=
  continuous_ψf.subtype_val.comp (continuous_const_mul _)

lemma psi₀_star z : psi₀ E (star z) = psi₀ E (-z) := by simp [psi₀, ψf_star (-_), mul_right_comm]

/-- Self-duality of Ô: a finite adele z satisfies ψ₀(zu) = 1 for all u in Ô if and only if z
lies in Ô, where ψ₀ = ψ_f(ȷαᾱ·). -/
lemma forall_psi₀_mul_eq_one_iff z : (∀ u ∈ Ô E, psi₀ E (z * u) = 1) ↔
  z ∈ Ô E := by simpa [psi₀_apply, ← mul_rotate' _ _ z, coe_eq_one, forall_ψf_mul_eq_one] using
  ((exists_reduction_and_idele_generator differentIdeal_ne_bot).elim fun _ ⟨_, _, t,
  _, h, H⟩ ↦ (H _).trans (by simp [mem_Ô, h, -WithZero.inv_exp, WithZero.exp_neg,
    by simpa using ‹WeilData E›.self_dual]))

lemma traceOneAdele_mem : traceOneAdele ∈ Ô E := algebraMap_mem_Ô.2 isIntegral_traceOne

/-- The element c₀ of the Weil data, viewed as a finite adele, satisfies c₀ + c̄₀ = 1. -/
@[simp] lemma traceOneAdele_add_star : traceOneAdele + star traceOneAdele = (1 :
  𝔸f E) := by simp [traceOneAdele, WeilData.traceOne, ← map_add, ← add_div]

omit [WeilData E] in
lemma two_mul_half : 2 * half = (1 : 𝔸f E) := by norm_num [half, two_mul, ← map_add]

omit [WeilData E] in
lemma star_half : star half = @half E .. := by simp [half]

attribute [grind .] traceOneAdele_add_star two_mul_half star_half

lemma psi₀_eq_one_of_mem {o} : o ∈ Ô E →
  psi₀ E o = 1 := by grind [forall_psi₀_mul_eq_one_iff, (Ô E).one_mem]

lemma psi₀_congr {a b o} t : o ∈ Ô E → a = b + (t + star t) + o → psi₀ E a = psi₀ E b := by
  simp_all [map_add_eq_mul, psi₀_star, ← map_add_eq_mul _, psi₀_eq_one_of_mem]

/-- For a finite adelic vector x, the complex number sc(x) = ψ_f(½c₀ȷαᾱ x*x). -/
def semichar (x : ι → _) := psi₀ E (traceOneAdele * half * star x ⬝ᵥ x)

/-- The finite vacuum: the function on finite adelic vectors equal to ψ_f(½c₀ȷαᾱ x*x) for x in
Ô^ι and to 0 otherwise. -/
def finVac x := ite (x ∈ stdLattice E ι) (delta% semichar x) 0

variable (E ι)

/-- The Heisenberg datum on finite adelic vectors indexed by ι with bicharacter β(x,y) =
ψ_f(½ȷαᾱ y*x). -/
def finHeis : Heisenberg (ι → 𝔸f E) := by refine ⟨fun x y ↦ psi₀ E (half * star y ⬝ᵥ x), ?_, ?_,
  fun x ↦ (psi₀ E).2 ▸ psi₀_congr (traceOneAdele * half * star x ⬝ᵥ x) (zero_mem
  _) ?_, ?_, by fun_prop⟩ <;> simp [mul_add, map_add_eq_mul, half, ← star_dotProduct, ← add_mul]
