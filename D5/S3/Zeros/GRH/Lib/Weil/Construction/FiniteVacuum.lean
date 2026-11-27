/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/FiniteVacuum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/FiniteVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.FiniteVacuum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/FiniteVacuum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Construction.FiniteHeisenberg
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Self-dual lattice gives a vacuum for the finite Heisenberg group (lattice model). -/

namespace stdLattice

open NumberField MeasureTheory Measure Matrix AddChar Heisenberg
section

variable {E ι : Type _} [Field E] [NumberField E]

lemma isOpen_stdLattice [Fintype ι] : (stdLattice E ι).IsOpen := isOpen_intVectors isOpen_Ô

end

variable {E ι : Type _} [Field E] [CMType E] {x y z : ι → 𝔸f E}

lemma mem_stdLattice : x ∈ stdLattice .. ↔ ∀ i, x i ∈ Ô E := .rfl

lemma isCompact_stdLattice : IsCompact (stdLattice E ι).carrier := isCompact_pi_infinite fun _ ↦
  isCompact_Ô

variable [Fintype ι]

variable (E) in
/-- The Haar measure on n-tuples of finite adeles of E that gives the lattice Ô^n mass one. -/
noncomputable def _root_.latticeMeasure n [Fintype n] : Measure (n → 𝔸f E) := addHaarMeasure
  ⟨⟨stdLattice E n, isCompact_stdLattice⟩, by simp [isOpen_stdLattice.interior_eq]⟩ deriving
  IsAddHaarMeasure

@[simp] lemma _root_.latticeMeasure_stdLattice : latticeMeasure E ι (stdLattice E ι) = 1 :=
  addHaarMeasure_self

@[simp] lemma star_mulVec_dot_mulVec (g : Gf E ι) x y : star (g.1.1 *ᵥ x) ⬝ᵥ g.1.1 *ᵥ y =
  star x ⬝ᵥ y := by simpa using U.form_mulVec_mulVec g ..

attribute [local simp] mul_mem star_mem_Ô finVac add_mem_cancel_right add_left add_right

omit [Fintype ι] in
lemma smul_mem_stdLattice {r} : r ∈ Ô E → x ∈ stdLattice .. →
  r • x ∈ stdLattice .. := by simp_all [mem_stdLattice]

lemma dot_mem : y ∈ stdLattice .. → z ∈ stdLattice .. → star z ⬝ᵥ y ∈ Ô E :=
  (sum_mem <| by simp [· _, · _])

variable [WeilData E]

lemma semichar_add x y : semichar x * semichar y * (finHeis E ι).β x y = psi₀ E (star traceOneAdele
  * star y ⬝ᵥ x) * semichar (x + y) := by simp [semichar, finHeis, ← map_add_eq_mul]; grind
  [psi₀_congr (traceOneAdele * half * star x ⬝ᵥ y) (zero_mem _), star_mul', star_dotProduct]

lemma finVac_add x : y ∈ stdLattice .. → finVac x * finVac y * (finHeis ..).β x y =
  finVac (x + y) := by simp_all [↓← semichar.eq_1, semichar_add, psi₀_eq_one_of_mem ∘ mul_mem _,
  dot_mem, traceOneAdele_mem]

lemma semichar_mul_self (h : y ∈ stdLattice ..) :
  semichar y * semichar y = 1 := by simpa [h, semichar] using finVac_add (-y) h

lemma mem_stdLattice_iff_psi₀ : x ∈ stdLattice .. ↔ ∀ y ∈ stdLattice .., psi₀ E (star y ⬝ᵥ x) = 1 :=
  ⟨by grind [psi₀_eq_one_of_mem, dot_mem], fun h i ↦ (forall_psi₀_mul_eq_one_iff _).1 fun _ k ↦ by
    simpa [mul_comm] using h _ (smul_mem_stdLattice (star_mem_Ô k) (single_mem_intVectors i))⟩

lemma _root_.integral_psi₀_stdLattice x : ∫ y in stdLattice E ι, psi₀ E (star x ⬝ᵥ y)
  ∂latticeMeasure E ι = ite (x ∈ stdLattice ..) 1 0 := by simp [↓setIntegral_char isOpen_stdLattice,
  map_add_eq_mul, real_def, star_dotProduct x, psi₀_star, map_neg_eq_inv, ← mem_stdLattice_iff_psi₀]

instance isVacuum_finVac :
  (finHeis E ι).IsVacuum (latticeMeasure ..) finVac := have ⟨Z, n⟩ : _ ∧ _ := by aesop
  have c :=
    IsClopen.continuous_indicator ⟨isCompact_stdLattice.isClosed, isOpen_stdLattice⟩ (by fun_prop)
  ⟨c, by simp, n, by grind [→ semichar_mul_self, mul_self_eq_one_iff, finVac, semichar], fun y x ↦
  by rw [← setIntegral_eq_integral_of_ae_compl_eq_zero, setIntegral_congr_fun
      isOpen_stdLattice.measurableSet fun z ↦ ?_,
    integral_const_mul (finVac (x - y) / (finHeis ..).β x y), integral_psi₀_stdLattice
    x] <;> simp_all [-finVac, ↓sub_add_eq_sub_sub_swap, sub_eq_add_neg, add_comm x,
    ← finVac_add]; grind [map_nsmul_eq_pow _ 2 (half * star x ⬝ᵥ z), → semichar_mul_self, finVac,
    semichar, β_mul_β, finHeis], HasCompactSupport.integrable (.intro isCompact_stdLattice Z) c⟩
