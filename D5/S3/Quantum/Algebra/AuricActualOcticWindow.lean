/- GID: D5/S3/Quantum/Algebra/AuricActualOcticWindow
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/AuricActualOcticWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual arbitrary-field window operators for the octic cut-free theorem. -/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Tactic

/-! Operators and scalar extension of an arbitrary actual octic window. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.AuricActualOcticWindow

open Module LinearMap
open scoped TensorProduct

variable {F D : Type*} [Field F] [Field D] [Algebra F D]

/-- The original quotient set, including zero whenever the window is nonzero. -/
def quotientSet (W : Submodule F D) : Set D :=
  {a | ∃ u ∈ W, ∃ v ∈ W, v ≠ 0 ∧ a = u / v}

/-- Multiplication in the original field followed by its actual quotient map. -/
def obstruction (W : Submodule F D) (a : D) : W →ₗ[F] D ⧸ W :=
  W.mkQ ∘ₗ (LinearMap.mulLeft F a) ∘ₗ W.subtype

private theorem obstruction_injective (W : Submodule F D) {a : D}
    (ha : a ∉ quotientSet W) : Function.Injective (obstruction W a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro w hw
    have haw : a * (w : D) ∈ W := by
      simpa [obstruction] using hw
    have hw0 : (w : D) = 0 := by
      by_contra hn
      exact ha ⟨a * w, haw, w, w.property, hn, (mul_div_cancel_right₀ a hn).symm⟩
    simpa using hw0
  · exact bot_le

private def obstructionEquiv [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) : W ≃ₗ[F] D ⧸ W :=
  LinearEquiv.ofBijective (obstruction W a)
    ⟨obstruction_injective W ha,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        have h := W.finrank_quotient_add_finrank
        omega)).mp (obstruction_injective W ha)⟩

/-- The original operator i_W A_W(a)⁻¹ π_W; no normalization of W is used. -/
private def actualOperator [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) : D →ₗ[F] D :=
  W.subtype ∘ₗ (obstructionEquiv W hD hW a ha).symm.toLinearMap ∘ₗ W.mkQ

private theorem actualOperator_kernel [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) :
    LinearMap.ker (actualOperator W hD hW a ha) = W := by
  ext x
  change (↑((obstructionEquiv W hD hW a ha).symm (W.mkQ x)) : D) = 0 ↔ x ∈ W
  rw [Submodule.coe_eq_zero, (obstructionEquiv W hD hW a ha).symm.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero W

private theorem actualOperator_range [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) :
    LinearMap.range (actualOperator W hD hW a ha) = W := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((obstructionEquiv W hD hW a ha).symm (W.mkQ y)).property
  · intro hx
    obtain ⟨y, hy⟩ := W.mkQ_surjective ((obstructionEquiv W hD hW a ha) ⟨x, hx⟩)
    refine ⟨y, ?_⟩
    change ↑((obstructionEquiv W hD hW a ha).symm (W.mkQ y)) = x
    rw [hy, LinearEquiv.symm_apply_apply]

private theorem actualOperator_square_zero [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) :
    (actualOperator W hD hW a ha).comp (actualOperator W hD hW a ha) = 0 := by
  ext x
  change actualOperator W hD hW a ha (actualOperator W hD hW a ha x) = 0
  apply (LinearMap.mem_ker).mp
  rw [actualOperator_kernel]
  exact (actualOperator_range W hD hW a ha).le ⟨x, rfl⟩

section Splitting

variable (F D) (K : Type*) [Field K] [Algebra F K]

/-- Evaluation uses all actual F-embeddings of D, with their literal labels. -/
private def splitHom : K ⊗[F] D →ₐ[K] ((D →ₐ[F] K) → K) :=
  AlgHom.liftEquiv F K D _ (AlgHom.pi fun σ : D →ₐ[F] K => σ)

private theorem splitHom_tmul (c : K) (d : D) (σ : D →ₐ[F] K) :
    splitHom F D K (c ⊗ₜ[F] d) σ = c * σ d := rfl

private theorem splitHom_surjective [FiniteDimensional F D] :
    Function.Surjective (splitHom F D K) := by
  classical
  let f := (splitHom F D K).toLinearMap
  by_contra hn
  have hr : LinearMap.range f < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    exact hn (LinearMap.range_eq_top.mp he))
  obtain ⟨φ, hφ, hvan⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hr inferInstance
  have hzero (z : K ⊗[F] D) : φ (f z) = 0 := by
    have hz : φ (f z) ∈ (LinearMap.range f).map φ := ⟨f z, ⟨z, rfl⟩, rfl⟩
    rw [hvan] at hz
    exact hz
  have hrel : ∑ σ : D →ₐ[F] K,
      φ (Pi.single σ 1) • σ.toLinearMap = 0 := by
    ext d
    have heq : (fun σ : D →ₐ[F] K => σ d) =
        ∑ σ : D →ₐ[F] K, (σ d) • Pi.single σ 1 := by
      ext τ
      simp [Pi.single_apply]
    have hh := hzero (1 ⊗ₜ[F] d)
    have heval : f (1 ⊗ₜ[F] d) = (fun σ : D →ₐ[F] K => σ d) := by
      ext σ
      change 1 * σ d = σ d
      exact one_mul _
    rw [heval] at hh
    rw [heq, map_sum] at hh
    simpa [mul_comm] using hh
  have hc : ∀ σ : D →ₐ[F] K, φ (Pi.single σ 1) = 0 :=
    Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap F D K) _ hrel
  apply hφ
  apply (Pi.basisFun K (D →ₐ[F] K)).ext
  intro σ
  simpa using hc σ

private def splitEquiv [FiniteDimensional F D] [Algebra.IsSeparable F D]
    (hK : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits) :
    K ⊗[F] D ≃ₐ[K] ((D →ₐ[F] K) → K) :=
  AlgEquiv.ofBijective (splitHom F D K) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
        AlgHom.card_of_splits F D K hK])).mpr (splitHom_surjective F D K),
    splitHom_surjective F D K⟩

end Splitting

section IdealizerDescent

variable (K : Type*) [Field K] [Algebra F K]
variable {ι : Type*} [Fintype ι] (b : Basis ι F K)

private def tensorCoeff (i : ι) : K ⊗[F] D →ₗ[F] D :=
  (TensorProduct.lid F D).toLinearMap ∘ₗ
    TensorProduct.map (b.coord i) (LinearMap.id : D →ₗ[F] D)

private theorem tensorCoeff_tmul (i : ι) (c : K) (d : D) :
    tensorCoeff K b i (c ⊗ₜ[F] d) = b.repr c i • d := by
  simp [tensorCoeff]

private theorem tensor_reconstruct (z : K ⊗[F] D) :
    ∑ i, b i ⊗ₜ[F] tensorCoeff K b i z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
      simp_rw [tensorCoeff_tmul, ← TensorProduct.smul_tmul]
      rw [← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy =>
      simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [hx, hy]

private theorem tensorCoeff_mem (W : Submodule F D) (i : ι)
    {z : K ⊗[F] D} (hz : z ∈ W.baseChange K) : tensorCoeff K b i z ∈ W := by
  obtain ⟨v, rfl⟩ := hz
  induction v using TensorProduct.inductionOn with
  | tmul c w =>
      simpa only [LinearMap.baseChange_tmul, tensorCoeff_tmul, Submodule.subtype_apply] using
        W.smul_mem (b.repr c i) w.property
  | add x y hx hy =>
      simpa only [map_add] using W.add_mem hx hy

private theorem tensorCoeff_mul_original (i : ι) (z : K ⊗[F] D) (w : D) :
    tensorCoeff K b i (z * (1 ⊗ₜ[F] w)) = tensorCoeff K b i z * w := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, tensorCoeff_tmul,
        smul_mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

/-- The hypothesis is exactly the idealizer of the original actual window. -/
def ScalarIdealizer (W : Submodule F D) : Prop :=
  ∀ c : D, (∀ w ∈ W, c * w ∈ W) → c ∈ Set.range (algebraMap F D)

private theorem tensor_stabilizer_coefficients (W : Submodule F D)
    (hW : ScalarIdealizer W) (z : K ⊗[F] D)
    (hz : ∀ w ∈ W, z * (1 ⊗ₜ[F] w) ∈ W.baseChange K) :
    ∀ i, tensorCoeff K b i z ∈ Set.range (algebraMap F D) := by
  intro i
  apply hW
  intro w hw
  rw [← tensorCoeff_mul_original]
  exact tensorCoeff_mem K b W i (hz w hw)

include b in
private theorem split_stabilizer_constant [FiniteDimensional F D]
    (W : Submodule F D) (hW : ScalarIdealizer W) (z : K ⊗[F] D)
    (hz : ∀ w ∈ W, z * (1 ⊗ₜ[F] w) ∈ W.baseChange K) :
    ∀ σ τ : D →ₐ[F] K, splitHom F D K z σ = splitHom F D K z τ := by
  intro σ τ
  have hc := tensor_stabilizer_coefficients K b W hW z hz
  rw [← tensor_reconstruct K b z]
  simp only [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨c, he⟩ := hc i
  rw [splitHom_tmul, splitHom_tmul, ← he, σ.commutes, τ.commutes]

end IdealizerDescent

section ActualSplitWindow

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [Algebra.IsSeparable F D]
variable (hK : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits)

/-- The image of K tensor W under the canonical evaluation splitting. -/
private def splitWindow (W : Submodule F D) : Submodule K ((D →ₐ[F] K) → K) :=
  (W.baseChange K).map (splitEquiv F D K hK).toLinearMap

private theorem splitWindow_mem_iff (W : Submodule F D) (z : K ⊗[F] D) :
    splitEquiv F D K hK z ∈ splitWindow K hK W ↔ z ∈ W.baseChange K := by
  constructor
  · rintro ⟨v, hv, he⟩
    have : v = z := (splitEquiv F D K hK).injective he
    exact this ▸ hv
  · intro hz
    exact ⟨z, hz, rfl⟩

private theorem splitWindow_finrank (W : Submodule F D) :
    finrank K (splitWindow K hK W) = finrank F W := by
  rw [splitWindow, Submodule.finrank_map_eq]
  rw [← (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq, Module.finrank_baseChange]

private theorem actual_split_diagonal_stabilizer [FiniteDimensional F K]
    (W : Submodule F D) (hW : ScalarIdealizer W)
    (c : (D →ₐ[F] K) → K)
    (hc : ∀ x ∈ splitWindow K hK W, c * x ∈ splitWindow K hK W) :
    ∀ σ τ, c σ = c τ := by
  let e := splitEquiv F D K hK
  let z := e.symm c
  have hz : ∀ w ∈ W, z * (1 ⊗ₜ[F] w) ∈ W.baseChange K := by
    intro w hw
    apply (splitWindow_mem_iff K hK W _).mp
    rw [map_mul, LinearEquiv.coe_coe, AlgEquiv.apply_symm_apply]
    apply hc
    exact (splitWindow_mem_iff K hK W _).mpr (W.tmul_mem_baseChange_of_mem 1 hw)
  have hh := split_stabilizer_constant K (Module.finBasis F K) W hW z hz
  intro σ τ
  simpa only [z, e, ← AlgEquiv.toAlgHom_eq_coe, AlgEquiv.apply_symm_apply] using hh σ τ

end ActualSplitWindow

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
