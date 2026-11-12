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
open scoped Classical

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
  rw [splitWindow, LinearEquiv.finrank_map_eq]
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
    rw [map_mul]
    change e (e.symm c) * e (1 ⊗ₜ[F] w) ∈ splitWindow K hK W
    rw [AlgEquiv.apply_symm_apply]
    apply hc
    exact (splitWindow_mem_iff K hK W _).mpr (W.tmul_mem_baseChange_of_mem 1 hw)
  have hh := split_stabilizer_constant K (Module.finBasis F K) W hW z hz
  intro σ τ
  specialize hh σ τ
  change e (e.symm c) σ = e (e.symm c) τ at hh
  simpa only [AlgEquiv.apply_symm_apply] using hh

end ActualSplitWindow

section CoordinateRanks

variable {K Ω : Type*} [Field K] [Fintype Ω] [DecidableEq Ω]

private def coordinateProject (S : Finset Ω) : (Ω → K) →ₗ[K] (Ω → K) where
  toFun x i := if i ∈ S then x i else 0
  map_add' x y := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i ∈ S <;> simp [h]

private def projected (U : Submodule K (Ω → K)) (S : Finset Ω) :
    Submodule K (Ω → K) := U.map (coordinateProject S)

private def rowRank (U : Submodule K (Ω → K)) (S : Finset Ω) : ℕ :=
  finrank K (projected U S)

private def coordinateKernel (U : Submodule K (Ω → K)) (S : Finset Ω) : Submodule K U :=
  LinearMap.ker ((coordinateProject S).domRestrict U)

private theorem mem_coordinateKernel (U : Submodule K (Ω → K)) (S : Finset Ω) (x : U) :
    x ∈ coordinateKernel U S ↔ ∀ i ∈ S, (x : Ω → K) i = 0 := by
  change coordinateProject S (x : Ω → K) = 0 ↔ _
  constructor
  · intro hx i hi
    simpa [coordinateProject, hi] using congrFun hx i
  · intro hx
    ext i
    by_cases hi : i ∈ S <;> simp [coordinateProject, hi, hx]

private theorem coordinate_rank_nullity (U : Submodule K (Ω → K)) (S : Finset Ω) :
    rowRank U S + finrank K (coordinateKernel U S) = finrank K U := by
  simpa only [rowRank, projected, coordinateKernel, LinearMap.range_domRestrict] using
    LinearMap.finrank_range_add_finrank_ker ((coordinateProject S).domRestrict U)

private theorem rowRank_empty (U : Submodule K (Ω → K)) : rowRank U ∅ = 0 := by
  have he : (coordinateProject (∅ : Finset Ω) : (Ω → K) →ₗ[K] (Ω → K)) = 0 := by
    ext x i
    simp [coordinateProject]
  simp [rowRank, projected, he]

private theorem rowRank_univ (U : Submodule K (Ω → K)) : rowRank U Finset.univ = finrank K U := by
  have he : (coordinateProject (Finset.univ : Finset Ω) : (Ω → K) →ₗ[K] (Ω → K)) = .id := by
    ext x i
    simp [coordinateProject]
  simp [rowRank, projected, he]

private theorem rowRank_mono (U : Submodule K (Ω → K)) {S T : Finset Ω} (h : S ⊆ T) :
    rowRank U S ≤ rowRank U T := by
  have hk : coordinateKernel U T ≤ coordinateKernel U S := by
    intro x hx
    rw [mem_coordinateKernel] at hx ⊢
    exact fun i hi => hx i (h hi)
  have hl := Submodule.finrank_mono hk
  have hs := coordinate_rank_nullity U S
  have ht := coordinate_rank_nullity U T
  omega

private theorem rowRank_submodular (U : Submodule K (Ω → K)) (S T : Finset Ω) :
    rowRank U (S ∪ T) + rowRank U (S ∩ T) ≤ rowRank U S + rowRank U T := by
  have hc : coordinateKernel U (S ∪ T) = coordinateKernel U S ⊓ coordinateKernel U T := by
    ext x
    simp only [Submodule.mem_inf, mem_coordinateKernel, Finset.mem_union]
    aesop
  have hi : coordinateKernel U S ⊔ coordinateKernel U T ≤ coordinateKernel U (S ∩ T) := by
    apply sup_le
    · intro x hx
      rw [mem_coordinateKernel] at hx ⊢
      exact fun i hi => hx i (Finset.mem_inter.mp hi).1
    · intro x hx
      rw [mem_coordinateKernel] at hx ⊢
      exact fun i hi => hx i (Finset.mem_inter.mp hi).2
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (coordinateKernel U S) (coordinateKernel U T)
  have hl := Submodule.finrank_mono hi
  have hS := coordinate_rank_nullity U S
  have hT := coordinate_rank_nullity U T
  have hC := coordinate_rank_nullity U (S ∪ T)
  have hI := coordinate_rank_nullity U (S ∩ T)
  rw [hc] at hC
  omega

private theorem project_add_complement (S : Finset Ω) (x : Ω → K) :
    coordinateProject S x + coordinateProject Sᶜ x = x := by
  ext i
  by_cases h : i ∈ S <;> simp [coordinateProject, h]

private theorem projected_disjoint (U : Submodule K (Ω → K)) (S : Finset Ω) :
    Disjoint (projected U S) (projected U Sᶜ) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  rintro x ⟨⟨v, hv, rfl⟩, w, hw, he⟩
  change coordinateProject S v = 0
  ext i
  have hi := congrFun he i
  by_cases hs : i ∈ S <;> simp_all [coordinateProject]

private theorem window_le_projected_sup (U : Submodule K (Ω → K)) (S : Finset Ω) :
    U ≤ projected U S ⊔ projected U Sᶜ := by
  intro x hx
  rw [← project_add_complement S x]
  exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩

private theorem projection_stable_of_rank_equality (U : Submodule K (Ω → K))
    (S : Finset Ω) (h : rowRank U S + rowRank U Sᶜ = finrank K U) :
    ∀ x ∈ U, coordinateProject S x ∈ U := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (projected U S) (projected U Sᶜ)
  rw [(projected_disjoint U S).eq_bot, finrank_bot, add_zero] at hd
  have he : U = projected U S ⊔ projected U Sᶜ :=
    Submodule.eq_of_le_of_finrank_eq (window_le_projected_sup U S)
      (h.symm.trans hd.symm)
  intro x hx
  rw [he]
  exact (show projected U S ≤ projected U S ⊔ projected U Sᶜ from le_sup_left)
    (show coordinateProject S x ∈ projected U S from ⟨x, hx, rfl⟩)

end CoordinateRanks

section ActualConnectivity

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [Algebra.IsSeparable F D] [FiniteDimensional F K]
variable (hK : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits)

private theorem actual_row_rank_connected (W : Submodule F D) (hW : ScalarIdealizer W)
    (S : Finset (D →ₐ[F] K)) (hs : S.Nonempty) (ht : Sᶜ.Nonempty) :
    finrank F W < rowRank (splitWindow K hK W) S + rowRank (splitWindow K hK W) Sᶜ := by
  classical
  let U := splitWindow K hK W
  have hle := Submodule.finrank_mono (window_le_projected_sup U S)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (projected U S) (projected U Sᶜ)
  rw [(projected_disjoint U S).eq_bot, finrank_bot, add_zero] at hd
  have hU : finrank K U = finrank F W := splitWindow_finrank K hK W
  by_contra hn
  have he : rowRank U S + rowRank U Sᶜ = finrank K U := by
    have hnr : rowRank U S + rowRank U Sᶜ ≤ finrank F W := Nat.le_of_not_gt hn
    change finrank K (projected U S) + finrank K (projected U Sᶜ) ≤ finrank F W at hnr
    change finrank K (projected U S) + finrank K (projected U Sᶜ) = finrank K U
    omega
  let c : (D →ₐ[F] K) → K := fun σ => if σ ∈ S then 1 else 0
  have hc : ∀ x ∈ U, c * x ∈ U := by
    intro x hx
    have hx' := projection_stable_of_rank_equality U S he x hx
    convert hx' using 1
    ext σ
    by_cases h : σ ∈ S <;> simp [c, coordinateProject, h]
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨τ, hτ⟩ := ht
  have hh := actual_split_diagonal_stabilizer K hK W hW c hc σ τ
  simpa [c, hσ, Finset.mem_compl.mp hτ] using hh

end ActualConnectivity

section GaloisLabels

variable (K : Type*) [Field K] [Algebra F K]

private instance embeddingAction : MulAction (K ≃ₐ[F] K) (D →ₐ[F] K) where
  smul g σ := g.toAlgHom.comp σ
  one_smul σ := by ext d; rfl
  mul_smul g h σ := by ext d; rfl

private theorem embeddings_transitive [Normal F K] (σ τ : D →ₐ[F] K) :
    ∃ g : K ≃ₐ[F] K, g • σ = τ := by
  let e := σ.equivFieldRange.symm.trans τ.equivFieldRange
  let g := e.liftNormal K
  refine ⟨g, ?_⟩
  ext d
  have h := e.liftNormal_commutes K (σ.equivFieldRange d)
  simpa [g, e] using h

private def galoisTensor (g : K ≃ₐ[F] K) : K ⊗[F] D ≃ₗ[F] K ⊗[F] D :=
  TensorProduct.congr g.toLinearEquiv (LinearEquiv.refl F D)

private theorem split_galois_covariance (g : K ≃ₐ[F] K) (z : K ⊗[F] D)
    (σ : D →ₐ[F] K) :
    splitHom F D K (galoisTensor K g z) (g • σ) = g (splitHom F D K z σ) := by
  induction z using TensorProduct.inductionOn with
  | tmul c d => simp [galoisTensor, splitHom_tmul, embeddingAction]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private theorem galoisTensor_window (W : Submodule F D) (g : K ≃ₐ[F] K)
    {z : K ⊗[F] D} (hz : z ∈ W.baseChange K) :
    galoisTensor K g z ∈ W.baseChange K := by
  obtain ⟨v, rfl⟩ := hz
  induction v using TensorProduct.inductionOn with
  | tmul c w =>
      simpa [galoisTensor] using W.tmul_mem_baseChange_of_mem (g c) w.property
  | add x y hx hy => simpa only [map_add] using (W.baseChange K).add_mem hx hy

end GaloisLabels

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
