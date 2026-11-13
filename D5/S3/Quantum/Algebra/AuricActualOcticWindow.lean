/- GID: D5/S3/Quantum/Algebra/AuricActualOcticWindow
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/AuricActualOcticWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual arbitrary-field window operators for the octic cut-free theorem. -/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import D5.S3.Quantum.Algebra.AuricOcticRanks
import Mathlib.Tactic

/-! Operators and scalar extension of an arbitrary actual octic window. -/

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

def obstructionEquiv [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) : W ≃ₗ[F] D ⧸ W :=
  LinearEquiv.ofBijective (obstruction W a)
    ⟨obstruction_injective W ha,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        have h := W.finrank_quotient_add_finrank
        omega)).mp (obstruction_injective W ha)⟩

/-- The original operator i_W A_W(a)⁻¹ π_W; no normalization of W is used. -/
def actualOperator [FiniteDimensional F D] (W : Submodule F D)
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
  change g (σ d) = τ d
  have h := e.liftNormal_commutes K (σ.equivFieldRange d)
  simpa [g, e] using h

private def galoisTensor (g : K ≃ₐ[F] K) : K ⊗[F] D ≃ₗ[F] K ⊗[F] D :=
  TensorProduct.congr g.toLinearEquiv (LinearEquiv.refl F D)

private theorem split_galois_covariance (g : K ≃ₐ[F] K) (z : K ⊗[F] D)
    (σ : D →ₐ[F] K) :
    splitHom F D K (galoisTensor K g z) (g • σ) = g (splitHom F D K z σ) := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
      change g c * g (σ d) = g (c * σ d)
      exact (map_mul g c (σ d)).symm
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

section ActualGaloisRanks

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [Algebra.IsSeparable F D] [FiniteDimensional F K]
variable (hK : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits)

private def galoisCoordinates (g : K ≃ₐ[F] K) :
    ((D →ₐ[F] K) → K) ≃+ ((D →ₐ[F] K) → K) where
  toFun x σ := g (x (g⁻¹ • σ))
  invFun x σ := g.symm (x (g • σ))
  left_inv x := by ext σ; simp
  right_inv x := by ext σ; simp
  map_add' x y := by ext σ; simp

private theorem coordinates_smul (g : K ≃ₐ[F] K) (c : K)
    (x : (D →ₐ[F] K) → K) :
    galoisCoordinates K g (c • x) = g c • galoisCoordinates K g x := by
  ext σ
  change g (c * x (g⁻¹ • σ)) = g c * g (x (g⁻¹ • σ))
  exact map_mul g _ _

private theorem coordinates_split (g : K ≃ₐ[F] K) (z : K ⊗[F] D) :
    galoisCoordinates K g (splitEquiv F D K hK z) =
      splitEquiv F D K hK (galoisTensor K g z) := by
  ext τ
  change g (splitHom F D K z (g⁻¹ • τ)) = splitHom F D K (galoisTensor K g z) τ
  have hh := split_galois_covariance K g z (g⁻¹ • τ)
  simpa only [smul_inv_smul] using hh.symm

private theorem coordinates_window (W : Submodule F D) (g : K ≃ₐ[F] K)
    {x : (D →ₐ[F] K) → K} (hx : x ∈ splitWindow K hK W) :
    galoisCoordinates K g x ∈ splitWindow K hK W := by
  obtain ⟨z, hz, rfl⟩ := hx
  change galoisCoordinates K g (splitEquiv F D K hK z) ∈ _
  rw [coordinates_split]
  exact (splitWindow_mem_iff K hK W _).mpr (galoisTensor_window K W g hz)

private theorem coordinates_project (g : K ≃ₐ[F] K) (S : Finset (D →ₐ[F] K))
    (x : (D →ₐ[F] K) → K) :
    galoisCoordinates K g (coordinateProject S x) =
      coordinateProject (orbitSet S g) (galoisCoordinates K g x) := by
  ext σ
  change g (if g⁻¹ • σ ∈ S then x (g⁻¹ • σ) else 0) =
    if σ ∈ orbitSet S g then g (x (g⁻¹ • σ)) else 0
  by_cases h : g⁻¹ • σ ∈ S <;> simp [mem_orbitSet, h]

private theorem coordinates_projected (W : Submodule F D) (g : K ≃ₐ[F] K)
    (S : Finset (D →ₐ[F] K)) {x : (D →ₐ[F] K) → K}
    (hx : x ∈ projected (splitWindow K hK W) S) :
    galoisCoordinates K g x ∈ projected (splitWindow K hK W) (orbitSet S g) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨galoisCoordinates K g y, coordinates_window K hK W g hy,
    (coordinates_project K g S y).symm⟩

private theorem actual_row_rank_galois (W : Submodule F D) (g : K ≃ₐ[F] K)
    (S : Finset (D →ₐ[F] K)) :
    rowRank (splitWindow K hK W) (orbitSet S g) = rowRank (splitWindow K hK W) S := by
  have horb : orbitSet (orbitSet S g) g⁻¹ = S := by
    ext i
    simp [mem_orbitSet]
  let e : projected (splitWindow K hK W) S ≃+
      projected (splitWindow K hK W) (orbitSet S g) :=
    { toFun := fun x => ⟨galoisCoordinates K g x, coordinates_projected K hK W g S x.property⟩
      invFun := fun y => ⟨galoisCoordinates K g⁻¹ y, by
        have hh := coordinates_projected K hK W g⁻¹ (orbitSet S g) y.property
        rwa [horb] at hh⟩
      left_inv := by intro x; apply Subtype.ext; ext σ; simp [galoisCoordinates]
      right_inv := by intro x; apply Subtype.ext; ext σ; simp [galoisCoordinates]
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (galoisCoordinates (D := D) K g)
          (x : (D →ₐ[F] K) → K) (y : (D →ₐ[F] K) → K) }
  have hr := rank_eq_of_equiv_equiv (g : K → K) e g.bijective (by
    intro r x
    apply Subtype.ext
    exact coordinates_smul K g r (x : (D →ₐ[F] K) → K))
  exact (congrArg Cardinal.toNat hr).symm

private theorem actual_strict_row_rank [Normal F K] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (hE : ScalarIdealizer W)
    (S : Finset (D →ₐ[F] K)) (hs : S.Nonempty) (ht : Sᶜ.Nonempty) :
    S.card + 1 ≤ 2 * rowRank (splitWindow K hK W) S := by
  apply invariant_half_rank_strict (splitWindow K hK W)
    ((AlgHom.card_of_splits F D K hK).trans hD)
    ((splitWindow_finrank K hK W).trans hW)
    (embeddings_transitive K) (actual_row_rank_galois K hK W)
    _ S hs ht
  intro T hT hTc
  simpa only [hW] using actual_row_rank_connected K hK W hE T hT hTc

end ActualGaloisRanks

section ActualSplitOperator

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [Algebra.IsSeparable F D] [FiniteDimensional F K]
variable (hK : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits)
variable (W : Submodule F D) (hD : finrank F D = 8) (hW : finrank F W = 4)
variable (a : D) (ha : a ∉ quotientSet W)

private def splitOperator : ((D →ₐ[F] K) → K) →ₗ[K] ((D →ₐ[F] K) → K) :=
  (splitEquiv F D K hK).toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ
    (splitEquiv F D K hK).symm.toLinearMap

private theorem baseOperator_kernel :
    LinearMap.ker ((actualOperator W hD hW a ha).baseChange K) = W.baseChange K := by
  change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor K K
    (actualOperator W hD hW a ha)) = _
  rw [Module.Flat.ker_lTensor_eq, actualOperator_kernel]
  rfl

private theorem baseOperator_range :
    LinearMap.range ((actualOperator W hD hW a ha).baseChange K) = W.baseChange K := by
  ext z
  have hh := congrArg (fun p : Submodule F (K ⊗[F] D) => z ∈ p)
    (LinearMap.lTensor_range K (g := actualOperator W hD hW a ha))
  rw [actualOperator_range] at hh
  exact Iff.of_eq hh

private theorem splitOperator_kernel :
    LinearMap.ker (splitOperator K hK W hD hW a ha) = splitWindow K hK W := by
  ext x
  change (splitEquiv F D K hK)
    ((actualOperator W hD hW a ha).baseChange K ((splitEquiv F D K hK).symm x)) = 0 ↔ _
  have he (y : K ⊗[F] D) : splitEquiv F D K hK y = 0 ↔ y = 0 := by
    constructor
    · intro hy
      apply (splitEquiv F D K hK).injective
      simpa only [map_zero] using hy
    · rintro rfl
      exact map_zero _
  rw [he]
  change (splitEquiv F D K hK).symm x ∈
    LinearMap.ker ((actualOperator W hD hW a ha).baseChange K) ↔ _
  rw [baseOperator_kernel]
  simpa only [AlgEquiv.apply_symm_apply] using
    (splitWindow_mem_iff K hK W ((splitEquiv F D K hK).symm x)).symm

private theorem splitOperator_range :
    LinearMap.range (splitOperator K hK W hD hW a ha) = splitWindow K hK W := by
  rw [splitOperator, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, baseOperator_range]
  rfl

private theorem splitOperator_square_zero :
    (splitOperator K hK W hD hW a ha).comp (splitOperator K hK W hD hW a ha) = 0 := by
  apply LinearMap.ext
  intro x
  change splitOperator K hK W hD hW a ha (splitOperator K hK W hD hW a ha x) = 0
  apply (LinearMap.mem_ker).mp
  rw [splitOperator_kernel, ← splitOperator_range K hK W hD hW a ha]
  exact ⟨x, rfl⟩

private theorem baseOperator_galois (g : K ≃ₐ[F] K) (z : K ⊗[F] D) :
    (actualOperator W hD hW a ha).baseChange K (galoisTensor K g z) =
      galoisTensor K g ((actualOperator W hD hW a ha).baseChange K z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c d => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem splitOperator_covariance (g : K ≃ₐ[F] K)
    (x : (D →ₐ[F] K) → K) :
    splitOperator K hK W hD hW a ha (galoisCoordinates K g x) =
      galoisCoordinates K g (splitOperator K hK W hD hW a ha x) := by
  obtain ⟨z, rfl⟩ := (splitEquiv F D K hK).surjective x
  simp only [coordinates_split, splitOperator, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
  rw [baseOperator_galois]

private theorem splitMatrix_square_zero :
    LinearMap.toMatrix' (splitOperator K hK W hD hW a ha) *
      LinearMap.toMatrix' (splitOperator K hK W hD hW a ha) = 0 := by
  rw [← LinearMap.toMatrix'_mul]
  change LinearMap.toMatrix' ((splitOperator K hK W hD hW a ha).comp
    (splitOperator K hK W hD hW a ha)) = 0
  rw [splitOperator_square_zero, map_zero]

private theorem splitMatrix_rank :
    (LinearMap.toMatrix' (splitOperator K hK W hD hW a ha)).rank = 4 := by
  have hm : (LinearMap.toMatrix' (splitOperator K hK W hD hW a ha)).mulVecLin =
      splitOperator K hK W hD hW a ha :=
    Matrix.toLin'_toMatrix' _
  rw [Matrix.rank, hm, splitOperator_range, splitWindow_finrank, hW]

private theorem galoisCoordinates_single (g : K ≃ₐ[F] K) (τ : D →ₐ[F] K) :
    galoisCoordinates K g (Pi.single τ (1 : K)) = Pi.single (g • τ) (1 : K) := by
  ext σ
  change g ((Pi.single τ (1 : K) : (D →ₐ[F] K) → K) (g⁻¹ • σ)) =
    (Pi.single (g • τ) (1 : K) : (D →ₐ[F] K) → K) σ
  by_cases h : σ = g • τ
  · subst σ
    simp [Pi.single_apply]
  · have hi : g⁻¹ • σ ≠ τ := by
      intro he
      apply h
      have hh := congrArg (g • ·) he
      simpa using hh
    simp [Pi.single_apply, h, hi]

private theorem splitMatrix_covariance (g : K ≃ₐ[F] K) (σ τ : D →ₐ[F] K) :
    LinearMap.toMatrix' (splitOperator K hK W hD hW a ha) (g • σ) (g • τ) =
      g (LinearMap.toMatrix' (splitOperator K hK W hD hW a ha) σ τ) := by
  have hh := congrFun (splitOperator_covariance K hK W hD hW a ha g (Pi.single τ 1))
    (g • σ)
  rw [galoisCoordinates_single] at hh
  change (splitOperator K hK W hD hW a ha) (Pi.single (g • τ) 1) (g • σ) =
    g ((splitOperator K hK W hD hW a ha) (Pi.single τ 1) σ)
  change (splitOperator K hK W hD hW a ha) (Pi.single (g • τ) 1) (g • σ) =
    g ((splitOperator K hK W hD hW a ha) (Pi.single τ 1) (g⁻¹ • (g • σ))) at hh
  simpa only [inv_smul_smul] using hh

end ActualSplitOperator

section ActualCutFree

variable (K : Type*) [Field K] [Algebra F K]
variable [FiniteDimensional F D] [CharZero F] [FiniteDimensional F K] [Normal F K]
variable (hK : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits)

private theorem actual_cut_free (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (hE : ScalarIdealizer W)
    (a : D) (ha : a ∉ quotientSet W) (S : Finset (D →ₐ[F] K))
    (hS2 : 2 ≤ S.card) (hS6 : S.card ≤ 6) :
    2 ≤ crossRank (splitOperator K hK W hD hW a ha) S ∨
    2 ≤ crossRank (splitOperator K hK W hD hW a ha) Sᶜ := by
  apply cut_free_of_actual_ranks (splitWindow K hK W) _
    (splitOperator_kernel K hK W hD hW a ha)
    (splitOperator_range K hK W hD hW a ha)
    ((AlgHom.card_of_splits F D K hK).trans hD)
    ((splitWindow_finrank K hK W).trans hW)
    (embeddings_transitive K) (actual_row_rank_galois K hK W) _ S hS2 hS6
  intro T hT hT8
  apply actual_strict_row_rank K hK W hD hW hE T (Finset.card_pos.mp hT)
  apply Finset.card_pos.mp
  have hc : Tᶜ.card + T.card = 8 := by
    simpa [(AlgHom.card_of_splits F D K hK).trans hD] using Finset.card_compl_add_card T
  omega

/-- The canonical splitting and all cut-free assertions concern the same actual W and n. -/
theorem general43_2_cut_free [Algebra D K] [IsScalarTower F D K]
    (W : Submodule F D) (hD : finrank F D = 8) (hW : finrank F W = 4)
    (hE : {c : D | ∀ w ∈ W, c * w ∈ W} = Set.range (algebraMap F D))
    (a : D) (ha : a ∉ quotientSet W) :
    Function.Bijective (obstruction W a) ∧
    ∃ e : K ⊗[F] D ≃ₐ[K] ((D →ₐ[F] K) → K),
      (∀ (c : K) (d : D) (σ : D →ₐ[F] K), e (c ⊗ₜ[F] d) σ = c * σ d) ∧
      let U := (W.baseChange K).map e.toLinearMap
      let n := e.toLinearMap ∘ₗ (actualOperator W hD hW a ha).baseChange K ∘ₗ e.symm.toLinearMap
      let N := LinearMap.toMatrix' n
      n.comp n = 0 ∧ n.range = U ∧ n.ker = U ∧ N * N = 0 ∧ N.rank = 4 ∧
      (∀ (g : K ≃ₐ[F] K) (σ τ : D →ₐ[F] K),
        N (g.toAlgHom.comp σ) (g.toAlgHom.comp τ) = g (N σ τ)) ∧
      (∀ S : Finset (D →ₐ[F] K), S.Nonempty → Sᶜ.Nonempty →
        S.card + 1 ≤ 2 * finrank K (U.map (coordinateProject S))) ∧
      (∀ S : Finset (D →ₐ[F] K), 2 ≤ S.card → S.card ≤ 6 →
        2 ≤ (N.submatrix (fun i : S => (i : D →ₐ[F] K))
          (fun j : ↥(Sᶜ) => (j : D →ₐ[F] K))).rank ∨
        2 ≤ (N.submatrix (fun i : ↥(Sᶜ) => (i : D →ₐ[F] K))
          (fun j : S => (j : D →ₐ[F] K))).rank) := by
  have hsplit : ∀ d : D, ((minpoly F d).map (algebraMap F K)).Splits := by
    intro d
    have hh := Normal.splits (inferInstance : Normal F K) (algebraMap D K d)
    rwa [minpoly.algebraMap_eq (algebraMap D K).injective] at hh
  have hscalar : ScalarIdealizer W := by
    intro c hc
    rw [← hE]
    exact hc
  refine ⟨(obstructionEquiv W hD hW a ha).bijective, splitEquiv F D K hsplit,
    (fun _ _ _ => rfl), ?_⟩
  change (splitOperator K hsplit W hD hW a ha).comp (splitOperator K hsplit W hD hW a ha) = 0 ∧
    (splitOperator K hsplit W hD hW a ha).range = splitWindow K hsplit W ∧
    (splitOperator K hsplit W hD hW a ha).ker = splitWindow K hsplit W ∧ _
  refine ⟨splitOperator_square_zero K hsplit W hD hW a ha,
    splitOperator_range K hsplit W hD hW a ha,
    splitOperator_kernel K hsplit W hD hW a ha,
    splitMatrix_square_zero K hsplit W hD hW a ha,
    splitMatrix_rank K hsplit W hD hW a ha,
    splitMatrix_covariance K hsplit W hD hW a ha,
    actual_strict_row_rank K hsplit W hD hW hscalar, ?_⟩
  intro S h2 h6
  have hh := actual_cut_free K hsplit W hD hW hscalar a ha S h2 h6
  rw [← crossRank_matrix, ← crossRank_matrix] at hh
  rcases hh with hl | hr
  · exact Or.inl hl
  · apply Or.inr
    have he := congrArg (fun T : Finset (D →ₐ[F] K) =>
      ((LinearMap.toMatrix' (splitOperator K hsplit W hD hW a ha)).submatrix
        (fun i : ↥(Sᶜ) => (i : D →ₐ[F] K))
        (fun j : T => (j : D →ₐ[F] K))).rank) (compl_compl S)
    exact he ▸ hr

end ActualCutFree

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
