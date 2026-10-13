import D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
import Reg.Support.BridgeGraphEqualityFamilies
import Reg.Support.BridgeGraphRelations

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
open Reg.Support.BridgeGraphEqualityFamilies Reg.Support.BridgeGraphRelations
open Matrix
open scoped BigOperators

noncomputable section
universe u_1 u_2 u_3 u_4
namespace Reg.Support.BridgeGraphOriginalLaws

/-- Injectivity is observed on the entire function at arbitrary carrier universes. -/
abbrev vectorFunctionSignature : Signature where
  Params := Σ _ : Type u_1, Type u_2
  State p := (p.2 → ℚ) → (p.1 → ℚ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def vectorFunctionActual : Realization vectorFunctionSignature.{u_1,u_2} :=
  realize vectorFunctionSignature
    (fun _ _ f => @Decidable.decide (Function.Injective f)
      (Classical.propDecidable (Function.Injective f))) (fun e => nomatch e)
def vectorFunctionRejected : Realization vectorFunctionSignature.{u_1,u_2} :=
  realize vectorFunctionSignature (fun _ _ _ => false) (fun e => nomatch e)

theorem vectorFunctionDependence :
    ObservationalDependence vectorFunctionSignature.{u_1,u_2} vectorFunctionActual := by
  classical
  intro i
  let p : vectorFunctionSignature.{u_1,u_2}.Params :=
    ⟨ULift.{u_1} Unit, ULift.{u_2} Unit⟩
  let x : vectorFunctionSignature.State p := fun z _ => z ⟨()⟩
  let y : vectorFunctionSignature.State p := fun _ _ => 0
  have hx : Function.Injective x := by
    intro a b h
    funext j
    have hj : j = (⟨()⟩ : ULift.{u_2} Unit) := Subsingleton.elim _ _
    rw [hj]
    exact congrFun h (⟨()⟩ : ULift.{u_1} Unit)
  refine ⟨p, x, y, ?_⟩
  intro h
  change decide (Function.Injective x) = decide (Function.Injective y) at h
  have hx' : decide (Function.Injective x) = true := by
    simpa only [decide_eq_true_eq] using hx
  have hy : Function.Injective y := of_decide_eq_true (h ▸ hx')
  have h01 := @hy (0 : ULift.{u_2} Unit → ℚ) (fun _ => 1) rfl
  have hq := congrFun h01 (⟨()⟩ : ULift.{u_2} Unit)
  change (0 : ℚ) = 1 at hq
  norm_num at hq

abbrev kernelFunctionSignature : Signature where
  Params := FiveParams
  State p := Fin p.2.1 × Fin p.2.2.2.2 → ℚ
  Output _ p := SourceIndex p.1 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def kernelFunctionActual : Realization kernelFunctionSignature :=
  realize kernelFunctionSignature
    (fun _ p x => kernelEmbedding p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e)
def kernelFunctionRejected : Realization kernelFunctionSignature :=
  realize kernelFunctionSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem kernelFunctionDependence :
    ObservationalDependence kernelFunctionSignature kernelFunctionActual := by
  intro i
  let p : kernelFunctionSignature.Params := ⟨1, ⟨1, ⟨1, ⟨1, 1⟩⟩⟩⟩
  let x : kernelFunctionSignature.State p := fun _ => 0
  let y : kernelFunctionSignature.State p := fun _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  dsimp [p] at h
  dsimp [kernelFunctionActual, realize] at h
  have hq := congrFun h
    (⟨Sum.inl (0 : Fin 1), ⟨0, by simp [blockLength]⟩⟩,
      ⟨Sum.inr (0 : Fin 1), ⟨1, by simp [blockLength]⟩⟩)
  simp [kernelEmbedding, antiDiagonal, x, y] at hq

abbrev typedVectorEqualitySignature : Signature where
  Params := Type u_1
  State m := m → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := (m → ℚ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def typedVectorEqualityActual : Realization typedVectorEqualitySignature.{u_1} :=
  realize typedVectorEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)
def typedVectorEqualityRejected : Realization typedVectorEqualitySignature.{u_1} :=
  realize typedVectorEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem typedVectorEqualityDependence :
    ObservationalDependence typedVectorEqualitySignature.{u_1} typedVectorEqualityActual := by
  intro i
  let m := ULift.{u_1} Unit
  let x : m → ℚ := 0
  let y : m → ℚ := fun _ => 1
  refine ⟨m, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hq := congrFun hy (⟨()⟩ : m)
  change (1 : ℚ) = 0 at hq
  norm_num at hq

end Reg.Support.BridgeGraphOriginalLaws

open Reg.Support.BridgeGraphOriginalLaws

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent

@[reducible] def inclusion_injectiveArena : Arena where
  signature := vectorFunctionSignature.{u_1,u_2}
  Law S := ∀ {m : Type u_1} {n : Type u_2} [Fintype n] [DecidableEq m]
    (e : n → m) (he : Function.Injective e),
    S.readout () ⟨m, n⟩ (inclusion e).mulVec = true
theorem inclusion_injectivePositive :
    inclusion_injectiveArena.{u_1,u_2}.Law vectorFunctionActual := by
  classical
  intro m n _ _ e he
  change decide (Function.Injective (inclusion e).mulVec) = true
  simpa only [decide_eq_true_eq] using
    _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective e he
theorem inclusion_injectiveNegative :
    ¬ inclusion_injectiveArena.{u_1,u_2}.Law vectorFunctionRejected := by
  intro h
  exact Bool.noConfusion (h (m := ULift.{u_1} Unit) (n := ULift.{u_2} Unit)
    (fun _ => ⟨()⟩) (fun _ _ _ => Subsingleton.elim _ _))

def inclusion_injectiveEvidence : Registration inclusion_injectiveArena.{u_1,u_2}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent.inclusion_injective.{u_1,u_2})) where
  actual := vectorFunctionActual
  bridge := by
    classical
    constructor
    · intro h m n _ _ e he
      change decide (Function.Injective (inclusion e).mulVec) = true
      simpa only [decide_eq_true_eq] using h e he
    · intro h m n _ _ e he
      exact of_decide_eq_true (h e he)
  variation := ⟨inclusion_injectivePositive, vectorFunctionRejected, inclusion_injectiveNegative⟩
  sensitivity := ⟨fun i => ⟨vectorFunctionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, inclusion_injectiveNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorFunctionDependence

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur

@[reducible] def kernelEmbedding_injectiveArena : Arena where
  signature := kernelFunctionSignature
  Law S := ∀ (p alpha beta gamma delta : ℕ),
    Function.Injective (S.readout () ⟨p, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩)
theorem kernelEmbedding_injectivePositive :
    kernelEmbedding_injectiveArena.Law kernelFunctionActual := by
  intro p alpha beta gamma delta
  exact _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injective
    p alpha beta gamma delta
theorem kernelEmbedding_injectiveNegative :
    ¬ kernelEmbedding_injectiveArena.Law kernelFunctionRejected := by
  intro h
  have hinj := h 1 1 1 1 1
  have hzeroone := @hinj (fun _ => (0 : ℚ)) (fun _ => 1) (by rfl)
  have hq := congrFun hzeroone (0, 0)
  change (0 : ℚ) = 1 at hq
  norm_num at hq

def kernelEmbedding_injectiveEvidence : Registration kernelEmbedding_injectiveArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernelEmbedding_injective)) where
  actual := kernelFunctionActual
  bridge := Iff.rfl
  variation := ⟨kernelEmbedding_injectivePositive, kernelFunctionRejected, kernelEmbedding_injectiveNegative⟩
  sensitivity := ⟨fun i => ⟨kernelFunctionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, kernelEmbedding_injectiveNegative⟩,
    fun i => nomatch i⟩
  dependence := kernelFunctionDependence

@[reducible] def kernel_coordinatesArena : Arena where
  signature := sourceVectorEqualitySignature
  Law S := ∀ (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) ×
      (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : (widthTwoMatrix p p alpha beta gamma delta).mulVec u = 0),
    ∃ w, S.readout () ⟨p, ⟨alpha, ⟨beta, ⟨gamma, delta⟩⟩⟩⟩
      (kernelEmbedding p alpha beta gamma delta w) u
theorem kernel_coordinatesPositive : kernel_coordinatesArena.Law sourceVectorEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinates
theorem kernel_coordinatesNegative : ¬ kernel_coordinatesArena.Law sourceVectorEqualityRejected := by
  intro h
  obtain ⟨w, hw⟩ := h 0 0 0 0 0 0 (Matrix.mulVec_zero _)
  exact hw

def kernel_coordinatesEvidence : Registration kernel_coordinatesArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur.kernel_coordinates)) where
  actual := sourceVectorEqualityActual
  bridge := Iff.rfl
  variation := ⟨kernel_coordinatesPositive, sourceVectorEqualityRejected, kernel_coordinatesNegative⟩
  sensitivity := ⟨fun i => ⟨sourceVectorEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, kernel_coordinatesNegative⟩,
    fun i => nomatch i⟩
  dependence := sourceVectorEqualityDependence

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks

@[reducible] def witness_of_typed_slicesArena : Arena where
  signature := witnessPredicateSignature
  Law S := ∀ {I : Type u_1} {J : Type u_2} {K : Type u_3} {L : Type u_4}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    {a b c d : ℕ} (hi : Fintype.card I = a) (hj : Fintype.card J = b)
    (hk : Fintype.card K = c) (hl : Fintype.card L = d)
    (M : Fin 3 → Matrix I J ℚ) (N : Fin 3 → Matrix L K ℚ)
    (hr : (∑ r : Fin 3, kronecker (M r) (N r)).rank = min (a * d) (b * c)),
    S.readout () () a b c d
theorem witness_of_typed_slicesPositive :
    witness_of_typed_slicesArena.{u_1,u_2,u_3,u_4}.Law witnessPredicateActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slices.{u_1,u_2,u_3,u_4}
theorem witness_of_typed_slicesNegative :
    ¬ witness_of_typed_slicesArena.{u_1,u_2,u_3,u_4}.Law witnessPredicateRejected := by
  intro h
  exact h (I := ULift.{u_1} Empty) (J := ULift.{u_2} Empty)
    (K := ULift.{u_3} Empty) (L := ULift.{u_4} Empty)
    (a := 0) (b := 0) (c := 0) (d := 0)
    (by simp) (by simp) (by simp) (by simp) 0 0 (by simp)

def witness_of_typed_slicesEvidence : Registration witness_of_typed_slicesArena.{u_1,u_2,u_3,u_4}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.witness_of_typed_slices.{u_1,u_2,u_3,u_4})) where
  actual := witnessPredicateActual
  bridge := Iff.rfl
  variation := ⟨witness_of_typed_slicesPositive, witnessPredicateRejected, witness_of_typed_slicesNegative⟩
  sensitivity := ⟨fun i => ⟨witnessPredicateRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, witness_of_typed_slicesNegative⟩,
    fun i => nomatch i⟩
  dependence := witnessPredicateDependence

@[reducible] def matrix_injective_of_rankArena : Arena where
  signature := vectorFunctionSignature.{u_1,u_2}
  Law S := ∀ {m : Type u_1} {n : Type u_2} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℚ) (hA : A.rank = Fintype.card n),
    S.readout () ⟨m, n⟩ A.mulVecLin = true
theorem matrix_injective_of_rankPositive :
    matrix_injective_of_rankArena.{u_1,u_2}.Law vectorFunctionActual := by
  classical
  intro m n _ _ _ A hA
  change decide (Function.Injective A.mulVecLin) = true
  simpa only [decide_eq_true_eq] using
    _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rank A hA
theorem matrix_injective_of_rankNegative :
    ¬ matrix_injective_of_rankArena.{u_1,u_2}.Law vectorFunctionRejected := by
  intro h
  exact Bool.noConfusion (h (m := ULift.{u_1} Empty) (n := ULift.{u_2} Empty) 0 (by simp))

def matrix_injective_of_rankEvidence : Registration matrix_injective_of_rankArena.{u_1,u_2}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.matrix_injective_of_rank.{u_1,u_2})) where
  actual := vectorFunctionActual
  bridge := by
    classical
    constructor
    · intro h m n _ _ _ A hA
      change decide (Function.Injective A.mulVecLin) = true
      simpa only [decide_eq_true_eq] using h A hA
    · intro h m n _ _ _ A hA
      exact of_decide_eq_true (h A hA)
  variation := ⟨matrix_injective_of_rankPositive, vectorFunctionRejected, matrix_injective_of_rankNegative⟩
  sensitivity := ⟨fun i => ⟨vectorFunctionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, matrix_injective_of_rankNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorFunctionDependence

@[reducible] def schur_two_equationsArena : Arena where
  signature := typedVectorEqualitySignature.{u_1}
  Law S := ∀ {m : Type u_1} {n : Type u_2} {k : Type u_3}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (R : Matrix m m ℚ) (T : Matrix m n ℚ) (L : Matrix k m ℚ) (H : Matrix k n ℚ)
    (hR : IsUnit R) (hS : Function.Injective (H-L*R⁻¹*T).mulVec)
    (v : m → ℚ) (w : n → ℚ)
    (hr : R.mulVec v + T.mulVec w = 0) (he : L.mulVec v + H.mulVec w = 0),
    S.readout () m v 0 ∧ w = 0
theorem schur_two_equationsPositive :
    schur_two_equationsArena.{u_1,u_2,u_3}.Law typedVectorEqualityActual :=
  @_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equations.{u_1,u_2,u_3}
theorem schur_two_equationsNegative :
    ¬ schur_two_equationsArena.{u_1,u_2,u_3}.Law typedVectorEqualityRejected := by
  intro h
  exact (h (m := ULift.{u_1} Empty) (n := ULift.{u_2} Empty) (k := ULift.{u_3} Empty)
    1 0 0 0 isUnit_one (fun _ _ _ => Subsingleton.elim _ _) 0 0
    (by simp) (by simp)).1

def schur_two_equationsEvidence : Registration schur_two_equationsArena.{u_1,u_2,u_3}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.schur_two_equations.{u_1,u_2,u_3})) where
  actual := typedVectorEqualityActual
  bridge := Iff.rfl
  variation := ⟨schur_two_equationsPositive, typedVectorEqualityRejected, schur_two_equationsNegative⟩
  sensitivity := ⟨fun i => ⟨typedVectorEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, schur_two_equationsNegative⟩,
    fun i => nomatch i⟩
  dependence := typedVectorEqualityDependence

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
