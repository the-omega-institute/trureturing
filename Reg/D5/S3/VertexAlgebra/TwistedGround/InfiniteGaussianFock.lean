import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock

/-! Faithful source-bound mirrors for the infinite Gaussian Fock declarations. -/
set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock

open scoped BigOperators InnerProductSpace lp ENNReal Matrix.Norms.L2Operator
open _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric
open _root_.D5.S3.VertexAlgebra.TwistedGround

universe u v

theorem source_actual_coordinateBasis_apply {J : Type u} [DecidableEq J] (j : J) :
    coordinateBasis J j = lp.single 2 j (1 : ℂ) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coordinateBasis_apply j

theorem source_actual_coordinateInclusion_single {A : Type u} {B : Type v}
    [DecidableEq A] [DecidableEq B] (e : A → B) (he : Function.Injective e)
    (a : A) (c : ℂ) :
    coordinateInclusion e he (lp.single 2 a c) = lp.single 2 (e a) c :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coordinateInclusion_single
    e he a c

theorem source_actual_coordinateInclusion_adjoint_apply {A : Type u} {B : Type v}
    [DecidableEq A] [DecidableEq B] (e : A → B) (he : Function.Injective e)
    (x : ℓ²(B, ℂ)) (a : A) :
    ContinuousLinearMap.adjoint (coordinateInclusion e he).toContinuousLinearMap x a =
      x (e a) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coordinateInclusion_adjoint_apply
    e he x a

theorem source_actual_Data_finiteInclusion_single {I : Type u} [DecidableEq I]
    (S : Finset I) (j : S) :
    Data.finiteInclusion S (EuclideanSpace.single j (1 : ℂ)) =
      lp.single 2 j.val (1 : ℂ) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.finiteInclusion_single
    S j

theorem source_actual_Data_finiteInclusion_adjoint_apply {I : Type u} [DecidableEq I]
    (S : Finset I) (x : ℓ²(I, ℂ)) (i : S) :
    ContinuousLinearMap.adjoint (Data.finiteInclusion S).toContinuousLinearMap x i = x i.val :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.finiteInclusion_adjoint_apply
    S x i

theorem source_actual_Data_compression_eq_matrix {I : Type u} [DecidableEq I]
    (D : Data I) (S : Finset I) :
    D.compression S = Matrix.toEuclideanCLM (𝕜 := ℂ) (D.block S) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.compression_eq_matrix D S

theorem source_actual_Data_block_opNorm_le {I : Type u} [DecidableEq I]
    (D : Data I) (S : Finset I) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (D.block S)‖ ≤ D.q :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.block_opNorm_le D S

theorem source_actual_Data_block_mass_le {I : Type u} [DecidableEq I]
    (D : Data I) (S : Finset I) :
    (∑ i : S, ∑ j : S, ‖D.block S i j‖ ^ 2) ≤ D.massBound :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.block_mass_le D S

theorem source_actual_quadratic_projection {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (K : Matrix B B ℂ) (e : A → B) (he : Function.Injective e) :
    MvPolynomial.killCompl he (FactorialFockQuadraticEstimate.quadratic K) =
      FactorialFockQuadraticEstimate.quadratic (fun i j => K (e i) (e j)) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.quadratic_projection K e he

theorem source_actual_gaussianPiece_projection {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (K : Matrix B B ℂ) (e : A → B) (he : Function.Injective e) (n : ℕ) :
    MvPolynomial.killCompl he (FactorialFockQuadraticEstimate.gaussianPiece K n) =
      FactorialFockQuadraticEstimate.gaussianPiece (fun i j => K (e i) (e j)) n :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.gaussianPiece_projection K e he n

theorem source_actual_gaussianCoefficient_enlarge {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (K : Matrix B B ℂ) (e : A → B) (he : Function.Injective e) (d : A →₀ ℕ) :
    FactorialFockQuadraticEstimate.gaussianCoefficient K (d.mapDomain e) =
      FactorialFockQuadraticEstimate.gaussianCoefficient (fun i j => K (e i) (e j)) d :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.gaussianCoefficient_enlarge
    K e he d

theorem source_actual_restrictOccupation_apply {I : Type u} [DecidableEq I]
    (S : Finset I) (d : Occupation I) (i : S) :
    restrictOccupation S d i = d i.val :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.restrictOccupation_apply S d i

theorem source_actual_extend_restrict {I : Type u} [DecidableEq I]
    (S : Finset I) (d : Occupation I) (hd : d.support ⊆ S) :
    (restrictOccupation S d).mapDomain (fun i : S => i.val) = d :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.extend_restrict S d hd

theorem source_actual_weight_restrict {I : Type u} [DecidableEq I]
    (S : Finset I) (d : Occupation I) (hd : d.support ⊆ S) :
    weight (restrictOccupation S d) = weight d :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.weight_restrict S d hd

theorem source_actual_coefficient_on_block {I : Type u} [DecidableEq I]
    (K : I → I → ℂ) (S : Finset I) (d : Occupation I) (hd : d.support ⊆ S) :
    coefficient K d = FactorialFockQuadraticEstimate.gaussianCoefficient
      (fun i j : S => K i.val j.val) (restrictOccupation S d) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coefficient_on_block K S d hd

theorem source_actual_coefficient_stabilization {I : Type u} [DecidableEq I]
    (K : I → I → ℂ) (S T : Finset I) (d : Occupation I)
    (hS : d.support ⊆ S) (hT : d.support ⊆ T) :
    FactorialFockQuadraticEstimate.gaussianCoefficient (fun i j : S => K i.val j.val)
        (restrictOccupation S d) =
      FactorialFockQuadraticEstimate.gaussianCoefficient (fun i j : T => K i.val j.val)
        (restrictOccupation T d) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coefficient_stabilization
    K S T d hS hT

theorem source_actual_coefficient_zero {I : Type u} [DecidableEq I]
    (K : I → I → ℂ) : coefficient K 0 = 1 :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coefficient_zero K

theorem source_actual_coefficient_odd {I : Type u} [DecidableEq I]
    (K : I → I → ℂ) (d : Occupation I) (hd : d.degree % 2 = 1) :
    coefficient K d = 0 :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.coefficient_odd K d hd

theorem source_actual_support_subset_commonBlock {I : Type u} [DecidableEq I]
    (F : Finset (Occupation I)) (d : Occupation I) (hd : d ∈ F) :
    d.support ⊆ commonBlock F :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.support_subset_commonBlock F d hd

theorem source_actual_commonRestriction_injective {I : Type u} [DecidableEq I]
    (F : Finset (Occupation I)) :
    Set.InjOn (restrictOccupation (commonBlock F)) F :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.commonRestriction_injective F

theorem source_actual_Data_finite_occupation_bound {I : Type u} [DecidableEq I]
    (D : Data I) (F : Finset (Occupation I)) :
    (∑ d ∈ F, (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) ≤ D.bound :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.finite_occupation_bound D F

theorem source_actual_Data_occupation_summable {I : Type u} [DecidableEq I]
    (D : Data I) :
    Summable (fun d : Occupation I => (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.occupation_summable D

theorem source_actual_Data_occupation_tsum_le {I : Type u} [DecidableEq I]
    (D : Data I) :
    (∑' d : Occupation I, (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) ≤ D.bound :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.occupation_tsum_le D

theorem source_actual_norm_scale_sq {I : Type u} (d : Occupation I) :
    ‖scale d‖ ^ 2 = (weight d : ℝ) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.norm_scale_sq d

theorem source_actual_Data_vector_apply {I : Type u} [DecidableEq I] [Countable I]
    (D : Data I) (d : Occupation I) :
    D.vector d = scale d * coefficient D.kernel d :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_apply D d

theorem source_actual_Data_vector_norm_sq {I : Type u} [DecidableEq I] [Countable I]
    (D : Data I) :
    ‖D.vector‖ ^ 2 = ∑' d : Occupation I,
      (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2 :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_norm_sq D

theorem source_actual_Data_vector_norm_sq_le {I : Type u} [DecidableEq I] [Countable I]
    (D : Data I) : ‖D.vector‖ ^ 2 ≤ D.bound :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_norm_sq_le D

theorem source_actual_Data_vector_vacuum {I : Type u} [DecidableEq I] [Countable I]
    (D : Data I) : D.vector 0 = 1 :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_vacuum D

theorem source_actual_Data_vector_odd {I : Type u} [DecidableEq I] [Countable I]
    (D : Data I) (d : Occupation I) (hd : d.degree % 2 = 1) :
    D.vector d = 0 :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_odd D d hd

theorem source_actual_Data_vector_empty {I : Type u} [DecidableEq I] [Countable I] [IsEmpty I]
    (D : Data I) : D.vector = lp.single 2 (0 : Occupation I) (1 : ℂ) :=
  _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_empty D

theorem source_actual_Data_vector_hasSum {I : Type u} [DecidableEq I] [Countable I]
    (D : Data I) :
    HasSum (fun d : Occupation I =>
      (scale d * coefficient D.kernel d) •
        (_root_.D5.S3.VertexAlgebra.FactorialFockMetric.hilbertBasis I d)) D.vector := by
  exact _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock.Data.vector_hasSum D

end Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
