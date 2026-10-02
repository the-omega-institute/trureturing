import D5.S3.Observer.Linear.ObservableTrajectoryCoordinates
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit ContinuousLinearMap MeasureTheory Set Filter Module WithLp
open scoped InnerProductSpace Matrix.Norms.L2Operator Topology
noncomputable section
namespace Reg.D5.S3.Observer.Linear.ObservableTrajectoryCoordinates
abbrev Parameters := Σ (d : ℕ), Σ (p : ℕ),
  Σ (_ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
  Σ (_ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin p)), ℝ
abbrev signature : Signature where
  Params := Parameters
  State := fun p => EuclideanSpace ℝ (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => EuclideanSpace ℝ (Fin p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance
def emptyAnchor : ∀ (_ : Empty) p, signature.State p := fun e => nomatch e
def actual : Realization signature := realize signature
  (fun _ p x => p.2.2.2.1 ((NormedSpace.exp (p.2.2.2.2 • p.2.2.1)) x)) emptyAnchor
def modified : Realization signature := realize signature (fun _ _ _ => 0) emptyAnchor
def theoremLaw (family : Realization signature) : Prop := ∀ (d p : ℕ)
    (B : (EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (C : (EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (T : ℝ) (hT : 0 < T)
    (hobs : ∀ x, (∀ k : Fin d, C ((B ^ (k : ℕ)) x) = 0) → x = 0) ,
    ∃ F : (EuclideanSpace ℝ (Fin d)) →L[ℝ] Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T)),
      (∀ x, (fun t => F x t) =ᵐ[volume.restrict (Ioc 0 T)]
        fun t => family.readout () ⟨d,p,B,C,t⟩ x) ∧
      Function.Injective F ∧ finrank ℝ F.range = d ∧
      ∃ basis : OrthonormalBasis (Fin d) ℝ F.range,
      ∃ U : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T)) →L[ℝ] EuclideanSpace ℝ (Fin d),
      ∃ M : Matrix (Fin d) (Fin d) ℝ,
        U = basis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
          F.range.orthogonalProjectionOnto ∧
        (∀ g, ‖U g‖ ≤ ‖g‖) ∧
        (∀ g i, U g i = ∫ t in (0:ℝ)..T,
          inner ℝ ((basis i : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T))) t) (g t)) ∧
        (∀ (g : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T))) i, IntervalIntegrable (fun t =>
          inner ℝ ((basis i : Lp (EuclideanSpace ℝ (Fin p)) 2 (volume.restrict (Ioc 0 T))) t) (g t)) volume 0 T) ∧
        U.adjoint.comp U = F.range.starProjection ∧
        M.toEuclideanLin.toContinuousLinearMap = U.comp F ∧
        (U.comp F).adjoint.comp (U.comp F) = F.adjoint.comp F ∧
        F.adjoint.comp F = ∫ t in (0:ℝ)..T,
          (C.comp (NormedSpace.exp (t • B))).adjoint.comp (C.comp (NormedSpace.exp (t • B))) ∧
        (let b := Matrix.toEuclideanLin.symm B.toLinearMap
         let c := Matrix.toEuclideanLin.symm C.toLinearMap
         M.transpose*M = ∫ t in (0:ℝ)..T,
           NormedSpace.exp (t • b.transpose)*c.transpose*c*NormedSpace.exp (t • b))

def arena : Arena where
  signature := signature
  Law := theoremLaw

theorem actual_law : arena.Law actual := by
  intro d p B C T hT hobs
  exact _root_.D5.S3.Observer.Linear.ObservableTrajectoryCoordinates.observable_trajectory_coordinates d p B C T hT hobs

theorem modified_law : ¬ arena.Law modified := by
  intro h
  let E := EuclideanSpace ℝ (Fin 1)
  have hobs : ∀ x : E, (∀ k : Fin 1, (ContinuousLinearMap.id ℝ E) (((0 : E →L[ℝ] E) ^ (k : ℕ)) x) = 0) → x = 0 := by
    intro x hx
    simpa using hx 0
  obtain ⟨F,hrep,hinj,rest⟩ := h 1 1 0 (ContinuousLinearMap.id ℝ E) 1 zero_lt_one hobs
  have hzero (x : E) : F x = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    change ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), F x t = 0
    exact hrep x
  have hx : (toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : E) = 0 :=
    hinj ((hzero _).trans (hzero 0).symm)
  have hc := congrArg (fun x : E => x (0 : Fin 1)) hx
  norm_num at hc

theorem dependence_proof : ObservationalDependence signature actual := by
  intro role
  let E := EuclideanSpace ℝ (Fin 1)
  refine ⟨⟨1,1,0,ContinuousLinearMap.id ℝ E,0⟩,
    (0:E),toLp 2 (fun _ : Fin 1 => (1:ℝ)),?_⟩
  intro h
  have hc := congrArg (fun x : E => x (0 : Fin 1)) h
  norm_num [actual,realize] at hc
  change (0:ℝ) = 1 at hc
  norm_num at hc

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,modified,modified_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨modified,?_,rfl,modified_law⟩
      intro other hne
      exact (hne (by cases role;cases other;rfl)).elim
    · intro e;exact nomatch e
  dependence := dependence_proof
end Reg.D5.S3.Observer.Linear.ObservableTrajectoryCoordinates
