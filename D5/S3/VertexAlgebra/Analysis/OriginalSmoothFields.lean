/- GID: D5/S3/VertexAlgebra/Analysis/OriginalSmoothFields
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalSmoothFields
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal original smooth charged fields on their common dense invariant domain. -/

import D5.S3.VertexAlgebra.Analysis.OriginalSmearingCore

/-!
The mathematical conclusion is infinite smooth smearing, a finite-carrier graph
core and opposite-charge formal adjoint inclusions. It is not mutual adjoint-
closure equality, essential self-adjointness or strong locality. No actual-lattice
counterexample to those stronger claims is asserted. All-state propagation,
BRST/no-ghost, string theory and AdS/CFT are subsequent obligations.

proof_shape: original_smooth_fields: content
admission_basis: escape-witness
escape_witness: The Hm completion, actual orthogonal shifted-image Sobolev bound,
smooth Fourier summability, compatible operator-norm sums and dense pairing/core
limits are all consumed by this original charged-field endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality SmoothCircleFourier
open private operator_absolute smear_vector_bound smear_paper_bound from
  D5.S3.VertexAlgebra.Analysis.OriginalInfiniteSmearing
open private smoothDomain_dense field_formal field_le_opposite_adjoint field_closable eta_cocycle from
  D5.S3.VertexAlgebra.Analysis.OriginalSmoothDomain
open private inclusion_self inclusion_comp from
  D5.S3.VertexAlgebra.Analysis.OriginalSobolev
open private field_closure_eq finite_carrier_core field_charge_transport from
  D5.S3.VertexAlgebra.Analysis.OriginalSmearingCore

/-- Original generating charged fields, including charge zero, smeared over all integers. -/
theorem original_smooth_fields (M : Model) (a : Charge M.D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Test,
      (∀ k : ℕ, Summable (fun m : ℤ => ‖M.operatorTerm a f k m‖)) ∧
      (∀ (k : ℕ) (x : M.Sobolev (M.order a+k)),
        ‖M.smear a f k x‖ ≤ C * f.W (M.order a+k) * ‖x‖) ∧
      Dense (M.smoothDomain : Set M.Hilbert) ∧
      (∀ u : M.smoothDomain, M.field a f u ∈ M.smoothDomain) ∧
      (M.field a f).IsFormalAdjoint (M.opposite a f) ∧
      M.field a f ≤ (M.opposite a f).adjoint ∧
      (M.field a f).IsClosable ∧ (M.opposite a f).IsClosable ∧
      (M.field a f).closure.IsClosed ∧
      (M.field a f).closure = (M.finiteField a f).closure ∧
      (M.field a f).closure.HasCore M.finiteDomain ∧
      (∀ (δ : Charge M.D) (u : M.smoothDomain),
        (u : M.Hilbert) ∈ M.chargeSector 0 δ →
          M.field a f u ∈ M.chargeSector 0 (a+δ)) ∧
      (∀ k : ℕ, ‖M.smear a f k‖ ≤ C *
        (f.jetNorm 0 + (2^(M.order a+k) * f.jetNorm (M.order a+k+2)) *
          (∑' m : ℤ, 1 / (m : ℝ)^2))) ∧
      M.eta a = epsilon M.D a (-a) ∧
      (∀ k : ℕ, M.inclusion k k le_rfl = ContinuousLinearMap.id ℂ (M.Sobolev k)) ∧
      (∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k),
        (M.inclusion i j hij).comp (M.inclusion j k hjk) =
          M.inclusion i k (hij.trans hjk)) := by
  refine ⟨M.modeConstant a, modeConstant_pos M a, ?_⟩
  intro f
  have hformal := field_formal M a f
  have hdense := smoothDomain_dense M
  have hclosable := field_closable M a f
  refine ⟨operator_absolute M a f, smear_vector_bound M a f, hdense, ?_, hformal,
    field_le_opposite_adjoint M a f, hclosable, ?_, hclosable.closure_isClosed,
    field_closure_eq M a f, finite_carrier_core M a f, ?_,
    smear_paper_bound M a f, eta_cocycle M a, inclusion_self M, inclusion_comp M⟩
  · intro u
    exact ⟨M.smearFamily a f (M.domainEquiv.symm u), rfl⟩
  · exact (LinearPMap.adjoint_isClosed (T := M.field a f) hdense).isClosable.leIsClosable
      (hformal.le_adjoint hdense)
  · exact fun δ u hu => field_charge_transport M a δ f u hu

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
