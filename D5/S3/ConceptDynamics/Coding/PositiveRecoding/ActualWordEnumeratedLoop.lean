/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual positive-word loop transport to literal vertex coordinates with both endpoint corrections. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.BasedLoopCoordinateTransport
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualWordRelabelAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualWordEnumeratedLoop
open D5.S3.ConceptDynamics.Coding
open EssentialWordRealization TwoSidedFiniteInduction TypedPositiveSplitWord
open CountedOrderTypeGyration
open SourceOnly.ActualWordMatrixPath (D reindex vertex dictionary endpointMap presentationBasis)
open SourceOnly.KernelRSSquareGyration (rows value)
open SourceOnly.FiniteKernelLadder (Mat rowUnit)
open SourceOnly.BasedLoopCoordinateTransport

section Coefficients
variable {I V : Type} [Fintype I] [DecidableEq I]

/-- A coefficient basis on the actual graph vertex functions. -/
def coefficientBasis (e : I ≃ V) : Module.Basis I D (V → D) :=
  (Pi.basisFun D I).map (reindex e)

theorem coefficient_apply [DecidableEq V] (e : I ≃ V) (i : I) (v : V) :
    coefficientBasis e i v = if e i = v then 1 else 0 := by
  classical
  change (Pi.basisFun D I i) (e.symm v) = _
  rw [Pi.basisFun_apply]
  by_cases h : e i = v
  · subst v
    simp
  · have hn : e.symm v ≠ i := by
      intro he
      apply h
      exact (congrArg e he).symm.trans (e.apply_symm_apply v)
    simp [Pi.single_apply, h, hn, Ne.symm hn]

theorem coefficient_repr (e : I ≃ V) (z : V → D) (i : I) :
    (coefficientBasis e).repr z i = z (e i) := by
  change (Pi.basisFun D I).repr ((reindex e).symm z) i = _
  rw [Pi.basisFun_repr]
  rfl

theorem rows_coefficients {W : Type}
    {n m : ℕ} (e : Fin n ≃ V) (q : Fin m ≃ W)
    (f : (V → D) →ₗ[D] (W → D)) (i : Fin n) (j : Fin m) :
    rows (coefficientBasis e) (coefficientBasis q) f i j =
      f (coefficientBasis e i) (q j) := by
  simp only [rows, Matrix.transpose_apply, LinearMap.toMatrix_apply]
  exact coefficient_repr q _ j

end Coefficients

/-- A COLUMN unit of the ACTUAL endomorphism, in any actual finite basis.
Its multiplication uses toMatrix, so the chronological order is preserved. -/
def columnUnit {V I : Type} [AddCommGroup V] [Module D V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I D V)
    (a : (Module.End D V)ˣ) : (Matrix I I D)ˣ where
  val := LinearMap.toMatrix b b (a : Module.End D V)
  inv := LinearMap.toMatrix b b (↑a⁻¹ : Module.End D V)
  val_inv := by
    rw [← LinearMap.toMatrix_comp b b b]
    change LinearMap.toMatrix b b
      ((a : Module.End D V) * (↑a⁻¹ : Module.End D V)) = 1
    rw [Units.mul_inv]
    exact LinearMap.toMatrix_id b
  inv_val := by
    rw [← LinearMap.toMatrix_comp b b b]
    change LinearMap.toMatrix b b
      ((↑a⁻¹ : Module.End D V) * (a : Module.End D V)) = 1
    rw [Units.inv_mul]
    exact LinearMap.toMatrix_id b

/-- Literal entries of the actual OLD-to-NEW coefficient permutation.
This is not a guessed equality of chart adjacency with a signed matrix. -/
theorem chart_change_entries (F : Presentation) {m : ℕ}
    (e : Fin m ≃ F.V) (i : Fin (Fintype.card F.V)) (j : Fin m) :
    changeRows (presentationBasis F) (coefficientBasis e) i j =
      if (ActualPositiveWordPeriodicCochain.chart F).vertex i = e j then 1 else 0 := by
  change rows (coefficientBasis (ActualPositiveWordPeriodicCochain.chart F).vertex)
    (coefficientBasis e) LinearMap.id i j = _
  rw [rows_coefficients]
  exact coefficient_apply _ i (e j)

/-- Both coefficient matrices and their inverse identities are explicit,
including the zero-dimensional case. -/
theorem chart_change_inverse (F : Presentation) {m : ℕ} (e : Fin m ≃ F.V) :
    changeRows (presentationBasis F) (coefficientBasis e) *
        changeRows (coefficientBasis e) (presentationBasis F) = 1 ∧
    changeRows (coefficientBasis e) (presentationBasis F) *
        changeRows (presentationBasis F) (coefficientBasis e) = 1 := by
  exact ⟨changeRows_inverse _ _, changeRows_inverse _ _⟩

/-- Actual Word/P1 consumer. It retains BOTH endpoint cochains, derives
both factor coordinates, and cancels the endpoints only after proving the
actual forward/backward RS equations. There is no rho identification here.
-/
theorem word_rebased {F : Presentation} (w : Word F F)
    (ht : IsUnit (vertex F).time) {m : ℕ} (e : Fin m ≃ F.V) :
    ∃ a : (Module.End D (F.V → D))ˣ,
      (a : Module.End D (F.V → D)) = endpointMap w ∧
      Commute (a : Module.End D (F.V → D)) (vertex F).time ∧
      let b := presentationBasis F
      let c := coefficientBasis e
      let C := changeRows b c
      let Cinv := changeRows c b
      let s : Module.End D (F.V → D) := ((vertex F).time : Module.End D (F.V → D)).comp (↑a⁻¹ : Module.End D (F.V → D))
      C * Cinv = 1 ∧ Cinv * C = 1 ∧
      (∀ i j, C i j = if (ActualPositiveWordPeriodicCochain.chart F).vertex i = e j
        then 1 else 0) ∧
      rows b b (a : Module.End D (F.V → D)) * C =
        C * rows c c (a : Module.End D (F.V → D)) ∧
      rows b b s * C = C * rows c c s ∧
      s.comp (a : Module.End D (F.V → D)) = (vertex F).time ∧
      (a : Module.End D (F.V → D)).comp s = (vertex F).time ∧
      ∀ (d : ℕ) [NeZero d] (hd : 3 ∣ d),
        (ActualWordLocalizedComparison.localizedCochain d hd w +
            value (d := d) b c LinearMap.id (vertex F).time =
          value (d := d) b c LinearMap.id (vertex F).time +
            dyadicGyration d (rowUnit c a : Mat m m)
              ((↑(rowUnit c a)⁻¹ : Mat m m) * rows c c (vertex F).time)) ∧
        ActualWordLocalizedComparison.localizedCochain d hd w =
          dyadicGyration d (rowUnit c a : Mat m m)
            ((↑(rowUnit c a)⁻¹ : Mat m m) * rows c c (vertex F).time) := by
  obtain ⟨a,ha,hc,hf,hs,hsr,hrs,hw⟩ :=
    path_rebased (dictionary w) ht (coefficientBasis e)
  refine ⟨a,ha.trans (SourceOnly.ActualWordMatrixPath.dictionary_forward w),hc,?_,?_,
    chart_change_entries F e,hf,hs,hsr,hrs,?_⟩
  · exact (chart_change_inverse F e).1
  · exact (chart_change_inverse F e).2
  · intro d _ hd
    have h := hw d hd
    rw [SourceOnly.ActualRelabelResidue.dictionary_residue w d hd] at h
    exact h

end SourceOnly.ActualWordEnumeratedLoop
