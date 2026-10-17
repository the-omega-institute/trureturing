/- SOURCE ONLY. UNCOMPILED. Unnamed application of the generic ranked-time
calibration to the literal ORIGINAL reset time. This is exactly the residual
Q=(tau^-1)^(a+k)*U telescope for the U previously constructed from the actual
Word. The original h supplies actual windows, the actual Word and its
actual endpoint unit. No rho/beam equality or orbit sum is an input. The
complete original-h character/root is not asserted.
-/
import D5.S3.ConceptDynamics.Coding.PresentationTimeCochain
import D5.S3.ConceptDynamics.Coding.CentralizerTimePowers
import D5.S3.ConceptDynamics.Coding.OriginalResponseTableIntake
import D5.S3.ConceptDynamics.Coding.OriginalPositiveWordAssembly
import D5.S3.ConceptDynamics.Coding.ResetQ4LocalizedGyrationCharacter

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding
open EssentialWordRealization TwoSidedFiniteInduction TypedPositiveSplitWord
open FiniteWindowTableCriterion StandardBeamHomeomorphisms
open ResponseTwoSidedConsumer OriginalPositiveWordAssembly
open InertGroupBlockConjugacy ResetNumberedHistories
open OriginalResponseTableIntake
open CountedOrderTypeGyration (dyadicGyration)
open ActualPositiveWordPeriodicCochain (Orbit)
open ResetQ4OriginalLocalizedCubes (T VertexIndex DyadicMatrix)
open ResetQ4LocalizedGyrationCharacter
  (originalRows vertexEquiv originalRows_mul originalRows_one columnGyration columnGyration_triangle)
open SourceOnly.ActualWordMatrixPath (D vertex timeMap endpointMap)
open SourceOnly.ActualWordEnumeratedLoop
  (coefficientBasis coefficient_apply coefficient_repr word_rebased columnUnit)
open SourceOnly.KernelRSSquareGyration (rows)
open scoped BigOperators Matrix

example (h : ResetFullAut 4) :
    let G := ResetGraph 4
    let P := original G (Alternating.reset_expanded_essential 4 (by omega))
    let σ : VertexIndex ≃ P.V := {
      toFun := fun v => (v.1,v.2)
      invFun := fun v => ⟨v.1,v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let b0 := coefficientBasis σ
    let c := coefficientBasis (vertexEquiv.trans σ)
    let τ := (ResetQ4OriginalLocalizedCubes.time : DyadicMatrixˣ)
    ∃ a b c' d : ℕ, ∃ w : Word P P,
    w.letters = (a+b+1)+2*((a+c')+(b+d+1)) ∧
    (∀ x : History G, h.val x = time G
      (-(a:ℤ)-(((a+c')+(b+d+1):ℕ):ℤ)) (w.eval x)) ∧
    ∃ U : DyadicMatrixˣ,
    (U : DyadicMatrix) = LinearMap.toMatrix b0 b0 (endpointMap w) ∧
    Commute (U : DyadicMatrix) T ∧
    let k := (a+c')+(b+d+1)
    let s : ℤ := -(a:ℤ)-(k:ℤ)
    let Q : DyadicMatrixˣ := (τ⁻¹)^(a+k)*U
    LinearMap.toMatrix b0 b0 (vertex P).time = T ∧
    originalRows T = rows c c (vertex P).time ∧
    originalRows ((↑U⁻¹ : DyadicMatrix)*T) =
      originalRows (↑U⁻¹ : DyadicMatrix)*originalRows T ∧
    originalRows ((↑Q⁻¹ : DyadicMatrix)*T) =
      originalRows (↑Q⁻¹ : DyadicMatrix)*originalRows T ∧
    (∀ (p : ℕ) [NeZero p], 3 ∣ p →
      columnGyration p (τ : DyadicMatrix) (↑τ⁻¹*T) =
        (Fintype.card (Orbit P p) : ZMod 3)) ∧
    (∀ (p : ℕ) [NeZero p], 3 ∣ p →
      dyadicGyration p (originalRows (Q : DyadicMatrix))
        (originalRows ((↑Q⁻¹ : DyadicMatrix)*T)) =
      dyadicGyration p (originalRows (U : DyadicMatrix))
        (originalRows ((↑U⁻¹ : DyadicMatrix)*T)) +
        (Fintype.card (Orbit P p) : ZMod 3)*(s : ZMod 3)) := by
  classical
  dsimp only
  let G := ResetGraph 4
  let P := original G (Alternating.reset_expanded_essential 4 (by omega))
  let σ : VertexIndex ≃ P.V := {
    toFun := fun v => (v.1,v.2)
    invFun := fun v => ⟨v.1,v.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let b0 := coefficientBasis σ
  let c := coefficientBasis (vertexEquiv.trans σ)
  let τ := (ResetQ4OriginalLocalizedCubes.time : DyadicMatrixˣ)
  -- Reuse the predecessor's actual native coefficient calculation, in this
  -- unnamed application. It is a local calculation, not a copied private
  -- supplier theorem or an assumed matrix/presentation identity.
  have hbc (i : Fin 8) : c i = b0 (vertexEquiv i) := by
    ext v
    rw [coefficient_apply, coefficient_apply]
    rfl
  have hrows (f : Module.End D (P.V → D)) :
      originalRows (LinearMap.toMatrix b0 b0 f) = rows c c f := by
    ext i j
    change b0.repr (f (b0 (vertexEquiv i))) (vertexEquiv j) = c.repr (f (c i)) j
    rw [coefficient_repr, coefficient_repr, hbc]
    rfl
  have hb0 (j : VertexIndex) : b0 j = Pi.single (j.1,j.2) (1 : D) := by
    ext v
    rw [coefficient_apply]
    simp [σ, Pi.single_apply, eq_comm]
  have hT : LinearMap.toMatrix b0 b0 (vertex P).time = T := by
    ext i j
    change b0.repr (timeMap G (b0 j)) i = algebraMap ℤ D
      ((LinearMap.toMatrix
        (vertexBasis (H := Sign) (n := 4)) (vertexBasis (H := Sign) (n := 4))
        (transition (resetMatrix 4))) i j)
    rw [coefficient_repr, hb0, LinearMap.toMatrix_apply]
    simp only [vertexBasis, Pi.basis_repr, Pi.basis_apply, MonoidAlgebra.basis_apply]
    change timeMap G (Pi.single (j.1,j.2) (1 : D)) (i.1,i.2) =
      algebraMap ℤ D (((transition (resetMatrix 4)
        (InertGroupBlockConjugacy.vertex j.1 j.2)) i.1).coeff i.2)
    rw [actual_expansion_adjacency]
    unfold timeMap
    rw [Matrix.toLinearMapRight'_apply, Matrix.single_vecMul]
    simp only [one_smul, Matrix.row, Matrix.map_apply, expanded_adjacency_eq]
    rfl
  have hA : originalRows T = rows c c (SourceOnly.ActualWordMatrixPath.vertex P).time := by
    rw [← hT]
    exact hrows _
  have hτ : (τ : DyadicMatrix) = T := ResetQ4OriginalLocalizedCubes.time_val
  -- Actual time invertibility comes from the EXISTING original time unit.
  -- No intermediate graph time or positive factor is required invertible.
  let τinv : Module.End D (P.V → D) :=
    (LinearMap.toMatrix b0 b0).symm (↑τ⁻¹ : DyadicMatrix)
  have hτmatrix : LinearMap.toMatrix b0 b0 (vertex P).time = (τ : DyadicMatrix) :=
    hT.trans hτ.symm
  let t : (Module.End D (P.V → D))ˣ := {
    val := (vertex P).time
    inv := τinv
    val_inv := by
      apply (LinearMap.toMatrix b0 b0).injective
      change LinearMap.toMatrix b0 b0 ((vertex P).time.comp τinv) =
        LinearMap.toMatrix b0 b0 LinearMap.id
      rw [LinearMap.toMatrix_comp, hτmatrix, LinearMap.toMatrix_id]
      change (τ : DyadicMatrix) * (LinearMap.toMatrix b0 b0)
        ((LinearMap.toMatrix b0 b0).symm ↑τ⁻¹) = 1
      rw [LinearEquiv.apply_symm_apply, Units.mul_inv]
    inv_val := by
      apply (LinearMap.toMatrix b0 b0).injective
      change LinearMap.toMatrix b0 b0 (τinv.comp (vertex P).time) =
        LinearMap.toMatrix b0 b0 LinearMap.id
      rw [LinearMap.toMatrix_comp, hτmatrix, LinearMap.toMatrix_id]
      change (LinearMap.toMatrix b0 b0)
        ((LinearMap.toMatrix b0 b0).symm ↑τ⁻¹) * (τ : DyadicMatrix) = 1
      rw [LinearEquiv.apply_symm_apply, Units.inv_mul] }
  have ht : IsUnit (vertex P).time := ⟨t,rfl⟩
  obtain ⟨a,b,c',d,hab,hcd⟩ := fullAut_has_two_windows G h
  let hG := Alternating.reset_expanded_essential 4 (by omega)
  let pair := tables G hG h a b c' d hab hcd
  let witness := actualWitness G hG h hab hcd
  obtain ⟨w,hletters,hhistory⟩ := positive_word G hG pair witness
  obtain ⟨u,hu,hcomm,hC,hCinv,hCent,hf,hb,hsr,hrs,hw⟩ :=
    word_rebased w ht (vertexEquiv.trans σ)
  let U := columnUnit b0 u
  let k := (a+c')+(b+d+1)
  let s : ℤ := -(a:ℤ)-(k:ℤ)
  have hU : (U : DyadicMatrix) = LinearMap.toMatrix b0 b0 (endpointMap w) := by
    change LinearMap.toMatrix b0 b0 (u : Module.End D (P.V → D)) = _
    rw [hu]
  have hUcomm : Commute (U : DyadicMatrix) T := by
    change LinearMap.toMatrix b0 b0 (u : Module.End D (P.V → D))*T =
      T*LinearMap.toMatrix b0 b0 (u : Module.End D (P.V → D))
    rw [← hT, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    exact congrArg (LinearMap.toMatrix b0 b0) hcomm.eq
  have hc : Commute U τ := by
    change U*τ = τ*U
    apply Units.ext
    simpa only [Units.val_mul, hτ] using hUcomm.eq
  have hOrder (V : DyadicMatrixˣ) (hV : Commute V τ) :
      originalRows ((↑V⁻¹ : DyadicMatrix)*T) =
        originalRows (↑V⁻¹ : DyadicMatrix)*originalRows T := by
    have hiorder : T*(↑V⁻¹ : DyadicMatrix) = (↑V⁻¹ : DyadicMatrix)*T := by
      have he := congrArg (fun W : DyadicMatrixˣ => (W : DyadicMatrix)) hV.inv_left.eq.symm
      simpa only [Units.val_mul, hτ] using he
    rw [← hiorder, originalRows_mul]
  have hQc : Commute ((τ⁻¹)^(a+k)*U) τ :=
    ((Commute.refl τ).inv_left.pow_left (a+k)).mul_left hc
  have hi : (↑τ⁻¹ : DyadicMatrix)*T = 1 := by
    rw [← hτ]
    exact Units.inv_mul τ
  have hcal (p : ℕ) [NeZero p] (hp : 3 ∣ p) :
      columnGyration p (τ : DyadicMatrix) (↑τ⁻¹*T) =
        (Fintype.card (Orbit P p) : ZMod 3) := by
    change dyadicGyration p (originalRows (τ : DyadicMatrix))
      (originalRows (↑τ⁻¹*T)) = _
    rw [hτ, hi, originalRows_one, hA]
    exact (SourceOnly.PresentationTimeCochain.time_calibration P c p hp).2
  refine ⟨a,b,c',d,w,hletters,hhistory,U,hU,hUcomm,
    hT,hA,hOrder U hc,hOrder _ hQc,hcal,?_⟩
  intro p _ hp
  have he := SourceOnly.CentralizerTimePowers.translated_value T
    (columnGyration p) (columnGyration_triangle hp) τ U hτ s
  rw [hcal p hp] at he
  have hs : s = -((a+k : ℕ) : ℤ) := by dsimp [s]; push_cast; ring
  have hpow : τ^s = (τ⁻¹)^(a+k) := by
    simp only [hs, zpow_neg, zpow_natCast, inv_pow]
  rw [hpow, mul_comm (s : ZMod 3)] at he
  exact he

end D5.S3.ConceptDynamics.Coding
