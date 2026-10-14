import D5.S3.VertexAlgebra.OriginalQFiniteTransferLawsTransient

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQFiniteHplCheck

theorem finite_transfer_ring_laws {Algebra : Type*} [Ring Algebra]
    (leading homotopy projector original inverse : Algebra)
    (originalSquare : original * original = 0)
    (homotopySquare : homotopy * homotopy = 0)
    (contraction : leading * homotopy + homotopy * leading = 1 - projector)
    (homotopyProjector : homotopy * projector = 0)
    (projectorHomotopy : projector * homotopy = 0)
    (leadingProjector : leading * projector = 0)
    (projectorSquare : projector * projector = projector)
    (correctionIdentity : (1 + homotopy * (original - leading)) * original =
      leading * (1 + homotopy * (original - leading)) + projector * (original - leading))
    (inverseLeft : inverse * (1 + homotopy * (original - leading)) = 1)
    (inverseRight : (1 + homotopy * (original - leading)) * inverse = 1) :
    let perturbation := original - leading
    let inclusion := inverse * projector
    let transferHomotopy := inverse * homotopy
    let projection := projector * (1 - perturbation * transferHomotopy)
    let transferred := projector * perturbation * inverse * projector
    original * inclusion = inclusion * transferred ∧
      projection * original = transferred * projection ∧
      projection * inclusion = projector ∧
      original * transferHomotopy + transferHomotopy * original = 1 - inclusion * projection ∧
      transferred * transferred = 0 := by
  dsimp only
  let perturbation := original - leading
  let inclusion := inverse * projector
  let transferHomotopy := inverse * homotopy
  let projection := projector * (1 - perturbation * transferHomotopy)
  let transferred := projector * perturbation * inverse * projector
  have hInverse : homotopy * inverse = homotopy := by
    calc
      _ = (homotopy + (homotopy * homotopy) * perturbation) * inverse := by
        rw [homotopySquare, zero_mul, add_zero]
      _ = homotopy * ((1 + homotopy * perturbation) * inverse) := by noncomm_ring
      _ = _ := by rw [inverseRight, mul_one]
  have pInverse : projector * inverse = projector := by
    calc
      _ = (projector + (projector * homotopy) * perturbation) * inverse := by
        rw [projectorHomotopy, zero_mul, add_zero]
      _ = projector * ((1 + homotopy * perturbation) * inverse) := by noncomm_ring
      _ = _ := by rw [inverseRight, mul_one]
  have inverseFormula : inverse = 1 - transferHomotopy * perturbation := by
    change inverse = 1 - (inverse * homotopy) * perturbation
    have expanded : inverse + (inverse * homotopy) * perturbation = 1 := by
      calc
        _ = inverse * (1 + homotopy * perturbation) := by noncomm_ring
        _ = 1 := inverseLeft
    rw [← expanded]
    abel
  have qInverse : original * inverse = inverse * leading + inclusion * perturbation * inverse := by
    calc
      _ = inverse * ((1 + homotopy * perturbation) * original) * inverse := by
        rw [← mul_assoc inverse, inverseLeft, one_mul]
      _ = inverse * (leading * (1 + homotopy * perturbation) + projector * perturbation) * inverse := by
        rw [correctionIdentity]
      _ = inverse * leading * ((1 + homotopy * perturbation) * inverse) +
          inclusion * perturbation * inverse := by dsimp [inclusion]; noncomm_ring
      _ = _ := by rw [inverseRight, mul_one]
  have inclusionProjector : inclusion * projector = inclusion := by
    dsimp [inclusion]
    rw [mul_assoc, projectorSquare]
  have projectorTransfer : projector * transferred = transferred := by
    dsimp [transferred]
    simp only [← mul_assoc, projectorSquare]
  have projectorProjection : projector * projection = projection := by
    dsimp [projection]
    rw [← mul_assoc, projectorSquare]
  have homotopyInclusion : transferHomotopy * inclusion = 0 := by
    dsimp [transferHomotopy, inclusion]
    rw [mul_assoc, ← mul_assoc homotopy, hInverse, homotopyProjector, mul_zero]
  have retract : projection * inclusion = projector := by
    calc
      _ = projector * inverse * projector - projector * perturbation *
          (transferHomotopy * inclusion) := by dsimp [projection, inclusion]; noncomm_ring
      _ = projector := by rw [pInverse, projectorSquare, homotopyInclusion, mul_zero, sub_zero]
  have inclusionChain : original * inclusion = inclusion * transferred := by
    calc
      _ = (original * inverse) * projector := by dsimp [inclusion]; noncomm_ring
      _ = (inverse * leading + inclusion * perturbation * inverse) * projector := by rw [qInverse]
      _ = inverse * (leading * projector) +
          (inclusion * projector) * perturbation * inverse * projector := by
            rw [inclusionProjector]
            noncomm_ring
      _ = inclusion * transferred := by
        rw [leadingProjector, mul_zero, zero_add]
        dsimp [transferred]
        noncomm_ring
  have homotopyLaw : original * transferHomotopy + transferHomotopy * original =
      1 - inclusion * projection := by
    calc
      _ = inverse * (leading * homotopy + homotopy * leading) +
          transferHomotopy * perturbation + inclusion * perturbation * transferHomotopy := by
            dsimp [transferHomotopy]
            rw [← mul_assoc original inverse, qInverse]
            dsimp [perturbation]
            noncomm_ring
      _ = inverse - inclusion + transferHomotopy * perturbation +
          inclusion * perturbation * transferHomotopy := by rw [contraction]; dsimp [inclusion]; noncomm_ring
      _ = 1 - inclusion * projection := by
        rw [inverseFormula]
        dsimp [projection]
        rw [← mul_assoc inclusion projector, inclusionProjector]
        noncomm_ring
  have retractCommutes : (inclusion * projection) * original = original * (inclusion * projection) := by
    have equality := congrArg (fun value => value * original - original * value) homotopyLaw
    have vanishing : original * transferHomotopy * original +
        transferHomotopy * (original * original) - (original * original) * transferHomotopy -
        original * transferHomotopy * original = 0 := by rw [originalSquare]; simp
    have expanded : (original * transferHomotopy + transferHomotopy * original) * original -
        original * (original * transferHomotopy + transferHomotopy * original) = 0 := by
      calc
        _ = _ := by noncomm_ring
        _ = 0 := vanishing
    rw [homotopyLaw] at expanded
    have difference : original * (inclusion * projection) - (inclusion * projection) * original = 0 := by
      calc
        _ = (1 - inclusion * projection) * original - original * (1 - inclusion * projection) := by
          noncomm_ring
        _ = 0 := expanded
    exact (sub_eq_zero.mp difference).symm
  have projectionChain : projection * original = transferred * projection := by
    calc
      _ = (projection * inclusion) * projection * original := by rw [retract, projectorProjection]
      _ = projection * ((inclusion * projection) * original) := by noncomm_ring
      _ = projection * (original * (inclusion * projection)) := by rw [retractCommutes]
      _ = projection * (original * inclusion) * projection := by noncomm_ring
      _ = projection * (inclusion * transferred) * projection := by rw [inclusionChain]
      _ = transferred * projection := by rw [← mul_assoc projection inclusion, retract, projectorTransfer]
  have transferredSquare : transferred * transferred = 0 := by
    calc
      _ = (projection * inclusion) * transferred * transferred := by rw [retract, projectorTransfer]
      _ = projection * (inclusion * transferred) * transferred := by noncomm_ring
      _ = projection * (original * inclusion) * transferred := by rw [inclusionChain]
      _ = projection * original * (inclusion * transferred) := by noncomm_ring
      _ = projection * original * (original * inclusion) := by rw [inclusionChain]
      _ = projection * (original * original) * inclusion := by noncomm_ring
      _ = 0 := by rw [originalSquare, mul_zero, zero_mul]
  exact ⟨inclusionChain, projectionChain, retract, homotopyLaw, transferredSquare⟩

end D5.S3.VertexAlgebra.OriginalQFiniteHplCheck
