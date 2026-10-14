import D5.S3.VertexAlgebra.OriginalIntegralBVGerstBracketTransient

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralGhostDegreeTransient

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge OriginalBrstReassembly
open scoped VertexOperator

private theorem covariance_exactly (data : LatticeData) (state input : State data) (mode : ℤ) :
    nativeJ data (((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) input) =
      ((LatticeBcGhostTensorStateField.stateField data (nativeJ data state))[[mode]]) input +
        ((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) (nativeJ data input) :=
  OriginalIntegralBVGerstBracketTransient.AcceptedGhostCovariance.stateField_ghostNumber_covariance_state
    data state input mode

private theorem field_state_number (data : LatticeData) (degree mode : ℤ)
    (state vector : State data) (member : state ∈ ghostPart data degree) :
    ((LatticeBcGhostTensorStateField.stateField data (nativeJ data state))[[mode]]) vector =
      (degree : ℂ) • ((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) vector := by
  have eigen : nativeJ data state = (degree : ℂ) • state :=
    (ghostPart_iff_number data degree state).mp member
  exact (congrArg (fun argument : State data =>
    ((LatticeBcGhostTensorStateField.stateField data argument)[[mode]]) vector) eigen).trans
      (by simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply])

private theorem field_input_number (data : LatticeData) (degree mode : ℤ)
    (state vector : State data) (member : vector ∈ ghostPart data degree) :
    ((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) (nativeJ data vector) =
      (degree : ℂ) • ((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) vector := by
  have eigen : nativeJ data vector = (degree : ℂ) • vector :=
    (ghostPart_iff_number data degree vector).mp member
  exact (congrArg ((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) eigen).trans
    (((LatticeBcGhostTensorStateField.stateField data state)[[mode]]).map_smul (degree : ℂ) vector)

private theorem scalar_degree_sum (data : LatticeData) (leftDegree rightDegree : ℤ)
    (vector : State data) :
    (leftDegree : ℂ) • vector + (rightDegree : ℂ) • vector =
      ((leftDegree + rightDegree : ℤ) : ℂ) • vector := by
  simp only [Int.cast_add, add_smul]

theorem native_field_integer_degree (data : LatticeData) (leftDegree rightDegree mode : ℤ)
    (state vector : State data) (stateDegree : state ∈ ghostPart data leftDegree)
    (vectorDegree : vector ∈ ghostPart data rightDegree) :
    ((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) vector ∈
      ghostPart data (leftDegree + rightDegree) := by
  apply (ghostPart_iff_number data (leftDegree + rightDegree) _).mpr
  exact (covariance_exactly data state vector mode).trans
    ((congrArg₂ (fun first second : State data => first + second)
      (field_state_number data leftDegree mode state vector stateDegree)
      (field_input_number data rightDegree mode state vector vectorDegree)).trans
      (scalar_degree_sum data leftDegree rightDegree
        (((LatticeBcGhostTensorStateField.stateField data state)[[mode]]) vector)))

#print axioms native_field_integer_degree

end D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralGhostDegreeTransient
