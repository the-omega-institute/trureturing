/- GID: D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/VertexOperatorTensorProductLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite nested diagonals and scalar-signed tensor locality. -/

/-
proof_shape: convolution_finite: content; convolution_delta_left: content
escape_witness: Nested truncation produces finite two-index convolution
support. Reindexing transfers the clearing polynomial between factors.
admission_basis: escape-witness
Classical source: coefficientwise locality of products of formal fields.
The scalar sign records operator exchange, not a Koszul state assignment.
-/

import D5.S3.VertexAlgebra.VertexOperatorTensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality

open D5.S3.VertexAlgebra.VertexOperatorTensorProduct
open scoped TensorProduct VertexOperator

universe u v w

variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

abbrev Pair (W : Type*) := ℤ → ℤ → W

def shiftFirst (value : Pair W) : Pair W := fun first second => value (first + 1) second

def shiftSecond (value : Pair W) : Pair W := fun first second => value first (second + 1)

def delta : Module.End ℂ (Pair W) where
  toFun value := shiftFirst value - shiftSecond value
  map_add' first second := by funext left right; simp [shiftFirst, shiftSecond]; abel
  map_smul' scalar value := by
    funext left right
    simp [shiftFirst, shiftSecond, smul_sub]

def Truncated (value : Pair W) : Prop :=
  (∃ bound : ℤ, ∀ first second : ℤ, bound < second → value first second = 0) ∧
    (∀ second : ℤ, ∃ bound : ℤ, ∀ first : ℤ, bound < first → value first second = 0)

def flip (value : Pair W) : Pair W := fun first second => value second first

def Compatible (left : Pair U) (right : Pair V) : Prop :=
  (Truncated left ∧ Truncated right) ∨ (Truncated (flip left) ∧ Truncated (flip right))

omit [Module ℂ W] in
theorem truncated_shiftFirst {value : Pair W} (bounded : Truncated value) :
    Truncated (shiftFirst value) := by
  constructor
  · obtain ⟨bound, law⟩ := bounded.1
    exact ⟨bound, fun first second above => law (first + 1) second above⟩
  · intro second
    obtain ⟨bound, law⟩ := bounded.2 second
    exact ⟨bound, fun first above => law (first + 1) (by omega)⟩

omit [Module ℂ W] in
theorem truncated_shiftSecond {value : Pair W} (bounded : Truncated value) :
    Truncated (shiftSecond value) := by
  constructor
  · obtain ⟨bound, law⟩ := bounded.1
    exact ⟨bound, fun first second above => law first (second + 1) (by omega)⟩
  · intro second
    obtain ⟨bound, law⟩ := bounded.2 (second + 1)
    exact ⟨bound, fun first above => law first above⟩

omit [Module ℂ W] in
theorem truncated_sub {first second : Pair W}
    (firstBound : Truncated first) (secondBound : Truncated second) :
    Truncated (first - second) := by
  constructor
  · obtain ⟨left, leftLaw⟩ := firstBound.1
    obtain ⟨right, rightLaw⟩ := secondBound.1
    refine ⟨max left right, ?_⟩
    intro first second above
    simp only [Pi.sub_apply, leftLaw first second (lt_of_le_of_lt (le_max_left _ _) above),
      rightLaw first second (lt_of_le_of_lt (le_max_right _ _) above), sub_self]
  · intro second
    obtain ⟨left, leftLaw⟩ := firstBound.2 second
    obtain ⟨right, rightLaw⟩ := secondBound.2 second
    refine ⟨max left right, ?_⟩
    intro first above
    simp only [Pi.sub_apply, leftLaw first (lt_of_le_of_lt (le_max_left _ _) above),
      rightLaw first (lt_of_le_of_lt (le_max_right _ _) above), sub_self]

theorem truncated_delta {value : Pair W} (bounded : Truncated value) :
    Truncated (delta value) :=
  truncated_sub (truncated_shiftFirst bounded) (truncated_shiftSecond bounded)

theorem truncated_delta_pow {value : Pair W} (bounded : Truncated value) (order : ℕ) :
    Truncated ((delta ^ order) value) := by
  induction order with
  | zero => simpa using bounded
  | succ order induction =>
      simpa only [pow_succ', Module.End.mul_apply] using truncated_delta induction

def term (left : Pair U) (right : Pair V) (first second : ℤ)
    (indices : ℤ × ℤ) : U ⊗[ℂ] V :=
  left indices.2 indices.1 ⊗ₜ[ℂ] right (first - 1 - indices.2) (second - 1 - indices.1)

theorem convolution_finite_truncated (left : Pair U) (right : Pair V)
    (leftBound : Truncated left) (rightBound : Truncated right) (first second : ℤ) :
    Function.HasFiniteSupport (term left right first second) := by
  classical
  obtain ⟨leftOuter, leftOuterLaw⟩ := leftBound.1
  obtain ⟨rightOuter, rightOuterLaw⟩ := rightBound.1
  choose leftInner leftInnerLaw using leftBound.2
  choose rightInner rightInnerLaw using rightBound.2
  let outer := Finset.Icc (second - 1 - rightOuter) leftOuter
  let bounds := outer.biUnion fun index =>
    (Finset.Icc (first - 1 - rightInner (second - 1 - index)) (leftInner index)).image
      (fun inner => (index, inner))
  refine bounds.finite_toSet.subset ?_
  intro indices member
  have leftNonzero : left indices.2 indices.1 ≠ 0 := by
    intro vanished
    exact member (by simp [term, vanished])
  have rightNonzero : right (first - 1 - indices.2) (second - 1 - indices.1) ≠ 0 := by
    intro vanished
    exact member (by simp [term, vanished])
  have outerLeft : indices.1 ≤ leftOuter := by
    by_contra bound
    exact leftNonzero (leftOuterLaw _ _ (by omega))
  have outerRight : second - 1 - rightOuter ≤ indices.1 := by
    by_contra bound
    exact rightNonzero (rightOuterLaw _ _ (by omega))
  have innerLeft : indices.2 ≤ leftInner indices.1 := by
    by_contra bound
    exact leftNonzero (leftInnerLaw _ _ (by omega))
  have innerRight : first - 1 - rightInner (second - 1 - indices.1) ≤ indices.2 := by
    by_contra bound
    exact rightNonzero (rightInnerLaw _ _ (by omega))
  apply Finset.mem_biUnion.mpr
  refine ⟨indices.1, Finset.mem_Icc.mpr ⟨outerRight, outerLeft⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨indices.2, Finset.mem_Icc.mpr ⟨innerRight, innerLeft⟩, rfl⟩

theorem convolution_finite (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) (first second : ℤ) :
    Function.HasFiniteSupport (term left right first second) := by
  rcases bounded with forward | backward
  · exact convolution_finite_truncated left right forward.1 forward.2 first second
  · have finite := convolution_finite_truncated (flip left) (flip right)
      backward.1 backward.2 second first
    have pullback := Function.HasFiniteSupport.comp_of_injective
      (Equiv.prodComm ℤ ℤ).injective finite
    change Function.HasFiniteSupport (term left right first second) at pullback
    exact pullback

def convolution (left : Pair U) (right : Pair V) : Pair (U ⊗[ℂ] V) :=
  fun first second => ∑ᶠ indices : ℤ × ℤ, term left right first second indices

omit [Module ℂ U] [Module ℂ V] in
theorem compatible_shiftFirst_left {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) : Compatible (shiftFirst left) right := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨truncated_shiftFirst forward.1, forward.2⟩
  · exact Or.inr ⟨truncated_shiftSecond backward.1, backward.2⟩

omit [Module ℂ U] [Module ℂ V] in
theorem compatible_shiftSecond_left {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) : Compatible (shiftSecond left) right := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨truncated_shiftSecond forward.1, forward.2⟩
  · exact Or.inr ⟨truncated_shiftFirst backward.1, backward.2⟩

def firstEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun indices := (indices.1, indices.2 + 1)
  invFun indices := (indices.1, indices.2 - 1)
  left_inv indices := by ext <;> simp
  right_inv indices := by ext <;> simp

def secondEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun indices := (indices.1 + 1, indices.2)
  invFun indices := (indices.1 - 1, indices.2)
  left_inv indices := by ext <;> simp
  right_inv indices := by ext <;> simp

theorem convolution_shiftFirst_left (left : Pair U) (right : Pair V) :
    convolution (shiftFirst left) right = shiftFirst (convolution left right) := by
  funext first second
  apply finsum_eq_of_bijective firstEquiv firstEquiv.bijective
  intro indices
  dsimp [term, shiftFirst, firstEquiv]
  congr 2
  omega

theorem convolution_shiftSecond_left (left : Pair U) (right : Pair V) :
    convolution (shiftSecond left) right = shiftSecond (convolution left right) := by
  funext first second
  apply finsum_eq_of_bijective secondEquiv secondEquiv.bijective
  intro indices
  dsimp [term, shiftSecond, secondEquiv]
  congr 2
  omega

theorem convolution_delta_left (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) :
    convolution (delta left) right = delta (convolution left right) := by
  have firstFinite := convolution_finite (shiftFirst left) right
    (compatible_shiftFirst_left bounded)
  have secondFinite := convolution_finite (shiftSecond left) right
    (compatible_shiftSecond_left bounded)
  have difference : convolution (delta left) right =
      convolution (shiftFirst left) right - convolution (shiftSecond left) right := by
    funext first second
    change (∑ᶠ indices : ℤ × ℤ, (shiftFirst left indices.2 indices.1 -
      shiftSecond left indices.2 indices.1) ⊗ₜ[ℂ]
      right (first - 1 - indices.2) (second - 1 - indices.1)) = _
    simp only [TensorProduct.sub_tmul]
    exact finsum_sub_distrib (firstFinite first second) (secondFinite first second)
  rw [difference, convolution_shiftFirst_left, convolution_shiftSecond_left]
  rfl

omit [Module ℂ U] [Module ℂ V] in
theorem compatible_shiftFirst_right {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) : Compatible left (shiftFirst right) := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨forward.1, truncated_shiftFirst forward.2⟩
  · exact Or.inr ⟨backward.1, truncated_shiftSecond backward.2⟩

omit [Module ℂ U] [Module ℂ V] in
theorem compatible_shiftSecond_right {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) : Compatible left (shiftSecond right) := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨forward.1, truncated_shiftSecond forward.2⟩
  · exact Or.inr ⟨backward.1, truncated_shiftFirst backward.2⟩

theorem convolution_shiftFirst_right (left : Pair U) (right : Pair V) :
    convolution left (shiftFirst right) = shiftFirst (convolution left right) := by
  funext first second
  apply finsum_congr
  intro indices
  dsimp [term, shiftFirst]
  congr 2
  omega

theorem convolution_shiftSecond_right (left : Pair U) (right : Pair V) :
    convolution left (shiftSecond right) = shiftSecond (convolution left right) := by
  funext first second
  apply finsum_congr
  intro indices
  dsimp [term, shiftSecond]
  congr 2
  omega

theorem convolution_delta_right (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) :
    convolution left (delta right) = delta (convolution left right) := by
  have firstFinite := convolution_finite left (shiftFirst right)
    (compatible_shiftFirst_right bounded)
  have secondFinite := convolution_finite left (shiftSecond right)
    (compatible_shiftSecond_right bounded)
  have difference : convolution left (delta right) =
      convolution left (shiftFirst right) - convolution left (shiftSecond right) := by
    funext first second
    change (∑ᶠ indices : ℤ × ℤ, left indices.2 indices.1 ⊗ₜ[ℂ]
      (shiftFirst right (first - 1 - indices.2) (second - 1 - indices.1) -
       shiftSecond right (first - 1 - indices.2) (second - 1 - indices.1))) = _
    simp only [TensorProduct.tmul_sub]
    exact finsum_sub_distrib (firstFinite first second) (secondFinite first second)
  rw [difference, convolution_shiftFirst_right, convolution_shiftSecond_right]
  rfl

omit [Module ℂ V] in
theorem compatible_delta_left {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) : Compatible (delta left) right := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨truncated_delta forward.1, forward.2⟩
  · refine Or.inr ⟨?_, backward.2⟩
    exact truncated_sub (truncated_shiftSecond backward.1) (truncated_shiftFirst backward.1)

omit [Module ℂ U] in
theorem compatible_delta_right {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) : Compatible left (delta right) := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨forward.1, truncated_delta forward.2⟩
  · refine Or.inr ⟨backward.1, ?_⟩
    exact truncated_sub (truncated_shiftSecond backward.2) (truncated_shiftFirst backward.2)

omit [Module ℂ V] in
theorem compatible_delta_pow_left {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) (order : ℕ) :
    Compatible ((delta ^ order) left) right := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨truncated_delta_pow forward.1 order, forward.2⟩
  · induction order with
    | zero => change Compatible left right; exact Or.inr backward
    | succ order induction =>
        simpa only [pow_succ', Module.End.mul_apply] using compatible_delta_left induction

omit [Module ℂ U] in
theorem compatible_delta_pow_right {left : Pair U} {right : Pair V}
    (bounded : Compatible left right) (order : ℕ) :
    Compatible left ((delta ^ order) right) := by
  rcases bounded with forward | backward
  · exact Or.inl ⟨forward.1, truncated_delta_pow forward.2 order⟩
  · induction order with
    | zero => change Compatible left right; exact Or.inr backward
    | succ order induction =>
        simpa only [pow_succ', Module.End.mul_apply] using compatible_delta_right induction

theorem convolution_delta_pow_left (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) (order : ℕ) :
    convolution ((delta ^ order) left) right = (delta ^ order) (convolution left right) := by
  induction order with
  | zero => simp
  | succ order induction =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [convolution_delta_left _ _ (compatible_delta_pow_left bounded order), induction]

theorem convolution_delta_pow_right (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) (order : ℕ) :
    convolution left ((delta ^ order) right) = (delta ^ order) (convolution left right) := by
  induction order with
  | zero => simp
  | succ order induction =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [convolution_delta_right _ _ (compatible_delta_pow_right bounded order), induction]

theorem convolution_clearing (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) (firstOrder secondOrder : ℕ) :
    convolution ((delta ^ firstOrder) left) ((delta ^ secondOrder) right) =
      (delta ^ (firstOrder + secondOrder)) (convolution left right) := by
  rw [convolution_delta_pow_left _ _ (compatible_delta_pow_right bounded secondOrder),
    convolution_delta_pow_right _ _ bounded, pow_add, Module.End.mul_apply]

theorem convolution_smul (left : Pair U) (right : Pair V)
    (bounded : Compatible left right) (firstSign secondSign : ℂ) :
    convolution (firstSign • left) (secondSign • right) =
      (firstSign * secondSign) • convolution left right := by
  funext first second
  change (∑ᶠ indices : ℤ × ℤ, (firstSign • left indices.2 indices.1) ⊗ₜ[ℂ]
    (secondSign • right (first - 1 - indices.2) (second - 1 - indices.1))) = _
  simp only [TensorProduct.smul_tmul_smul]
  exact (smul_finsum' _ (convolution_finite left right bounded first second)).symm

theorem convolution_signed_clearing (left reverseLeft : Pair U) (right reverseRight : Pair V)
    (forwardBound : Compatible left right) (reverseBound : Compatible reverseLeft reverseRight)
    (firstSign secondSign : ℂ) (firstOrder secondOrder : ℕ)
    (firstLocal : (delta ^ firstOrder) left = firstSign • (delta ^ firstOrder) reverseLeft)
    (secondLocal : (delta ^ secondOrder) right = secondSign • (delta ^ secondOrder) reverseRight) :
    (delta ^ (firstOrder + secondOrder)) (convolution left right) =
      (firstSign * secondSign) •
        (delta ^ (firstOrder + secondOrder)) (convolution reverseLeft reverseRight) := by
  rw [← convolution_clearing _ _ forwardBound, firstLocal, secondLocal,
    convolution_smul _ _
      (compatible_delta_pow_right (compatible_delta_pow_left reverseBound firstOrder) secondOrder),
    convolution_clearing _ _ reverseBound]

theorem convolution_flip (left : Pair U) (right : Pair V) :
    convolution (flip left) (flip right) = flip (convolution left right) := by
  funext first second
  apply finsum_eq_of_bijective (Equiv.prodComm ℤ ℤ) (Equiv.prodComm ℤ ℤ).bijective
  intro indices
  rfl

def ordered (A C : VertexOperator ℂ W) (vector : W) : Pair W :=
  fun first second => (A[[first]]) ((C[[second]]) vector)

def reversed (A C : VertexOperator ℂ W) (vector : W) : Pair W :=
  fun first second => (C[[second]]) ((A[[first]]) vector)

def SignedLocal (A C : VertexOperator ℂ W) (sign : ℂ) (order : ℕ) : Prop :=
  ∀ vector : W, (delta ^ order) (ordered A C vector - sign • reversed A C vector) = 0

theorem ordered_truncated (A C : VertexOperator ℂ W) (vector : W) :
    Truncated (ordered A C vector) := by
  constructor
  · refine ⟨upper C vector, ?_⟩
    intro first second above
    simp [ordered, mode_zero_above C vector second above]
  · intro second
    refine ⟨upper A ((C[[second]]) vector), ?_⟩
    intro first above
    exact mode_zero_above A ((C[[second]]) vector) first above

theorem ordered_tensor (A C : VertexOperator ℂ U) (B D : VertexOperator ℂ V)
    (left : U) (right : V) :
    ordered (field A B) (field C D) (left ⊗ₜ[ℂ] right) =
      convolution (ordered A C left) (ordered B D right) := by
  funext first second
  have bounded : Compatible (ordered A C left) (ordered B D right) :=
    Or.inl ⟨ordered_truncated A C left, ordered_truncated B D right⟩
  have finite := convolution_finite _ _ bounded first second
  have move : (mode A B first) (∑ᶠ index : ℤ, diagonal C D second left right index) =
      ∑ᶠ index : ℤ, (mode A B first) (diagonal C D second left right index) :=
    (mode A B first).toAddMonoidHom.map_finsum (diagonal_finite C D second left right)
  simp only [ordered, field_mode]
  rw [mode_tmul]
  change (mode A B first) (∑ᶠ index : ℤ, diagonal C D second left right index) = _
  rw [move]
  simp only [diagonal]
  simp only [mode_tmul]
  exact (finsum_curry (term (ordered A C left) (ordered B D right) first second) finite).symm

theorem reversed_tensor (A C : VertexOperator ℂ U) (B D : VertexOperator ℂ V)
    (left : U) (right : V) :
    reversed (field A B) (field C D) (left ⊗ₜ[ℂ] right) =
      convolution (reversed A C left) (reversed B D right) := by
  change flip (ordered (field C D) (field A B) (left ⊗ₜ[ℂ] right)) =
    convolution (flip (ordered C A left)) (flip (ordered D B right))
  rw [ordered_tensor, convolution_flip]

theorem clearing_identity (A C : VertexOperator ℂ W) (sign : ℂ) (order : ℕ)
    (locality : SignedLocal A C sign order) (vector : W) :
    (delta ^ order) (ordered A C vector) =
      sign • (delta ^ order) (reversed A C vector) := by
  have killed := locality vector
  rw [map_sub, map_smul] at killed
  exact sub_eq_zero.mp killed

theorem signedLocal_tensor (A C : VertexOperator ℂ U) (B D : VertexOperator ℂ V)
    (firstSign secondSign : ℂ) (firstOrder secondOrder : ℕ)
    (firstLocal : SignedLocal A C firstSign firstOrder)
    (secondLocal : SignedLocal B D secondSign secondOrder) :
    SignedLocal (field A B) (field C D) (firstSign * secondSign) (firstOrder + secondOrder) := by
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero =>
      have forward : ordered (field A B) (field C D) 0 = 0 := by
        funext first second; simp [ordered]
      have backward : reversed (field A B) (field C D) 0 = 0 := by
        funext first second; simp [reversed]
      simp only [forward, backward, smul_zero, sub_self, map_zero]
  | tmul left right =>
      rw [ordered_tensor, reversed_tensor, map_sub, map_smul]
      apply sub_eq_zero.mpr
      exact convolution_signed_clearing _ _ _ _
        (Or.inl ⟨ordered_truncated A C left, ordered_truncated B D right⟩)
        (Or.inr ⟨ordered_truncated C A left, ordered_truncated D B right⟩)
        firstSign secondSign firstOrder secondOrder
        (clearing_identity A C firstSign firstOrder firstLocal left)
        (clearing_identity B D secondSign secondOrder secondLocal right)
  | add first second firstIH secondIH =>
      have forward : ordered (field A B) (field C D) (first + second) =
          ordered (field A B) (field C D) first + ordered (field A B) (field C D) second := by
        funext left right; simp [ordered]
      have backward : reversed (field A B) (field C D) (first + second) =
          reversed (field A B) (field C D) first + reversed (field A B) (field C D) second := by
        funext left right; simp [reversed]
      rw [forward, backward, smul_add]
      have regroup : ordered (field A B) (field C D) first +
          ordered (field A B) (field C D) second -
          ((firstSign * secondSign) • reversed (field A B) (field C D) first +
           (firstSign * secondSign) • reversed (field A B) (field C D) second) =
          (ordered (field A B) (field C D) first -
           (firstSign * secondSign) • reversed (field A B) (field C D) first) +
          (ordered (field A B) (field C D) second -
           (firstSign * secondSign) • reversed (field A B) (field C D) second) := by abel
      rw [regroup, map_add, firstIH, secondIH, add_zero]

end D5.S3.VertexAlgebra.VertexOperatorTensorProductLocality
