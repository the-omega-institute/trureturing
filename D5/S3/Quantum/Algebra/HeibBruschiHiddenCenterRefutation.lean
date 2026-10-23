/- GID: D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.claim; result=D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.result; claim=D5/S3/Quantum/Algebra/HeibBruschiHiddenCenterRefutation.claim
   digest: Refutes Heib-Bruschi Conjecture 80 over every field with a hidden central direction. -/

import D5.S3.Quantum.Algebra.HeibBruschiCenterlessIdealGraphRefutation
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.TransferInstance
import Mathlib.LinearAlgebra.CrossProduct

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Algebra.HeibBruschiHiddenCenterRefutation

open D5.S3.Quantum.Algebra.HeibBruschiCenterlessIdealGraphRefutation
open Module
open scoped Matrix

variable {K L : Type} [Field K] [LieRing L] [LieAlgebra K L]

def conjecture80Over (K : Type) [Field K] : Prop :=
  ∀ (L : Type) [LieRing L] [LieAlgebra K L] (n : ℕ) (b : Basis (Fin n) K L),
    IsAdmissible b → LieAlgebra.center K L ≠ ⊥ →
      ∃ W : Set (Fin n), W.Nonempty ∧ W ≠ Set.univ ∧ IdealGraphProperty b W ∧
        ∃ I : LieIdeal K L,
          (I : Submodule K L) = Submodule.span K (b '' W) ∧ LieAlgebra.IsSolvable I

def claim : Prop := ∀ (K : Type) [Field K], conjecture80Over K

private def HiddenCenter (K : Type) := Fin 4 → K

private instance hiddenCenterAddCommGroup : AddCommGroup (HiddenCenter K) :=
  inferInstanceAs (AddCommGroup (Fin 4 → K))

private instance hiddenCenterModule : Module K (HiddenCenter K) :=
  inferInstanceAs (Module K (Fin 4 → K))

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Cross.lieRing

private instance crossLieAlgebra : LieAlgebra K (Fin 3 → K) where
  lie_smul t x y := by
    rw [show ⁅x, y⁆ = x ⨯₃ y from rfl]
    exact (crossProduct x).map_smul t y

private def hiddenToFun (u : HiddenCenter K) : (Fin 3 → K) × K :=
  (![u 0, u 1, u 2 + u 3], u 3)

private def hiddenInvFun (p : (Fin 3 → K) × K) : HiddenCenter K :=
  ![p.1 0, p.1 1, p.1 2 - p.2, p.2]

private def hiddenEquiv : HiddenCenter K ≃ₗ[K] ((Fin 3 → K) × K) where
  toFun := hiddenToFun
  invFun := hiddenInvFun
  left_inv u := by
    funext i
    fin_cases i <;> dsimp only [hiddenToFun, hiddenInvFun] <;> simp [Matrix.cons_val]
  right_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i <;> dsimp only [hiddenToFun, hiddenInvFun] <;> simp [Matrix.cons_val]
    · dsimp only [hiddenToFun, hiddenInvFun]; simp [Matrix.cons_val]
  map_add' x y := by
    apply Prod.ext
    · change ![(x + y) 0, (x + y) 1, (x + y) 2 + (x + y) 3] =
        ![x 0, x 1, x 2 + x 3] + ![y 0, y 1, y 2 + y 3]
      rw [Matrix.vec3_add]
      apply Matrix.vec3_eq
      · rfl
      · rfl
      · change (x 2 + y 2) + (x 3 + y 3) = x 2 + x 3 + (y 2 + y 3)
        ring
    · change (hiddenToFun (x + y)).2 = (hiddenToFun x + hiddenToFun y).2
      change (x + y) 3 = x 3 + y 3
      exact Pi.add_apply x y 3
  map_smul' t x := by
    apply Prod.ext
    · change ![(t • x) 0, (t • x) 1, (t • x) 2 + (t • x) 3] =
        t • ![x 0, x 1, x 2 + x 3]
      rw [Matrix.smul_vec3]
      apply Matrix.vec3_eq
      · rfl
      · rfl
      · change t * x 2 + t * x 3 = t * (x 2 + x 3)
        ring
    · change (hiddenToFun (t • x)).2 = (t • hiddenToFun x).2
      change (t • x) 3 = t * x 3
      exact Pi.smul_apply t x 3

private instance hiddenCenterLieRing : LieRing (HiddenCenter K) :=
  AddEquiv.lieRing (L := (Fin 3 → K) × K)
    (hiddenEquiv (K := K)).toAddEquiv

private instance hiddenCenterLieAlgebra : LieAlgebra K (HiddenCenter K) :=
  LinearEquiv.lieAlgebra (L := (Fin 3 → K) × K) (hiddenEquiv (K := K))

private def hiddenBasis : Basis (Fin 4) K (HiddenCenter K) :=
  Pi.basisFun K (Fin 4)

private theorem hiddenBasis_zero : hiddenBasis (K := K) 0 = ![(1 : K), 0, 0, 0] := by
  classical
  funext i
  change (Pi.basisFun K (Fin 4) 0 : Fin 4 → K) i = _
  rw [Pi.basisFun_apply]
  fin_cases i <;> simp [Matrix.cons_val]

private theorem hiddenBasis_one : hiddenBasis (K := K) 1 = ![(0 : K), 1, 0, 0] := by
  classical
  funext i
  change (Pi.basisFun K (Fin 4) 1 : Fin 4 → K) i = _
  rw [Pi.basisFun_apply]
  fin_cases i <;> simp [Matrix.cons_val]

private theorem hiddenBasis_two : hiddenBasis (K := K) 2 = ![(0 : K), 0, 1, 0] := by
  classical
  funext i
  change (Pi.basisFun K (Fin 4) 2 : Fin 4 → K) i = _
  rw [Pi.basisFun_apply]
  fin_cases i <;> simp [Matrix.cons_val]

private theorem hiddenBasis_three : hiddenBasis (K := K) 3 = ![(0 : K), 0, 0, 1] := by
  classical
  funext i
  change (Pi.basisFun K (Fin 4) 3 : Fin 4 → K) i = _
  rw [Pi.basisFun_apply]
  fin_cases i <;> simp [Matrix.cons_val]

private theorem hidden_neg_basis_one_three :
    (-hiddenBasis (K := K) 1 : HiddenCenter K) 3 = 0 := by
  rw [hiddenBasis_one]
  change -((![0, 1, 0, 0] : Fin 4 → K) 3) = 0
  simp [Matrix.cons_val]

private theorem hidden_neg_basis_zero_three :
    (-hiddenBasis (K := K) 0 : HiddenCenter K) 3 = 0 := by
  rw [hiddenBasis_zero]
  change -((![1, 0, 0, 0] : Fin 4 → K) 3) = 0
  simp [Matrix.cons_val]

private theorem hidden_basis_brackets :
    (⁅hiddenBasis (K := K) 0, hiddenBasis (K := K) 1⁆ = hiddenBasis (K := K) 2) ∧
    (⁅hiddenBasis (K := K) 1, hiddenBasis (K := K) 2⁆ = hiddenBasis (K := K) 0) ∧
    (⁅hiddenBasis (K := K) 2, hiddenBasis (K := K) 0⁆ = hiddenBasis (K := K) 1) ∧
    (⁅hiddenBasis (K := K) 0, hiddenBasis (K := K) 3⁆ = -hiddenBasis (K := K) 1) ∧
    (⁅hiddenBasis (K := K) 1, hiddenBasis (K := K) 3⁆ = hiddenBasis (K := K) 0) ∧
    (⁅hiddenBasis (K := K) 3, hiddenBasis (K := K) 0⁆ = hiddenBasis (K := K) 1) ∧
    (⁅hiddenBasis (K := K) 3, hiddenBasis (K := K) 1⁆ = -hiddenBasis (K := K) 0) := by
  constructor
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 0), hiddenToFun (hiddenBasis (K := K) 1)⁆ =
      hiddenToFun (hiddenBasis (K := K) 2)
    apply Prod.ext
    · change (hiddenToFun (hiddenBasis (K := K) 0)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 1)).1 = (hiddenToFun (hiddenBasis (K := K) 2)).1
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_two, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 0)).2 *
          (hiddenToFun (hiddenBasis (K := K) 1)).2 -
          (hiddenToFun (hiddenBasis (K := K) 1)).2 *
            (hiddenToFun (hiddenBasis (K := K) 0)).2 =
        (hiddenToFun (hiddenBasis (K := K) 2)).2
      dsimp only [hiddenToFun]; simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_two, Matrix.cons_val]
  constructor
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 1), hiddenToFun (hiddenBasis (K := K) 2)⁆ =
      hiddenToFun (hiddenBasis (K := K) 0)
    apply Prod.ext
    · change (hiddenToFun (hiddenBasis (K := K) 1)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 2)).1 = (hiddenToFun (hiddenBasis (K := K) 0)).1
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_two, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 1)).2 * (hiddenToFun (hiddenBasis (K := K) 2)).2 -
          (hiddenToFun (hiddenBasis (K := K) 2)).2 * (hiddenToFun (hiddenBasis (K := K) 1)).2 =
        (hiddenToFun (hiddenBasis (K := K) 0)).2
      dsimp only [hiddenToFun]; simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_two, Matrix.cons_val]
  constructor
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 2), hiddenToFun (hiddenBasis (K := K) 0)⁆ =
      hiddenToFun (hiddenBasis (K := K) 1)
    apply Prod.ext
    · change (hiddenToFun (hiddenBasis (K := K) 2)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 0)).1 = (hiddenToFun (hiddenBasis (K := K) 1)).1
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_two, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 2)).2 * (hiddenToFun (hiddenBasis (K := K) 0)).2 -
          (hiddenToFun (hiddenBasis (K := K) 0)).2 * (hiddenToFun (hiddenBasis (K := K) 2)).2 =
        (hiddenToFun (hiddenBasis (K := K) 1)).2
      dsimp only [hiddenToFun]; simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_two]
  constructor
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 0), hiddenToFun (hiddenBasis (K := K) 3)⁆ =
      hiddenToFun (-hiddenBasis (K := K) 1)
    have hneg := (hiddenEquiv (K := K)).map_neg (hiddenBasis (K := K) 1)
    change hiddenToFun (-hiddenBasis (K := K) 1) = -hiddenToFun (hiddenBasis (K := K) 1) at hneg
    apply Prod.ext
    · rw [hneg]
      change (hiddenToFun (hiddenBasis (K := K) 0)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 3)).1 = -(hiddenToFun (hiddenBasis (K := K) 1)).1
      rw [show -(hiddenToFun (hiddenBasis (K := K) 1)).1 = ![(0 : K), -1, 0] by
        dsimp only [hiddenToFun]; simp [hiddenBasis_one, Matrix.cons_val]]
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_zero, hiddenBasis_three, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 0)).2 * (hiddenToFun (hiddenBasis (K := K) 3)).2 -
          (hiddenToFun (hiddenBasis (K := K) 3)).2 * (hiddenToFun (hiddenBasis (K := K) 0)).2 =
        (hiddenToFun (-hiddenBasis (K := K) 1)).2
      change (hiddenToFun (hiddenBasis (K := K) 0)).2 *
          (hiddenToFun (hiddenBasis (K := K) 3)).2 -
          (hiddenToFun (hiddenBasis (K := K) 3)).2 *
            (hiddenToFun (hiddenBasis (K := K) 0)).2 =
        (-hiddenBasis (K := K) 1 : HiddenCenter K) 3
      rw [hidden_neg_basis_one_three]
      dsimp only [hiddenToFun]; simp [hiddenBasis_zero, hiddenBasis_three]
  constructor
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 1), hiddenToFun (hiddenBasis (K := K) 3)⁆ =
      hiddenToFun (hiddenBasis (K := K) 0)
    apply Prod.ext
    · change (hiddenToFun (hiddenBasis (K := K) 1)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 3)).1 = (hiddenToFun (hiddenBasis (K := K) 0)).1
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_three, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 1)).2 * (hiddenToFun (hiddenBasis (K := K) 3)).2 -
          (hiddenToFun (hiddenBasis (K := K) 3)).2 * (hiddenToFun (hiddenBasis (K := K) 1)).2 =
        (hiddenToFun (hiddenBasis (K := K) 0)).2
      dsimp only [hiddenToFun]; simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_three]
  constructor
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 3), hiddenToFun (hiddenBasis (K := K) 0)⁆ =
      hiddenToFun (hiddenBasis (K := K) 1)
    apply Prod.ext
    · change (hiddenToFun (hiddenBasis (K := K) 3)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 0)).1 = (hiddenToFun (hiddenBasis (K := K) 1)).1
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_three, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 3)).2 * (hiddenToFun (hiddenBasis (K := K) 0)).2 -
          (hiddenToFun (hiddenBasis (K := K) 0)).2 * (hiddenToFun (hiddenBasis (K := K) 3)).2 =
        (hiddenToFun (hiddenBasis (K := K) 1)).2
      dsimp only [hiddenToFun]; simp [hiddenBasis_zero, hiddenBasis_one, hiddenBasis_three]
  · apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    change ⁅hiddenToFun (hiddenBasis (K := K) 3), hiddenToFun (hiddenBasis (K := K) 1)⁆ =
      hiddenToFun (-hiddenBasis (K := K) 0)
    have hneg := (hiddenEquiv (K := K)).map_neg (hiddenBasis (K := K) 0)
    change hiddenToFun (-hiddenBasis (K := K) 0) = -hiddenToFun (hiddenBasis (K := K) 0) at hneg
    apply Prod.ext
    · rw [hneg]
      change (hiddenToFun (hiddenBasis (K := K) 3)).1 ⨯₃
          (hiddenToFun (hiddenBasis (K := K) 1)).1 = -(hiddenToFun (hiddenBasis (K := K) 0)).1
      rw [show -(hiddenToFun (hiddenBasis (K := K) 0)).1 = ![(-1 : K), 0, 0] by
        dsimp only [hiddenToFun]; simp [hiddenBasis_zero, Matrix.cons_val]]
      rw [cross_apply]
      apply Matrix.vec3_eq <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_one, hiddenBasis_three, Matrix.cons_val]
    · change (hiddenToFun (hiddenBasis (K := K) 3)).2 * (hiddenToFun (K := K) (hiddenBasis (K := K) 1)).2 -
          (hiddenToFun (hiddenBasis (K := K) 1)).2 * (hiddenToFun (hiddenBasis (K := K) 3)).2 =
        (hiddenToFun (-hiddenBasis (K := K) 0)).2
      change (hiddenToFun (hiddenBasis (K := K) 3)).2 *
          (hiddenToFun (hiddenBasis (K := K) 1)).2 -
          (hiddenToFun (hiddenBasis (K := K) 1)).2 *
            (hiddenToFun (hiddenBasis (K := K) 3)).2 =
        (-hiddenBasis (K := K) 0 : HiddenCenter K) 3
      rw [hidden_neg_basis_zero_three]
      dsimp only [hiddenToFun]; simp [hiddenBasis_one, hiddenBasis_three]

private theorem hidden_basis_bracket_23 :
    ⁅hiddenBasis (K := K) 2, hiddenBasis (K := K) 3⁆ = 0 := by
  apply (hiddenEquiv (K := K)).injective
  rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
  change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
  simp only [LinearEquiv.apply_symm_apply, map_zero]
  change ⁅hiddenToFun (hiddenBasis (K := K) 2), hiddenToFun (hiddenBasis (K := K) 3)⁆ = 0
  apply Prod.ext
  · change (hiddenToFun (hiddenBasis (K := K) 2)).1 ⨯₃
        (hiddenToFun (hiddenBasis (K := K) 3)).1 = 0
    rw [cross_apply]
    funext i
    fin_cases i <;> dsimp only [hiddenToFun] <;> simp [hiddenBasis_two, hiddenBasis_three, Matrix.cons_val]
  · change (hiddenToFun (hiddenBasis (K := K) 2)).2 *
        (hiddenToFun (hiddenBasis (K := K) 3)).2 -
        (hiddenToFun (hiddenBasis (K := K) 3)).2 *
          (hiddenToFun (hiddenBasis (K := K) 2)).2 = 0
    dsimp only [hiddenToFun]; simp [hiddenBasis_two, hiddenBasis_three]

private theorem hidden_basis_bracket_32 :
    ⁅hiddenBasis (K := K) 3, hiddenBasis (K := K) 2⁆ = 0 := by
  calc
        ⁅hiddenBasis (K := K) 3, hiddenBasis (K := K) 2⁆ =
        -⁅hiddenBasis (K := K) 2, hiddenBasis (K := K) 3⁆ := (lie_skew _ _).symm
    _ = 0 := by rw [hidden_basis_bracket_23, neg_zero]

private theorem hiddenBasis_admissible : IsAdmissible (hiddenBasis (K := K)) := by
  let α : Fin 4 → Fin 4 → K :=
    ![![0, 1, -1, -1], ![-1, 0, 1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]
  let δ : Fin 4 → Fin 4 → Option (Fin 4) :=
    ![![none, some 2, some 1, some 1],
      ![some 2, none, some 0, some 0],
      ![some 1, some 0, none, none],
      ![some 1, some 0, none, none]]
  refine ⟨α, δ, ?_, ?_, ?_, ?_⟩
  · intro j k
    fin_cases j <;> fin_cases k <;> simp [α, Matrix.cons_val]
  · intro j k
    fin_cases j <;> fin_cases k <;> rfl
  · intro j k
    fin_cases j <;> fin_cases k <;> simp [α, δ, Matrix.cons_val]
  · intro j k
    rcases hidden_basis_brackets (K := K) with ⟨h01, h12, h20, h03, h13, h30, h31⟩
    have h02 : ⁅hiddenBasis (K := K) 0, hiddenBasis (K := K) 2⁆ =
        -hiddenBasis (K := K) 1 := by
      calc
        ⁅hiddenBasis (K := K) 0, hiddenBasis (K := K) 2⁆ =
            -⁅hiddenBasis (K := K) 2, hiddenBasis (K := K) 0⁆ := (lie_skew _ _).symm
        _ = -hiddenBasis (K := K) 1 := by rw [h20]
    have h10 : ⁅hiddenBasis (K := K) 1, hiddenBasis (K := K) 0⁆ =
        -hiddenBasis (K := K) 2 := by
      calc
        ⁅hiddenBasis (K := K) 1, hiddenBasis (K := K) 0⁆ =
            -⁅hiddenBasis (K := K) 0, hiddenBasis (K := K) 1⁆ := (lie_skew _ _).symm
        _ = -hiddenBasis (K := K) 2 := by rw [h01]
    have h21 : ⁅hiddenBasis (K := K) 2, hiddenBasis (K := K) 1⁆ =
        -hiddenBasis (K := K) 0 := by
      calc
        ⁅hiddenBasis (K := K) 2, hiddenBasis (K := K) 1⁆ =
            -⁅hiddenBasis (K := K) 1, hiddenBasis (K := K) 2⁆ := (lie_skew _ _).symm
        _ = -hiddenBasis (K := K) 0 := by rw [h12]
    fin_cases j <;> fin_cases k
    · simp [α, δ]
    · simpa [α, δ, Matrix.cons_val] using h01
    · simpa [α, δ, Matrix.cons_val] using h02
    · simpa [α, δ, Matrix.cons_val] using h03
    · simpa [α, δ, Matrix.cons_val] using h10
    · simp [α, δ]
    · simpa [α, δ, Matrix.cons_val] using h12
    · simpa [α, δ, Matrix.cons_val] using h13
    · simpa [α, δ, Matrix.cons_val] using h20
    · simpa [α, δ, Matrix.cons_val] using h21
    · simp [α, δ, Matrix.cons_val]
    · simpa [α, δ, Matrix.cons_val] using hidden_basis_bracket_23 (K := K)
    · simpa [α, δ, Matrix.cons_val] using h30
    · simpa [α, δ, Matrix.cons_val] using h31
    · simpa [α, δ, Matrix.cons_val] using hidden_basis_bracket_32 (K := K)
    · simp [α, δ, Matrix.cons_val]

private theorem hidden_center_nonzero : LieAlgebra.center K (HiddenCenter K) ≠ ⊥ := by
  intro hz
  let z : HiddenCenter K := ![0, 0, -1, 1]
  have hmem : z ∈ LieAlgebra.center K (HiddenCenter K) := by
    apply (LieModule.mem_maxTrivSubmodule K (HiddenCenter K) (HiddenCenter K) _).mpr
    intro x
    apply (hiddenEquiv (K := K)).injective
    rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
    change hiddenEquiv ((hiddenEquiv (K := K)).symm _) = _
    simp only [LinearEquiv.apply_symm_apply, map_zero]
    change ⁅hiddenToFun x, hiddenToFun z⁆ = 0
    apply Prod.ext
    · change (hiddenToFun x).1 ⨯₃ (hiddenToFun z).1 = 0
      rw [cross_apply]
      funext i
      fin_cases i <;> dsimp only [hiddenToFun] <;> simp [z, Matrix.cons_val]
    · change (hiddenToFun x).2 * (hiddenToFun z).2 -
          (hiddenToFun z).2 * (hiddenToFun x).2 = 0
      dsimp only [hiddenToFun]; simp [z, Matrix.cons_val]
  have hbotmem : z ∈ (⊥ : LieIdeal K (HiddenCenter K)) :=
    hz ▸ hmem
  have hbot : z = 0 := by
    change z = 0 at hbotmem
    exact hbotmem
  have hc := congrArg (fun x : HiddenCenter K => x 3) hbot
  change z 3 = 0 at hc
  simp [z, Matrix.cons_val] at hc

private def hiddenIdeal : LieIdeal K (HiddenCenter K) :=
  { toSubmodule := Submodule.comap (LinearMap.proj (R := K) (φ := fun _ : Fin 4 => K) 3) (⊥ : Submodule K K)
    lie_mem := by
      intro x y hy
      change (⁅x, y⁆ : HiddenCenter K) 3 = 0
      rw [AddEquiv.bracket_def (hiddenEquiv (K := K)).toAddEquiv]
      have h := (hiddenEquiv (K := K)).apply_symm_apply
        ⁅hiddenEquiv x, hiddenEquiv y⁆
      change (hiddenToFun ((hiddenEquiv (K := K)).symm
        ⁅hiddenEquiv x, hiddenEquiv y⁆)).2 = 0
      rw [show (hiddenToFun ((hiddenEquiv (K := K)).symm
          ⁅hiddenEquiv x, hiddenEquiv y⁆)).2 =
          (⁅hiddenEquiv x, hiddenEquiv y⁆ : (Fin 3 → K) × K).2 by
        exact congrArg Prod.snd h]
      change (hiddenEquiv x).2 * (hiddenEquiv y).2 -
          (hiddenEquiv y).2 * (hiddenEquiv x).2 = 0
      ring }

private theorem hiddenIdeal_mem (x : HiddenCenter K) :
    x ∈ hiddenIdeal (K := K) ↔ x 3 = 0 := by
  change (LinearMap.proj (R := K) (φ := fun _ : Fin 4 => K) 3 x ∈ (⊥ : Submodule K K)) ↔ x 3 = 0
  change x 3 = 0 ↔ x 3 = 0
  rfl

private theorem hiddenIdeal_span :
    (hiddenIdeal (K := K) : Submodule K (HiddenCenter K)) =
      Submodule.span K (hiddenBasis (K := K) '' ({0, 1, 2} : Set (Fin 4))) := by
  ext x
  change x ∈ hiddenIdeal (K := K) ↔ _
  rw [hiddenIdeal_mem]
  change Fin 4 → K at x
  change x 3 = 0 ↔ x ∈ Pi.spanSubset K ({0, 1, 2} : Set (Fin 4))
  rw [Pi.mem_spanSubset_iff]
  constructor
  · intro h i hi
    fin_cases i <;> simp_all
  · intro h
    exact h 3 (by simp)

private theorem hidden_edge_01 : Edge (hiddenBasis (K := K)) 0 1 2 := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa using (hidden_basis_brackets (K := K)).1

private theorem hidden_edge_12 : Edge (hiddenBasis (K := K)) 1 2 0 := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa using (hidden_basis_brackets (K := K)).2.1

private theorem hidden_edge_20 : Edge (hiddenBasis (K := K)) 2 0 1 := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa using (hidden_basis_brackets (K := K)).2.2.1

private theorem hidden_edge_30 : Edge (hiddenBasis (K := K)) 3 0 1 := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa using (hidden_basis_brackets (K := K)).2.2.2.2.2.1

private theorem hidden_edge_31 : Edge (hiddenBasis (K := K)) 3 1 0 := by
  refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
  simpa [smul_eq_mul] using (hidden_basis_brackets (K := K)).2.2.2.2.2.2

private theorem hidden_graph_classification {W : Set (Fin 4)}
    (hne : W.Nonempty) (hproper : W ≠ Set.univ)
    (hgraph : IdealGraphProperty (hiddenBasis (K := K)) W) :
    W = ({0, 1, 2} : Set (Fin 4)) := by
  obtain ⟨i, hi⟩ := hne
  have h012 : (0 : Fin 4) ∈ W ∧ (1 : Fin 4) ∈ W ∧ (2 : Fin 4) ∈ W := by
    fin_cases i
    · have h2 := hgraph _ _ _ hidden_edge_01 hi
      have h1 := hgraph _ _ _ hidden_edge_20 h2
      exact ⟨hi, h1, h2⟩
    · have h0 := hgraph _ _ _ hidden_edge_12 hi
      exact ⟨h0, hi, hgraph _ _ _ hidden_edge_01 h0⟩
    · have h1 := hgraph _ _ _ hidden_edge_20 hi
      exact ⟨hgraph _ _ _ hidden_edge_12 h1, h1, hi⟩
    · have h0 := hgraph _ _ _ hidden_edge_30 hi
      have h1 := hgraph _ _ _ hidden_edge_31 hi
      exact ⟨h1, h0, hgraph _ _ _ hidden_edge_01 h1⟩
  have h3 : (3 : Fin 4) ∉ W := by
    intro h3
    apply hproper
    ext i
    fin_cases i
    · simp [h012.1]
    · simp [h012.2.1]
    · simp [h012.2.2]
    · simp [h3]
  ext i
  fin_cases i <;> simp [h012.1, h012.2.1, h012.2.2, h3]

private theorem hiddenIdeal_not_solvable :
    ¬ LieAlgebra.IsSolvable (hiddenIdeal (K := K)) := by
  let i0 : hiddenIdeal (K := K) :=
    ⟨hiddenBasis (K := K) 0, by
      rw [hiddenIdeal_mem]
      simp [hiddenBasis_zero, Matrix.cons_val]⟩
  let i1 : hiddenIdeal (K := K) :=
    ⟨hiddenBasis (K := K) 1, by
      rw [hiddenIdeal_mem]
      simp [hiddenBasis_one, Matrix.cons_val]⟩
  let i2 : hiddenIdeal (K := K) :=
    ⟨hiddenBasis (K := K) 2, by
      rw [hiddenIdeal_mem]
      simp [hiddenBasis_two, Matrix.cons_val]⟩
  have hi0 : i0 ∈ (LieAlgebra.derivedSeries K (hiddenIdeal (K := K)) 1 :
      Submodule K (hiddenIdeal (K := K))) := by
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.subset_span
    refine ⟨i1, i2, ?_⟩
    apply Subtype.ext
    simpa [i0, i1, i2] using (hidden_basis_brackets (K := K)).2.1
  have hi1 : i1 ∈ (LieAlgebra.derivedSeries K (hiddenIdeal (K := K)) 1 :
      Submodule K (hiddenIdeal (K := K))) := by
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.subset_span
    refine ⟨i2, i0, ?_⟩
    apply Subtype.ext
    simpa [i0, i1, i2] using (hidden_basis_brackets (K := K)).2.2.1
  have hi2 : i2 ∈ (LieAlgebra.derivedSeries K (hiddenIdeal (K := K)) 1 :
      Submodule K (hiddenIdeal (K := K))) := by
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.subset_span
    refine ⟨i0, i1, ?_⟩
    apply Subtype.ext
    simpa [i0, i1, i2] using (hidden_basis_brackets (K := K)).1
  have hperfect : LieAlgebra.derivedSeries K (hiddenIdeal (K := K)) 1 = ⊤ := by
    apply top_unique
    intro x hx
    have hx3 : (x : HiddenCenter K) 3 = 0 :=
      (hiddenIdeal_mem (K := K) (x : HiddenCenter K)).mp x.property
    have hdecomp : (x : HiddenCenter K) =
        (x : HiddenCenter K) 0 • hiddenBasis (K := K) 0 +
          (x : HiddenCenter K) 1 • hiddenBasis (K := K) 1 +
            (x : HiddenCenter K) 2 • hiddenBasis (K := K) 2 := by
      let y : Fin 4 → K := (x : HiddenCenter K)
      have hy3 : y 3 = 0 := hx3
      have h := (Pi.basisFun K (Fin 4)).sum_repr y
      change y = y 0 • Pi.basisFun K (Fin 4) 0 + y 1 • Pi.basisFun K (Fin 4) 1 +
        y 2 • Pi.basisFun K (Fin 4) 2
      simpa [Fin.sum_univ_succ, Pi.basisFun_repr, hy3, add_assoc] using h.symm
    rw [show x = (x : HiddenCenter K) 0 • i0 +
        (x : HiddenCenter K) 1 • i1 + (x : HiddenCenter K) 2 • i2 by
      apply Subtype.ext
      simpa [i0, i1, i2] using hdecomp]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hi0) (Submodule.smul_mem _ _ hi1))
      (Submodule.smul_mem _ _ hi2)
  intro hsolv
  obtain ⟨n, hn⟩ := (LieAlgebra.isSolvable_iff K (hiddenIdeal (K := K))).mp hsolv
  rw [LieIdeal.derivedSeries_eq_top n hperfect] at hn
  have htopbot : (⊤ : LieIdeal K (hiddenIdeal (K := K))) = ⊥ := by
    exact hn
  have hi0bot : i0 ∈ (⊥ : LieIdeal K (hiddenIdeal (K := K))) := by
    rw [← htopbot]
    trivial
  have hi0zero : (i0 : hiddenIdeal (K := K)) = 0 := hi0bot
  have hc := congrArg (fun x : hiddenIdeal (K := K) => (x : HiddenCenter K) 0) hi0zero
  have hzero : ((0 : HiddenCenter K) : Fin 4 → K) 0 = (0 : K) := by rfl
  have h10 : (1 : K) = 0 := by
    simpa [i0, hiddenBasis_zero, Matrix.cons_val] using hc.trans hzero
  exact (one_ne_zero : (1 : K) ≠ 0) h10

private theorem conjecture_fails (K : Type) [Field K] : ¬ conjecture80Over K := by
  intro hc
  obtain ⟨W, hne, hproper, hgraph, I, hIspan, hIsolv⟩ :=
    hc (HiddenCenter K) 4 (hiddenBasis (K := K))
      (hiddenBasis_admissible (K := K)) (hidden_center_nonzero (K := K))
  have hW := hidden_graph_classification hne hproper hgraph
  have hIeq : I = hiddenIdeal (K := K) := by
    apply LieSubmodule.toSubmodule_injective
    exact hIspan.trans (by rw [hW]; exact (hiddenIdeal_span (K := K)).symm)
  rw [hIeq] at hIsolv
  exact (hiddenIdeal_not_solvable (K := K)) hIsolv

theorem result : ¬ claim := by
  intro h
  exact conjecture_fails ℚ (h ℚ)

end D5.S3.Quantum.Algebra.HeibBruschiHiddenCenterRefutation
