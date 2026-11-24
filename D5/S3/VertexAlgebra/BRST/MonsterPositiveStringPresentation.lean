/- GID: D5/S3/VertexAlgebra/BRST/MonsterPositiveStringPresentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/MonsterPositiveStringPresentation
   mirror-E: none(waiver:algebraic-positive-presentation)
   anchors: []
   utility: none
   digest: The positive Monster semidirect decomposition and its rank-two grading and support. -/

import D5.S3.VertexAlgebra.BRST.MonsterPositiveCocycle
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
Borcherds, *Monstrous moonshine and monstrous Lie superalgebras* (1992), gives the Monster
presentation. Jurisich, *Generalized Kac–Moody Lie algebras, free Lie algebras and the structure
of the Monster Lie algebra* (1998), Corollary 5.1 and Theorem 5.2, gives the free Lie structure.
The two explicit universal-property maps follow §2 of the direct-presentation derivation
dated 2026-11-24. We use paper weights `(m,n)`, corresponding to native charges `(m,-n)`.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.MonsterPositiveStringPresentation

open MonsterPositiveCocycle
open LieAlgebra LieAlgebra.SemiDirectSum
open scoped TensorProduct

private theorem map_adIter {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [LieRing M] [LieAlgebra ℝ M] (f : L →ₗ⁅ℝ⁆ M) (e y : L) (k : ℕ) :
    f (adIter e k y) = adIter (f e) k (f y) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [adIter, adIter, LieHom.map_lie, ih]

/-- A derivation of a free Lie algebra, lifted through the split extension by its
abelian adjoint module. -/
private def freeDerivation {X : Type*} (v : X → FreeLieAlgebra ℝ X) :
    LieDerivation ℝ (FreeLieAlgebra ℝ X) (FreeLieAlgebra ℝ X) := by
  let A := FreeLieAlgebra ℝ X
  let c : LieModule.Cohomology.twoCocycle ℝ A A := 0
  let F : A →ₗ⁅ℝ⁆ LieAlgebra.ofTwoCocycle c :=
    FreeLieAlgebra.lift ℝ fun w => ⟨(FreeLieAlgebra.of ℝ w, v w)⟩
  let proj : LieAlgebra.ofTwoCocycle c →ₗ⁅ℝ⁆ A :=
    { toFun := fun x => x.carrier.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := fun {_ _} => rfl }
  have hproj : proj.comp F = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro w
    change (F (FreeLieAlgebra.of ℝ w)).carrier.1 = _
    rw [show F (FreeLieAlgebra.of ℝ w) = ⟨(FreeLieAlgebra.of ℝ w, v w)⟩ from
      FreeLieAlgebra.lift_of_apply _ _]
    rfl
  have hfirst (x : A) : (F x).carrier.1 = x := DFunLike.congr_fun hproj x
  exact
    { toFun := fun x => (F x).carrier.2
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun t x => by rw [map_smul]; rfl
      leibniz' := fun x y => by
        change (F ⁅x, y⁆).carrier.2 = ⁅x, (F y).carrier.2⁆ - ⁅y, (F x).carrier.2⁆
        rw [LieHom.map_lie, LieAlgebra.bracket_ofTwoCocycle]
        change (c : A →ₗ[ℝ] A →ₗ[ℝ] A) (F x).carrier.1 (F y).carrier.1 +
          ⁅(F x).carrier.1, (F y).carrier.2⁆ - ⁅(F y).carrier.1, (F x).carrier.2⁆ = _
        simp [c, hfirst] }

@[simp] private theorem freeDerivation_of {X : Type*} (v : X → FreeLieAlgebra ℝ X) (w : X) :
    freeDerivation v (FreeLieAlgebra.of ℝ w) = v w := by
  change ((FreeLieAlgebra.lift ℝ (fun w =>
    (⟨(FreeLieAlgebra.of ℝ w, v w)⟩ : LieAlgebra.ofTwoCocycle
      (0 : LieModule.Cohomology.twoCocycle ℝ (FreeLieAlgebra ℝ X) (FreeLieAlgebra ℝ X)))))
      (FreeLieAlgebra.of ℝ w)).carrier.2 = _
  rw [FreeLieAlgebra.lift_of_apply]

private theorem free_lieSpan_eq_top {X : Type*} :
    LieSubalgebra.lieSpan ℝ (FreeLieAlgebra ℝ X) (Set.range (FreeLieAlgebra.of ℝ)) = ⊤ := by
  let S := LieSubalgebra.lieSpan ℝ (FreeLieAlgebra ℝ X) (Set.range (FreeLieAlgebra.of ℝ))
  let f : FreeLieAlgebra ℝ X →ₗ⁅ℝ⁆ S :=
    FreeLieAlgebra.lift ℝ fun w => ⟨FreeLieAlgebra.of ℝ w,
      LieSubalgebra.subset_lieSpan (Set.mem_range_self w)⟩
  have h : S.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro w
    change ((f (FreeLieAlgebra.of ℝ w) : S) : FreeLieAlgebra ℝ X) = _
    simp [f]
  apply top_unique
  intro x _
  have hx : (f x : FreeLieAlgebra ℝ X) = x := DFunLike.congr_fun h x
  exact hx ▸ (f x).property

variable {J : Type*} (order : J → ℕ+)

/-- One token for each depth of each imaginary simple-root string. -/
abbrev StringToken := Σ j : J, Fin (order j : ℕ)

/-- The ideal generated freely by the imaginary string tokens. -/
abbrev StringLie := FreeLieAlgebra ℝ (StringToken order)

local notation "A" => StringLie order
local notation "P" => PositivePresentation order

/-- Advance by one depth, with value zero at the end of the string. -/
def shift (w : StringToken order) : A :=
  if h : w.2.val + 1 < (order w.1 : ℕ) then
    FreeLieAlgebra.of ℝ ⟨w.1, ⟨w.2.val + 1, h⟩⟩
  else 0

/-- The real generator acts on the free string Lie algebra by this derivation. -/
def stringDerivation : LieDerivation ℝ A A := freeDerivation (shift order)

@[simp] theorem stringDerivation_of (w : StringToken order) :
    stringDerivation order (FreeLieAlgebra.of ℝ w) = shift order w :=
  freeDerivation_of _ _

/-- The abelian real line, with its own Lie algebra instance. -/
def RealLine := ℝ

/-- Read the real coordinate of the abelian Lie algebra. -/
def RealLine.toReal (x : RealLine) : ℝ := x

instance : AddCommGroup RealLine := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ RealLine := inferInstanceAs (Module ℝ ℝ)

instance : LieRing RealLine where
  bracket _ _ := 0
  add_lie _ _ _ := (zero_add 0).symm
  lie_add _ _ _ := (zero_add 0).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := (zero_add 0).symm

instance : LieAlgebra ℝ RealLine where
  lie_smul t _ _ := (smul_zero t).symm

/-- Scalar multiplication of the string derivation is the action of the real line. -/
def realAction : RealLine →ₗ⁅ℝ⁆ LieDerivation ℝ A A where
  toFun c := c.toReal • stringDerivation order
  map_add' x y := add_smul x.toReal y.toReal _
  map_smul' t c := mul_smul t c.toReal _
  map_lie' := by
    intro x y
    change (0 : ℝ) • stringDerivation order =
      ⁅x.toReal • stringDerivation order, y.toReal • stringDerivation order⁆
    rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero, zero_smul]

/-- The positive Monster model, with the free Lie algebra in the first coordinate. -/
abbrev StringSemidirect := A ⋊⁅realAction order⁆ RealLine

local notation "S" => StringSemidirect order

/-- The model's real generator. -/
def modelReal : S := ⟨0, (show RealLine from (1 : ℝ))⟩

/-- The token at depth zero. -/
def firstToken (j : J) : StringToken order := ⟨j, ⟨0, (order j).property⟩⟩

private theorem modelReal_bracket (x : A) :
    ⁅modelReal order, inl (realAction order) x⁆ =
      inl (realAction order) (stringDerivation order x) := by
  change (⟨⁅0, x⁆ + (1 : ℝ) • stringDerivation order x -
      realAction order 0 0, 0⟩ : S) = _
  simp

private theorem modelString (j : J) (k : ℕ) :
    adIter (modelReal order) k (inl (realAction order) (FreeLieAlgebra.of ℝ (firstToken order j))) =
      if h : k < (order j : ℕ) then inl (realAction order) (FreeLieAlgebra.of ℝ
        (⟨j, ⟨k, h⟩⟩ : StringToken order)) else 0 := by
  induction k with
  | zero => simp [adIter, firstToken]
  | succ k ih =>
    by_cases hk : k < (order j : ℕ)
    · simp only [adIter, ih, dite_eq_left hk, modelReal_bracket, stringDerivation_of, shift]
      split <;> simp_all
    · have hnext : ¬ k + 1 < (order j : ℕ) := by omega
      rw [adIter, ih, dite_eq_right hk, dite_eq_right hnext, lie_zero]

private theorem serre_relation (j : J) :
    adIter (generator order none) (order j : ℕ) (generator order (some j)) = 0 := by
  unfold generator
  rw [← map_adIter (presentationQuotient order)]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan (Set.mem_range_self j))

private def freeToModel : FreeLieAlgebra ℝ (Option J) →ₗ⁅ℝ⁆ S :=
  FreeLieAlgebra.lift ℝ fun
    | none => modelReal order
    | some j => inl (realAction order) (FreeLieAlgebra.of ℝ (firstToken order j))

private theorem serreIdeal_le_ker : serreIdeal order ≤ (freeToModel order).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro _ ⟨j, rfl⟩
  change freeToModel order (adIter (FreeLieAlgebra.of ℝ none) (order j : ℕ)
    (FreeLieAlgebra.of ℝ (some j))) = 0
  rw [map_adIter]
  simp only [freeToModel, FreeLieAlgebra.lift_of_apply, modelString, dite_eq_right (lt_irrefl _)]

/-- The universal map from the existing Serre quotient into the semidirect product. -/
def toModel : P →ₗ⁅ℝ⁆ S :=
  { (serreIdeal order).toSubmodule.liftQ (freeToModel order).toLinearMap
      (serreIdeal_le_ker order) with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => exact (freeToModel order).map_lie x y }

@[simp] theorem toModel_real : toModel order (generator order none) = modelReal order :=
  FreeLieAlgebra.lift_of_apply _ _

@[simp] theorem toModel_imaginary (j : J) :
    toModel order (generator order (some j)) =
      inl (realAction order) (FreeLieAlgebra.of ℝ (firstToken order j)) :=
  FreeLieAlgebra.lift_of_apply _ _

/-- Evaluate a free string token as the corresponding iterated adjoint in the quotient. -/
def stringMap : A →ₗ⁅ℝ⁆ P :=
  FreeLieAlgebra.lift ℝ fun w =>
    adIter (generator order none) w.2.val (generator order (some w.1))

@[simp] theorem stringMap_of (w : StringToken order) :
    stringMap order (FreeLieAlgebra.of ℝ w) =
      adIter (generator order none) w.2.val (generator order (some w.1)) :=
  FreeLieAlgebra.lift_of_apply _ _

/-- The action compatibility extends from tokens to the whole free Lie algebra. -/
theorem stringMap_derivation (x : A) :
    stringMap order (stringDerivation order x) =
      ⁅generator order none, stringMap order x⁆ := by
  have hx : x ∈ LieSubalgebra.lieSpan ℝ A (Set.range (FreeLieAlgebra.of ℝ)) := by
    rw [free_lieSpan_eq_top]
    trivial
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hx
    simp only [stringDerivation_of, shift, stringMap_of]
    split
    · rw [stringMap_of]
      rfl
    · rename_i h
      have hend : k.val.succ = (order j : ℕ) := by have := k.isLt; omega
      rw [map_zero, ← adIter, hend, serre_relation]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]
  | lie x y _ _ hx hy =>
    simp only [LieDerivation.apply_lie_eq_sub, map_sub, LieHom.map_lie, hx, hy]
    rw [leibniz_lie (generator order none) (stringMap order x) (stringMap order y),
      sub_eq_add_neg, lie_skew ⁅generator order none, stringMap order x⁆ (stringMap order y),
      add_comm]

private theorem fromModel_bracket (x y : S) :
    stringMap order (⁅x, y⁆ : S).left +
        (⁅x, y⁆ : S).right.toReal • generator order none =
      ⁅stringMap order x.left + x.right.toReal • generator order none,
        stringMap order y.left + y.right.toReal • generator order none⁆ := by
  change stringMap order (⁅x.left, y.left⁆ +
      x.right.toReal • stringDerivation order y.left -
      y.right.toReal • stringDerivation order x.left) +
      (0 : ℝ) • generator order none = _
  simp only [map_sub, map_add, map_smul, LieHom.map_lie, stringMap_derivation, zero_smul, add_zero,
    add_lie, lie_add, lie_smul, smul_lie, lie_self, smul_zero, add_zero]
  rw [← lie_skew (stringMap order x.left) (generator order none), smul_neg, sub_eq_add_neg]

/-- Assemble the string evaluation and the scalar multiple of the real generator. -/
def fromModel : S →ₗ⁅ℝ⁆ P where
  toFun x := stringMap order x.left + x.right.toReal • generator order none
  map_add' x y := by
    change stringMap order (x.left + y.left) +
      (x.right.toReal + y.right.toReal) • generator order none = _
    simp only [map_add, add_smul]
    abel
  map_smul' c x := by
    change stringMap order (c • x.left) +
      (c * x.right.toReal) • generator order none = _
    simp only [RingHom.id_apply, map_smul, mul_smul, smul_add]
  map_lie' := fun {x y} => fromModel_bracket order x y

@[simp] theorem fromModel_real : fromModel order (modelReal order) = generator order none := by
  change stringMap order 0 + (1 : ℝ) • generator order none = _
  simp

@[simp] theorem fromModel_inl (x : A) :
    fromModel order (inl (realAction order) x) = stringMap order x := by
  change stringMap order x + (0 : ℝ) • generator order none = _
  simp

private theorem fromModel_toModel (x : P) : fromModel order (toModel order x) = x := by
  have h : (fromModel order).comp ((toModel order).comp (presentationQuotient order)) =
      presentationQuotient order := by
    apply FreeLieAlgebra.hom_ext
    intro j
    change fromModel order (toModel order (generator order j)) = generator order j
    cases j with
    | none => simp
    | some j => rw [toModel_imaginary, fromModel_inl, stringMap_of]; rfl
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact DFunLike.congr_fun h x

private theorem toModel_stringMap (x : A) :
    toModel order (stringMap order x) = inl (realAction order) x := by
  have h : (toModel order).comp (stringMap order) = inl (realAction order) := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨j, k⟩
    change toModel order (stringMap order (FreeLieAlgebra.of ℝ
      (⟨j, k⟩ : StringToken order))) = _
    rw [stringMap_of, map_adIter, toModel_real, toModel_imaginary, modelString, dite_eq_left k.isLt]
  exact DFunLike.congr_fun h x

private theorem toModel_fromModel (x : S) : toModel order (fromModel order x) = x := by
  change toModel order (stringMap order x.left +
    x.right.toReal • generator order none) = x
  rw [map_add, map_smul, toModel_stringMap, toModel_real]
  apply LieAlgebra.SemiDirectSum.ext
  · change x.left + x.right.toReal • (0 : A) = x.left
    simp
  · change (0 : ℝ) + x.right.toReal * 1 = x.right.toReal
    simp

/-- The actual positive Serre quotient is the semidirect product of the free strings
by the abelian real line. Both inverse composites were checked on generators. -/
def presentationEquiv : P ≃ₗ⁅ℝ⁆ S :=
  { toModel order with
    invFun := fromModel order
    left_inv := fromModel_toModel order
    right_inv := toModel_fromModel order }

@[simp] theorem presentationEquiv_real :
    presentationEquiv order (generator order none) = modelReal order :=
  toModel_real order

@[simp] theorem presentationEquiv_imaginary (j : J) :
    presentationEquiv order (generator order (some j)) =
      inl (realAction order) (FreeLieAlgebra.of ℝ (firstToken order j)) :=
  toModel_imaginary order j

@[simp] theorem presentationEquiv_symm_token (w : StringToken order) :
    (presentationEquiv order).symm (inl (realAction order) (FreeLieAlgebra.of ℝ w)) =
      adIter (generator order none) w.2.val (generator order (some w.1)) := by
  change fromModel order (inl (realAction order) (FreeLieAlgebra.of ℝ w)) = _
  rw [fromModel_inl, stringMap_of]

theorem stringMap_injective : Function.Injective (stringMap order) := by
  intro x y h
  exact inl_injective (realAction order) (by
    rw [← toModel_stringMap, ← toModel_stringMap, h])

private def RealLine.toRealLinear : RealLine →ₗ[ℝ] ℝ where
  toFun := RealLine.toReal
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def imaginaryCoordinate (j : J) : A →ₗ⁅ℝ⁆ RealLine := by
  classical
  exact FreeLieAlgebra.lift ℝ fun w : StringToken order =>
    if w.1 = j then (show RealLine from (1 : ℝ)) else 0

private def generatorCoordinate (j : Option J) : P →ₗ[ℝ] ℝ :=
  RealLine.toRealLinear.comp
    ((match j with
     | none => (projr (realAction order)).toLinearMap
     | some i => (imaginaryCoordinate order i).toLinearMap.comp (projl (realAction order))).comp
       (toModel order).toLinearMap)

private theorem generatorCoordinate_apply [DecidableEq J] (j k : Option J) :
    generatorCoordinate order j (generator order k) = (if k = j then 1 else 0 : ℝ) := by
  classical
  cases j <;> cases k
  · change (toModel order (generator order none)).right.toReal = _
    rw [toModel_real]
    rfl
  · rename_i k
    change (toModel order (generator order (some k))).right.toReal = _
    rw [toModel_imaginary]
    rfl
  · rename_i j
    change (imaginaryCoordinate order j (toModel order (generator order none)).left).toReal = _
    rw [toModel_real]
    change (imaginaryCoordinate order j 0).toReal = _
    rw [map_zero]
    rfl
  · rename_i j k
    change (imaginaryCoordinate order j (toModel order (generator order (some k))).left).toReal = _
    rw [toModel_imaginary]
    change (imaginaryCoordinate order j (FreeLieAlgebra.of ℝ (firstToken order k))).toReal = _
    rw [imaginaryCoordinate, FreeLieAlgebra.lift_of_apply]
    by_cases h : k = j
    · simp [firstToken, h, RealLine.toReal]
    · simp [firstToken, h, RealLine.toReal]
      rfl

/-- The real and imaginary simple generators are linearly independent in the presentation. -/
theorem generator_linearIndependent : LinearIndependent ℝ (generator order) := by
  classical
  rw [linearIndependent_iff']
  intro s c h j hj
  have hc := congrArg (generatorCoordinate order j) h
  simp only [map_zero, map_sum, map_smul, generatorCoordinate_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', hj, ite_true] at hc
  exact hc

/-- The paper bidegree of a token, written as its initial weight plus its adjoint depth. -/
def tokenWeight (w : StringToken order) : Weight :=
  w.2.val • realRoot + imaginaryRoot (order w.1 : ℕ)

theorem tokenWeight_coordinates (w : StringToken order) :
    tokenWeight order w = ((w.2.val : ℤ) + 1, (order w.1 : ℕ) - (w.2.val : ℤ)) := by
  ext <;> simp [tokenWeight, realRoot, imaginaryRoot, sub_eq_add_neg, add_comm]

theorem tokenWeight_positive (w : StringToken order) :
    0 < (tokenWeight order w).1 ∧ 0 < (tokenWeight order w).2 := by
  rw [tokenWeight_coordinates]
  have := w.2.isLt
  constructor <;> dsimp <;> omega

private theorem tokenWeight_next (j : J) (k : ℕ) (h : k < (order j : ℕ))
    (hn : k + 1 < (order j : ℕ)) :
    tokenWeight order ⟨j, ⟨k + 1, hn⟩⟩ =
      realRoot + tokenWeight order ⟨j, ⟨k, h⟩⟩ := by
  change (k + 1) • realRoot + imaginaryRoot _ = realRoot + (k • realRoot + imaginaryRoot _)
  rw [succ_nsmul', add_assoc]

/-- A single real eigenvalue separates the lattice weights. -/
private def weightScalar : Weight →+ ℝ where
  toFun p := (p.1 : ℝ) + (p.2 : ℝ) * Real.sqrt 2
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

private theorem weightScalar_injective : Function.Injective weightScalar := by
  intro p q h
  change (p.1 : ℝ) + (p.2 : ℝ) * Real.sqrt 2 = (q.1 : ℝ) + (q.2 : ℝ) * Real.sqrt 2 at h
  have h₂ : p.2 = q.2 := by
    by_contra hne
    have hden : ((p.2 : ℝ) - (q.2 : ℝ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    apply irrational_sqrt_two.ne_rational (q.1 - p.1) (p.2 - q.2)
    push_cast
    apply (eq_div_iff hden).2
    linarith only [h]
  apply Prod.ext _ h₂
  rw [h₂, add_left_inj] at h
  exact_mod_cast h

private def stringEuler : LieDerivation ℝ A A :=
  freeDerivation fun w => weightScalar (tokenWeight order w) • FreeLieAlgebra.of ℝ w

private theorem stringEuler_of (w : StringToken order) :
    stringEuler order (FreeLieAlgebra.of ℝ w) =
      weightScalar (tokenWeight order w) • FreeLieAlgebra.of ℝ w :=
  freeDerivation_of _ _

private theorem stringEuler_shift (x : A) :
    stringEuler order (stringDerivation order x) =
      stringDerivation order (stringEuler order x) +
        weightScalar realRoot • stringDerivation order x := by
  have h : ⁅stringEuler order, stringDerivation order⁆ =
      weightScalar realRoot • stringDerivation order := by
    apply LieDerivation.ext_of_lieSpan_eq_top _ free_lieSpan_eq_top
    rintro _ ⟨⟨j, k⟩, rfl⟩
    change stringEuler order (stringDerivation order (FreeLieAlgebra.of ℝ ⟨j, k⟩)) -
      stringDerivation order (stringEuler order (FreeLieAlgebra.of ℝ ⟨j, k⟩)) =
      weightScalar realRoot • stringDerivation order (FreeLieAlgebra.of ℝ ⟨j, k⟩)
    rw [stringEuler_of, map_smul, stringDerivation_of, shift]
    split
    · rename_i hn
      rw [stringEuler_of, tokenWeight_next order j k.val k.isLt hn, map_add, add_smul,
        add_sub_cancel_right]
    · simp
  have hx := DFunLike.congr_fun h x
  change stringEuler order (stringDerivation order x) -
    stringDerivation order (stringEuler order x) =
    weightScalar realRoot • stringDerivation order x at hx
  exact (sub_eq_iff_eq_add.mp hx).trans (add_comm _ _)

private def modelEuler : LieDerivation ℝ S S where
  toFun x := ⟨stringEuler order x.left, weightScalar realRoot • x.right⟩
  map_add' x y := by
    apply LieAlgebra.SemiDirectSum.ext
    · exact map_add (stringEuler order) x.left y.left
    · exact smul_add (weightScalar realRoot) x.right y.right
  map_smul' t x := by
    apply LieAlgebra.SemiDirectSum.ext
    · exact map_smul (stringEuler order) t x.left
    · exact smul_comm (weightScalar realRoot) t x.right
  leibniz' x y := by
    apply LieAlgebra.SemiDirectSum.ext
    · change stringEuler order (⁅x.left, y.left⁆ +
          x.right.toReal • stringDerivation order y.left -
          y.right.toReal • stringDerivation order x.left) =
        (⁅x.left, stringEuler order y.left⁆ +
          x.right.toReal • stringDerivation order (stringEuler order y.left) -
          (weightScalar realRoot * y.right.toReal) • stringDerivation order x.left) -
        (⁅y.left, stringEuler order x.left⁆ +
          y.right.toReal • stringDerivation order (stringEuler order x.left) -
          (weightScalar realRoot * x.right.toReal) • stringDerivation order y.left)
      simp only [map_sub, map_add, map_smul, LieDerivation.apply_lie_eq_sub, stringEuler_shift,
        smul_add, mul_smul]
      rw [smul_comm x.right.toReal (weightScalar realRoot),
        smul_comm y.right.toReal (weightScalar realRoot)]
      abel
    · change weightScalar realRoot • (0 : RealLine) = 0 - 0
      simp

private def presentationEuler : LieDerivation ℝ P P where
  toLinearMap := (presentationEquiv order).toLinearEquiv.symm.toLinearMap.comp
    ((modelEuler order).toLinearMap.comp (presentationEquiv order).toLinearEquiv.toLinearMap)
  leibniz' x y := by
    change (presentationEquiv order).symm (modelEuler order (presentationEquiv order ⁅x, y⁆)) =
      ⁅x, (presentationEquiv order).symm (modelEuler order (presentationEquiv order y))⁆ -
        ⁅y, (presentationEquiv order).symm (modelEuler order (presentationEquiv order x))⁆
    apply (presentationEquiv order).injective
    simp only [LieEquiv.coe_toLieHom, LieEquiv.map_lie, map_sub, LieEquiv.apply_symm_apply,
      LieDerivation.apply_lie_eq_sub]

/-- The string grading by additive token weights. -/
def stringGrade (p : Weight) : Submodule ℝ A :=
  Module.End.eigenspace (stringEuler order).toLinearMap (weightScalar p)

/-- The grading of the actual Serre presentation in paper coordinates. -/
def presentationGrade (p : Weight) : Submodule ℝ P :=
  Module.End.eigenspace (presentationEuler order).toLinearMap (weightScalar p)

private theorem eigenspace_lie {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (D : LieDerivation ℝ L L) {p q : Weight} {x y : L}
    (hx : x ∈ Module.End.eigenspace D.toLinearMap (weightScalar p))
    (hy : y ∈ Module.End.eigenspace D.toLinearMap (weightScalar q)) :
    ⁅x, y⁆ ∈ Module.End.eigenspace D.toLinearMap (weightScalar (p + q)) := by
  rw [Module.End.mem_eigenspace_iff] at hx hy ⊢
  change D x = _ at hx
  change D y = _ at hy
  change D ⁅x, y⁆ = _
  rw [LieDerivation.apply_lie_eq_add, hx, hy, smul_lie, lie_smul, map_add, add_smul, add_comm]

theorem stringGrade_bracket {p q : Weight} {x y : A}
    (hx : x ∈ stringGrade order p) (hy : y ∈ stringGrade order q) :
    ⁅x, y⁆ ∈ stringGrade order (p + q) :=
  eigenspace_lie (stringEuler order) hx hy

theorem presentationGrade_bracket {p q : Weight} {x y : P}
    (hx : x ∈ presentationGrade order p) (hy : y ∈ presentationGrade order q) :
    ⁅x, y⁆ ∈ presentationGrade order (p + q) :=
  eigenspace_lie (presentationEuler order) hx hy

theorem token_mem_stringGrade (w : StringToken order) :
    FreeLieAlgebra.of ℝ w ∈ stringGrade order (tokenWeight order w) :=
  Module.End.mem_eigenspace_iff.mpr (stringEuler_of order w)

theorem real_mem_presentationGrade : generator order none ∈ presentationGrade order realRoot := by
  apply Module.End.mem_eigenspace_iff.mpr
  change (presentationEquiv order).symm (modelEuler order
    (presentationEquiv order (generator order none))) = _
  rw [presentationEquiv_real]
  have h : modelEuler order (modelReal order) = weightScalar realRoot • modelReal order := by
    apply LieAlgebra.SemiDirectSum.ext
    · change stringEuler order 0 = weightScalar realRoot • (0 : A)
      simp
    · rfl
  rw [h, map_smul, ← presentationEquiv_real, LieEquiv.symm_apply_apply]

theorem stringMap_mem_presentationGrade {p : Weight} {x : A} (hx : x ∈ stringGrade order p) :
    stringMap order x ∈ presentationGrade order p := by
  apply Module.End.mem_eigenspace_iff.mpr
  change (presentationEquiv order).symm (modelEuler order (toModel order (stringMap order x))) = _
  apply (presentationEquiv order).injective
  simp only [LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply, map_smul]
  change modelEuler order (toModel order (stringMap order x)) =
    weightScalar p • toModel order (stringMap order x)
  rw [toModel_stringMap]
  apply LieAlgebra.SemiDirectSum.ext
  · exact Module.End.mem_eigenspace_iff.mp hx
  · change weightScalar realRoot • (0 : RealLine) = weightScalar p • (0 : RealLine)
    simp

theorem imaginary_mem_presentationGrade (j : J) :
    generator order (some j) ∈ presentationGrade order (imaginaryRoot (order j : ℕ)) := by
  have h := stringMap_mem_presentationGrade order (token_mem_stringGrade order (firstToken order j))
  simpa only [stringMap_of, firstToken, adIter, tokenWeight, zero_nsmul, zero_add] using h

/-- Lie words contain at least one token, and their weights are computed by addition. -/
private inductive LieWord (X : Type*)
  | token (w : X)
  | bracket (x y : LieWord X)

private def LieWord.eval {X L : Type*} [Bracket L L] (f : X → L) : LieWord X → L
  | .token w => f w
  | .bracket x y => ⁅x.eval f, y.eval f⁆

private def LieWord.weight {X : Type*} (f : X → Weight) : LieWord X → Weight
  | .token w => f w
  | .bracket x y => x.weight f + y.weight f

private theorem lie_mem_span_words {X L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (f : X → L) {x y : L}
    (hx : x ∈ Submodule.span ℝ (Set.range (LieWord.eval f)))
    (hy : y ∈ Submodule.span ℝ (Set.range (LieWord.eval f))) :
    ⁅x, y⁆ ∈ Submodule.span ℝ (Set.range (LieWord.eval f)) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact Submodule.subset_span (Set.mem_range_self (LieWord.bracket u v))
  | zero_left => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left _ _ _ _ _ _ h₁ h₂ => rw [add_lie]; exact Submodule.add_mem _ h₁ h₂
  | add_right _ _ _ _ _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂
  | smul_left c _ _ _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c _ _ _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

private theorem string_words_span :
    Submodule.span ℝ (Set.range (LieWord.eval (FreeLieAlgebra.of ℝ : StringToken order → A))) = ⊤ := by
  let S' : LieSubalgebra ℝ A :=
    { Submodule.span ℝ (Set.range (LieWord.eval (FreeLieAlgebra.of ℝ : StringToken order → A))) with
      lie_mem' := fun hx hy => lie_mem_span_words _ hx hy }
  have h : LieSubalgebra.lieSpan ℝ A (Set.range (FreeLieAlgebra.of ℝ)) ≤ S' := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self (LieWord.token w))
  rw [free_lieSpan_eq_top] at h
  exact top_unique h

local notation "evalWord" => LieWord.eval (FreeLieAlgebra.of ℝ : StringToken order → A)
local notation "wordWeight" => LieWord.weight (tokenWeight order)

private theorem word_mem_stringGrade (w : LieWord (StringToken order)) :
    evalWord w ∈ stringGrade order (wordWeight w) := by
  induction w with
  | token w => exact token_mem_stringGrade order w
  | bracket u v hu hv => exact stringGrade_bracket order hu hv

private theorem wordWeight_positive (w : LieWord (StringToken order)) :
    0 < (wordWeight w).1 ∧ 0 < (wordWeight w).2 := by
  induction w with
  | token w => exact tokenWeight_positive order w
  | bracket u v hu hv =>
    exact ⟨add_pos hu.1 hv.1, add_pos hu.2 hv.2⟩

private theorem stringGrade_independent : iSupIndep (stringGrade order) :=
  (Module.End.eigenspaces_iSupIndep (stringEuler order).toLinearMap).comp weightScalar_injective

private theorem presentationGrade_independent : iSupIndep (presentationGrade order) :=
  (Module.End.eigenspaces_iSupIndep (presentationEuler order).toLinearMap).comp weightScalar_injective

/-- The free string grades are an internal algebraic direct sum. -/
noncomputable instance stringGradeDecomposition : DirectSum.Decomposition (stringGrade order) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (stringGrade_independent order)
  apply top_unique
  conv_lhs => rw [← string_words_span order]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  exact (le_iSup (stringGrade order) (wordWeight w)) (word_mem_stringGrade order w)

private def stringWordSet (p : Weight) : Set A :=
  {x | ∃ w : LieWord (StringToken order), wordWeight w = p ∧ x = evalWord w}

private theorem stringGrade_eq_span_words (p : Weight) :
    stringGrade order p = Submodule.span ℝ (stringWordSet order p) := by
  have hle : (fun p => Submodule.span ℝ (stringWordSet order p)) ≤ stringGrade order := by
    intro q
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl, rfl⟩
    exact word_mem_stringGrade order w
  have htop : (⨆ p, Submodule.span ℝ (stringWordSet order p)) = ⊤ := by
    apply top_unique
    conv_lhs => rw [← string_words_span order]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact (le_iSup (fun q => Submodule.span ℝ (stringWordSet order q)) (wordWeight w))
      (Submodule.subset_span ⟨w, rfl, rfl⟩)
  exact congrFun ((stringGrade_independent order).le_iff_eq_of_iSup_eq_top htop |>.mp hle).symm p

/-- Every nonzero string grade lies in the strictly positive quadrant. -/
theorem stringGrade_eq_bot_of_outside (p : Weight) (h : ¬ (0 < p.1 ∧ 0 < p.2)) :
    stringGrade order p = ⊥ := by
  rw [stringGrade_eq_span_words]
  suffices stringWordSet order p = ∅ by rw [this, Submodule.span_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨w, hw, _⟩
  exact h (hw ▸ wordWeight_positive order w)

private def presentationWordSet (p : Weight) : Set P :=
  {x | p = realRoot ∧ x = generator order none} ∪
    {x | ∃ w : LieWord (StringToken order), wordWeight w = p ∧
      x = stringMap order (evalWord w)}

private theorem presentationWordSet_le (p : Weight) :
    Submodule.span ℝ (presentationWordSet order p) ≤ presentationGrade order p := by
  apply Submodule.span_le.mpr
  rintro x (⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩)
  · exact real_mem_presentationGrade order
  · exact stringMap_mem_presentationGrade order (word_mem_stringGrade order w)

private theorem presentationWordSet_span :
    (⨆ p, Submodule.span ℝ (presentationWordSet order p)) = ⊤ := by
  let T : Submodule ℝ P := ⨆ p, Submodule.span ℝ (presentationWordSet order p)
  have he : generator order none ∈ T :=
    (le_iSup (fun p => Submodule.span ℝ (presentationWordSet order p)) realRoot)
      (Submodule.subset_span (Or.inl ⟨rfl, rfl⟩))
  have hs (x : A) : stringMap order x ∈ T := by
    have h : Submodule.span ℝ (Set.range evalWord) ≤ T.comap (stringMap order).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      exact (le_iSup (fun p => Submodule.span ℝ (presentationWordSet order p)) (wordWeight w))
        (Submodule.subset_span (Or.inr ⟨w, rfl, rfl⟩))
    apply h
    rw [string_words_span order]
    trivial
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := (presentationEquiv order).symm.surjective x
  change stringMap order y.left + y.right.toReal • generator order none ∈ T
  exact T.add_mem (hs y.left) (T.smul_mem _ he)

private theorem presentationGrade_eq_span_words (p : Weight) :
    presentationGrade order p = Submodule.span ℝ (presentationWordSet order p) :=
  congrFun ((presentationGrade_independent order).le_iff_eq_of_iSup_eq_top
    (presentationWordSet_span order) |>.mp (presentationWordSet_le order)).symm p

/-- The actual presentation has an internal algebraic direct sum decomposition by weights. -/
noncomputable instance presentationGradeDecomposition :
    DirectSum.Decomposition (presentationGrade order) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (presentationGrade_independent order)
  change (⨆ p, presentationGrade order p) = ⊤
  simp_rw [presentationGrade_eq_span_words]
  exact presentationWordSet_span order

/-- The real root and the strictly positive quadrant contain the entire support. -/
theorem presentationGrade_eq_bot_of_outside (p : Weight)
    (hreal : p ≠ realRoot) (hpos : ¬ (0 < p.1 ∧ 0 < p.2)) :
    presentationGrade order p = ⊥ := by
  rw [presentationGrade_eq_span_words]
  suffices presentationWordSet order p = ∅ by rw [this, Submodule.span_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x (⟨hr, _⟩ | ⟨w, hw, _⟩)
  · exact hreal hr
  · exact hpos (hw ▸ wordWeight_positive order w)

theorem presentationGrade_null (m : ℤ) : presentationGrade order (m, 0) = ⊥ := by
  apply presentationGrade_eq_bot_of_outside
  · simp [realRoot]
  · simp

private theorem wordWeight_fst_eq_one {w : LieWord (StringToken order)}
    (h : (wordWeight w).1 = 1) :
    ∃ j, w = .token (firstToken order j) := by
  cases w with
  | token w =>
    have hk : w.2.val = 0 := by
      change (tokenWeight order w).1 = 1 at h
      rw [tokenWeight_coordinates] at h
      dsimp at h
      omega
    obtain ⟨j, k⟩ := w
    have hfin : k = (firstToken order j).2 := Fin.ext hk
    exact ⟨j, congrArg (fun k => LieWord.token (⟨j, k⟩ : StringToken order)) hfin⟩
  | bracket u v =>
    have hu := (wordWeight_positive order u).1
    have hv := (wordWeight_positive order v).1
    change (wordWeight u).1 + (wordWeight v).1 = 1 at h
    omega

/-- The real root space is the real line generated by the real simple generator. -/
theorem presentationGrade_real :
    presentationGrade order realRoot = ℝ ∙ generator order none := by
  rw [presentationGrade_eq_span_words]
  congr 1
  ext x
  constructor
  · rintro (⟨_, rfl⟩ | ⟨w, hw, _⟩)
    · exact Set.mem_singleton _
    · have hp := (wordWeight_positive order w).2
      rw [hw] at hp
      norm_num [realRoot] at hp
  · intro hx
    exact Or.inl ⟨rfl, hx⟩

/-- Every other first-coordinate-one space is the span of precisely the imaginary
simple generators of that weight. For an absent order this is the zero space. -/
theorem presentationGrade_first (n : ℤ) (hn : n ≠ -1) :
    presentationGrade order (1, n) =
      Submodule.span ℝ {x | ∃ j : J, ((order j : ℕ) : ℤ) = n ∧
        x = generator order (some j)} := by
  rw [presentationGrade_eq_span_words]
  congr 1
  ext x
  constructor
  · rintro (⟨hr, _⟩ | ⟨w, hw, rfl⟩)
    · exact (hn (congrArg Prod.snd hr)).elim
    · obtain ⟨j, rfl⟩ := wordWeight_fst_eq_one order (congrArg Prod.fst hw)
      refine ⟨j, ?_, by simp [LieWord.eval, firstToken, adIter]⟩
      simpa [LieWord.weight, firstToken, tokenWeight, imaginaryRoot] using congrArg Prod.snd hw
  · rintro ⟨j, rfl, rfl⟩
    exact Or.inr ⟨.token (firstToken order j), by simp [LieWord.weight, firstToken, tokenWeight,
      imaginaryRoot], by simp [LieWord.eval, firstToken, adIter]⟩

/-- The supplier's tensor map instantiated with the constructed presentation grading. -/
def gradedPresentationDelta : P →ₗ[ℝ] P ⊗[ℝ] P :=
  presentationDelta order (presentationGrade order) (fun {_ _ _ _} => presentationGrade_bracket order)
    (real_mem_presentationGrade order) (imaginary_mem_presentationGrade order)

theorem gradedPresentationDelta_generator (j : Option J) :
    gradedPresentationDelta order (generator order j) = 0 :=
  presentation_tensor_generator order (presentationGrade order)
    (fun {_ _ _ _} => presentationGrade_bracket order)
    (real_mem_presentationGrade order) (imaginary_mem_presentationGrade order) j

theorem gradedPresentationDelta_bracket {p q : Weight} {x y : P}
    (hx : x ∈ presentationGrade order p) (hy : y ∈ presentationGrade order q) :
    gradedPresentationDelta order ⁅x, y⁆ = ⁅x, gradedPresentationDelta order y⁆ -
      ⁅y, gradedPresentationDelta order x⁆ + homogeneousEta weightForm p q x y :=
  presentation_tensor_bracket order (presentationGrade order)
    (fun {_ _ _ _} => presentationGrade_bracket order)
    (real_mem_presentationGrade order) (imaginary_mem_presentationGrade order) hx hy

end D5.S3.VertexAlgebra.MonsterPositiveStringPresentation
