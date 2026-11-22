/- GID: D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/CrossedModuleSurfacePasting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Quaternion, mathlib/module/Mathlib.GroupTheory.Subgroup.Center]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.claim; result=D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.result; claim=D5/S3/HomologicalAlgebra/CrossedModuleSurfacePasting.claim
   digest: Typed crossed-module pasting satisfies Peiffer interchange and admits a nontrivial central quaternion shell. -/

import Mathlib.Algebra.Group.End
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting

universe u v

/-- A group homomorphism with an equivariant action satisfying the Peiffer identity. -/
structure CrossedModule (H : Type u) (G : Type v) [Group H] [Group G] where
  μ : H →* G
  act : G →* MulAut H
  equivariant : ∀ p h, μ (act p h) = p * μ h * p⁻¹
  peiffer : ∀ h k, act (μ h) k = h * k * h⁻¹

variable {H : Type u} {G : Type v} [Group H] [Group G]

/-- The Peiffer identity forces every kernel element to commute with all labels. -/
theorem CrossedModule.ker_le_center (X : CrossedModule H G) :
    ∀ h ∈ X.μ.ker, h ∈ Subgroup.center H := by
  intro h hh
  have hμ := MonoidHom.mem_ker.mp hh
  apply Subgroup.mem_center_iff.mpr
  intro k
  have hc := X.peiffer h k
  rw [hμ, map_one, MulAut.one_apply] at hc
  calc
    _ = (h * k * h⁻¹) * h := congrArg (· * h) hc
    _ = _ := by group

/-- A label with prescribed source and target path gains. -/
@[ext]
structure Face (X : CrossedModule H G) (p q : G) where
  label : H
  boundary : X.μ label * p = q

namespace Face

variable {X : CrossedModule H G}
variable {p q r s p' q' r' p'' q'' : G}

/-- The boundary equation is equivalent to facewise fake flatness. -/
theorem fake_flat_iff (X : CrossedModule H G) (p q : G) (h : H) :
    X.μ h * p = q ↔ X.μ h = q * p⁻¹ := by
  constructor
  · intro hh
    rw [← hh]
    group
  · intro hh
    rw [hh]
    group

/-- The identity face on a path gain. -/
def id (X : CrossedModule H G) (p : G) : Face X p p :=
  ⟨1, by rw [map_one, one_mul]⟩

/-- Vertical pasting applies the second label after the first. -/
def vertical (h : Face X p q) (k : Face X q r) : Face X p r :=
  ⟨k.label * h.label, by
    rw [map_mul, mul_assoc, h.boundary, k.boundary]⟩

/-- Horizontal pasting acts on the second label by the first source path. -/
def horizontal (h : Face X p q) (k : Face X p' q') : Face X (p * p') (q * q') :=
  ⟨h.label * X.act p k.label, by
    have hh := (fake_flat_iff X p q h.label).mp h.boundary
    rw [map_mul, X.equivariant, hh]
    calc
      _ = q * (X.μ k.label * p') := by group
      _ = q * q' := by rw [k.boundary]⟩

/-- Vertical pasting has identity faces and is associative. -/
theorem vertical_laws (h : Face X p q) (k : Face X q r) (l : Face X r s) :
    (id X p).vertical h = h ∧ h.vertical (id X q) = h ∧
      (h.vertical k).vertical l = h.vertical (k.vertical l) := by
  refine ⟨Face.ext (mul_one _), Face.ext (one_mul _), Face.ext ?_⟩
  exact (mul_assoc _ _ _).symm

/-- Horizontal pasting has unit path identities and is associative on labels.
The two endpoints of the associative composites are identified by group associativity. -/
theorem horizontal_laws (h : Face X p q) (k : Face X p' q')
    (l : Face X p'' q'') :
    ((id X 1).horizontal h).label = h.label ∧
      (h.horizontal (id X 1)).label = h.label ∧
      ((h.horizontal k).horizontal l).label = (h.horizontal (k.horizontal l)).label := by
  refine ⟨?_, ?_, ?_⟩
  · simp [horizontal, id]
  · simp [horizontal, id]
  · simp only [horizontal]
    rw [map_mul X.act, MulAut.mul_apply, map_mul, mul_assoc]

/-- The Peiffer identity exchanges the two orders of pasting a typed square grid. -/
theorem interchange (h : Face X p q) (k : Face X p' q')
    (h' : Face X q r) (k' : Face X q' r') :
    (h.horizontal k).vertical (h'.horizontal k') =
      (h.vertical h').horizontal (k.vertical k') := by
  have exchange : X.act q k'.label * h.label = h.label * X.act p k'.label := by
    rw [← h.boundary, map_mul X.act, MulAut.mul_apply, X.peiffer]
    group
  apply Face.ext
  change (h'.label * X.act q k'.label) * (h.label * X.act p k.label) =
    (h'.label * h.label) * X.act p (k'.label * k.label)
  rw [map_mul]
  calc
    _ = h'.label * ((X.act q k'.label * h.label) * X.act p k.label) := by group
    _ = _ := by rw [exchange]; group

end Face

/-- Six oriented edge gains and four typed faces of a tetrahedral shell. -/
structure Tetrahedron (X : CrossedModule H G) where
  g01 : G
  g02 : G
  g03 : G
  g12 : G
  g13 : G
  g23 : G
  h012 : Face X g02 (g01 * g12)
  h013 : Face X g03 (g01 * g13)
  h023 : Face X g03 (g02 * g23)
  h123 : Face X g13 (g12 * g23)

namespace Tetrahedron

variable {X : CrossedModule H G}

/-- Paste through the path via vertices 1 and 3. -/
def left (T : Tetrahedron X) : Face X T.g03 (T.g01 * (T.g12 * T.g23)) :=
  T.h013.vertical ((Face.id X T.g01).horizontal T.h123)

/-- Paste through the path via vertices 2 and 3, typing the final path by associativity. -/
def right (T : Tetrahedron X) : Face X T.g03 (T.g01 * (T.g12 * T.g23)) :=
  let h := T.h023.vertical (T.h012.horizontal (Face.id X T.g23))
  ⟨T.h012.label * T.h023.label, by
    simpa only [Face.vertical, Face.horizontal, Face.id, map_one, mul_one, mul_assoc]
      using h.boundary⟩

/-- The ratio of the two labels with common source and target. -/
def obstruction (T : Tetrahedron X) : H := T.left.label * T.right.label⁻¹

/-- The two typed composites have equal images under the boundary homomorphism. -/
theorem obstruction_mem_ker (T : Tetrahedron X) : T.obstruction ∈ X.μ.ker := by
  have hm : X.μ T.left.label = X.μ T.right.label :=
    mul_right_cancel (T.left.boundary.trans T.right.boundary.symm)
  rw [MonoidHom.mem_ker, obstruction, map_mul, map_inv, hm, mul_inv_cancel]

/-- The ratio commutes with every element of the label group. -/
theorem obstruction_mem_center (T : Tetrahedron X) :
    T.obstruction ∈ Subgroup.center H :=
  X.ker_le_center _ T.obstruction_mem_ker

/-- The ratio is the identity exactly when the two labels agree. -/
theorem obstruction_eq_one_iff (T : Tetrahedron X) :
    T.obstruction = 1 ↔ T.left.label = T.right.label := by
  change T.left.label * T.right.label⁻¹ = 1 ↔ _
  exact mul_inv_eq_one

end Tetrahedron

/-- The Klein four group in multiplicative notation. -/
abbrev V4 := Multiplicative (ZMod 2 × ZMod 2)

private def parity : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

private theorem zmod_two_neg (i : ZMod 2) : -i = i := by
  fin_cases i <;> decide

/-- The quotient sends a power of a to its parity and records the presence of x. -/
def q8Boundary : QuaternionGroup 2 →* V4 where
  toFun
    | .a i => Multiplicative.ofAdd (0, parity i)
    | .xa i => Multiplicative.ofAdd (1, parity i)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply (Multiplicative.toAdd : V4 ≃ _).injective <;>
      change Prod.mk _ _ = Prod.mk _ _ <;>
      congr 1 <;>
      simp [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
        QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa, sub_eq_add_neg,
        zmod_two_neg, add_comm] <;> decide

private theorem q8Boundary_surjective : Function.Surjective q8Boundary := by
  intro y
  obtain ⟨i, j⟩ := y.toAdd
  change ∃ h, q8Boundary h = Multiplicative.ofAdd (i, j)
  fin_cases i <;> fin_cases j
  · exact ⟨.a 0, rfl⟩
  · exact ⟨.a 1, rfl⟩
  · exact ⟨.xa 0, rfl⟩
  · exact ⟨.xa 1, rfl⟩

/-- The central element a squared in the quaternion group. -/
def minusOne : QuaternionGroup 2 := .a 2

private theorem q8Boundary_kernel (h : QuaternionGroup 2) :
    h ∈ q8Boundary.ker ↔ h = 1 ∨ h = minusOne := by
  cases h with
  | a i => fin_cases i <;> decide
  | xa i => fin_cases i <;> decide

private theorem minusOne_central : minusOne ∈ Subgroup.center (QuaternionGroup 2) := by
  rw [Subgroup.mem_center_iff]
  rintro (i | i) <;> fin_cases i <;> decide

private theorem q8Conj_kernel (h : QuaternionGroup 2) (hh : h ∈ q8Boundary.ker) :
    MulAut.conj h = 1 := by
  rcases (q8Boundary_kernel h).mp hh with rfl | rfl
  · exact map_one _
  · ext k
    change minusOne * k * minusOne⁻¹ = k
    rw [← (Subgroup.mem_center_iff.mp minusOne_central k), mul_assoc, mul_inv_cancel, mul_one]

private noncomputable def q8Action : V4 →* MulAut (QuaternionGroup 2) :=
  q8Boundary.liftOfSurjective q8Boundary_surjective ⟨MulAut.conj, q8Conj_kernel⟩

private theorem q8Action_proj (h : QuaternionGroup 2) :
    q8Action (q8Boundary h) = MulAut.conj h :=
  MonoidHom.liftOfRightInverse_comp_apply ..

/-- The action of the Klein four quotient is conjugation by a quaternion lift. -/
noncomputable def q8CrossedModule : CrossedModule (QuaternionGroup 2) V4 where
  μ := q8Boundary
  act := q8Action
  equivariant := by
    intro p k
    obtain ⟨h, rfl⟩ := q8Boundary_surjective p
    rw [q8Action_proj]
    change q8Boundary (h * k * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  peiffer := by
    intro h k
    rw [q8Action_proj]
    rfl

/-- The tetrahedral edge gains are the images of a and x on 01 and 12,
and the identity on the four remaining edges. -/
def q8Tetrahedron : Tetrahedron q8CrossedModule where
  g01 := q8Boundary (.a 1)
  g02 := 1
  g03 := 1
  g12 := q8Boundary (.xa 0)
  g13 := 1
  g23 := 1
  h012 := ⟨.xa 1, by decide⟩
  h013 := ⟨.a 1, by decide⟩
  h023 := ⟨1, by decide⟩
  h123 := ⟨.xa 0, by decide⟩

private theorem q8_left (T : Tetrahedron q8CrossedModule)
    (h01 : T.g01 = q8Boundary (.a 1)) (h123 : T.h123.label = .xa 0)
    (h013 : T.h013.label = .a 1) : T.left.label = .xa 3 := by
  change (1 * q8CrossedModule.act T.g01 T.h123.label) * T.h013.label = _
  rw [one_mul, h01, h123, h013, q8CrossedModule.peiffer]
  decide

/-- In this typed shell the two composite labels are xa cubed and xa.
Their ratio is the nonidentity central element a squared. -/
theorem q8_tetrahedron_nontrivial :
    ∃ T : Tetrahedron q8CrossedModule, T.obstruction = minusOne ∧ T.obstruction ≠ 1 := by
  have hleft := q8_left q8Tetrahedron rfl rfl rfl
  have hright : q8Tetrahedron.right.label = .xa 1 := by decide
  have h : q8Tetrahedron.obstruction = minusOne := by
    rw [Tetrahedron.obstruction, hleft, hright]
    decide
  exact ⟨q8Tetrahedron, h, h.trans_ne (by decide)⟩

/-- The proposed assertion that facewise typing alone forces a trivial shell. -/
def claim : Prop := ∀ T : Tetrahedron q8CrossedModule, T.obstruction = 1

/-- The typed quaternion shell refutes automatic triviality. -/
theorem result : ¬ claim := by
  obtain ⟨T, _, h⟩ := q8_tetrahedron_nontrivial
  exact fun all => h (all T)

end D5.S3.HomologicalAlgebra.CrossedModuleSurfacePasting
