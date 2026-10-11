/- GID: D5/S3/HomologicalAlgebra/Solid/BinaryShiftSupplier
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/BinaryShiftSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Actual continuous binary child operations on the protected sequence object P.
Binary subdivision identities are as in Rodríguez Camargo, Notes on Solid
Geometry, arXiv:2603.03012, proof of Proposition 3.2.5.
-/
/- Supplier source: immutable root review
/tmp/trureturing-cw-derived-simplex-review-20261006/src/CWComparison/BinaryShift.lean
SHA256 0dad874eeda461d16996b0253868c584bd5f0e190f71dd013fc4a90b78486a95
Original source is a newly proved Apache-2.0 checkpoint module, not an upstream
LeanCondensed file. Underlying protected supplier pin: LeanCondensed
339ecc99fdc4bdb68ef248c16da0148dce61a639; official Mathlib
5e0c4e5239cb0a2d86d68a884bf52cfd963fce22 / Lean4.35.0-rc3.
Only the import is isolated to the existing proved BoundedObject/DiscreteInt closure;
all formal declaration bodies below remain byte-identical. -/
import D5.S3.HomologicalAlgebra.Solid.BoundedObject

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightProfinite OnePoint Filter Topology

namespace CWComparison

local instance : Epi P_proj := inferInstanceAs (Epi (cokernel.π P_map))

/-- Proper affine indexing maps really extend continuously to infinity. -/
def binarySequenceMap (c : ℕ) : ℕ∪{∞} ⟶ ℕ∪{∞} := ConcreteCategory.ofHom {
  toFun := OnePoint.map (fun n => 2 * n + c)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    have ht : Tendsto (OnePoint.some : ℕ → OnePoint ℕ) atTop (𝓝 ∞) := by
      simpa only [coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
        Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
    exact ht.comp (tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n + c)
      tendsto_id) }

abbrev binaryLeft : ℕ∪{∞} ⟶ ℕ∪{∞} := binarySequenceMap 1
abbrev binaryRight : ℕ∪{∞} ⟶ ℕ∪{∞} := binarySequenceMap 2

@[simp] theorem binaryLeft_shift : binaryLeft ≫ LightProfinite.shift = binaryRight := by
  ext x
  cases x with
  | none => rfl
  | some n => change OnePoint.some (2 * n + 1 + 1) = OnePoint.some (2 * n + 2); congr 1

@[simp] theorem binaryRight_shift :
    binaryRight ≫ LightProfinite.shift = LightProfinite.shift ≫ binaryLeft := by
  ext x
  cases x with
  | none => rfl
  | some n => change OnePoint.some (2 * n + 2 + 1) = OnePoint.some (2 * (n + 1) + 1); congr 1 <;> omega

/-- Descending an infinity-preserving map to the exact protected cokernel P. -/
def sequencePMap (f : ℕ∪{∞} ⟶ ℕ∪{∞}) (hf : f ∞ = ∞) : P ⟶ P :=
  P_homMk P ((lightProfiniteToLightCondSet ⋙ free ℤ).map f ≫ P_proj) (by
    rw [← Category.assoc, P_map, ← Functor.map_comp]
    have h : ι ≫ f = ι := by ext p; exact hf
    rw [h]
    exact cokernel.condition _)

@[reassoc (attr := simp)] theorem P_proj_sequencePMap (f : ℕ∪{∞} ⟶ ℕ∪{∞}) (hf : f ∞ = ∞) :
    P_proj ≫ sequencePMap f hf = (lightProfiniteToLightCondSet ⋙ free ℤ).map f ≫ P_proj := by
  simp [sequencePMap, P_homMk, P_proj]

/-- The genuine child endomorphisms of P. -/
abbrev PbinaryLeft : P ⟶ P := sequencePMap binaryLeft rfl
abbrev PbinaryRight : P ⟶ P := sequencePMap binaryRight rfl
abbrev Pshift : P ⟶ P := sequencePMap LightProfinite.shift rfl

/-- The shift expression is identified with the protected oneMinusShift, not a
replacement definition of solidness. -/
theorem oneMinusShift_eq : oneMinusShift = 𝟙 P - Pshift := by
  apply (cancel_epi P_proj).1
  rw [LightCondensed.P_proj_oneMinusShift]
  simp [oneMinusShift', Preadditive.comp_sub, Preadditive.sub_comp]

/-- The binary relation holds as an equality of actual condensed morphisms. -/
theorem PbinaryLeft_shift : PbinaryLeft ≫ Pshift = PbinaryRight := by
  apply (cancel_epi P_proj).1
  dsimp [PbinaryLeft, PbinaryRight, Pshift]
  simp only [P_proj_sequencePMap_assoc, P_proj_sequencePMap]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map binaryLeft ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift ≫ P_proj = _
  rw [← Functor.map_comp_assoc, binaryLeft_shift]

theorem PbinaryRight_shift : PbinaryRight ≫ Pshift = Pshift ≫ PbinaryLeft := by
  apply (cancel_epi P_proj).1
  dsimp [PbinaryLeft, PbinaryRight, Pshift]
  simp only [P_proj_sequencePMap_assoc, P_proj_sequencePMap]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map binaryRight ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift ≫ P_proj =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map binaryLeft ≫ P_proj
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, binaryRight_shift]

theorem binary_P_subdivision :
    (PbinaryLeft + PbinaryRight) ≫ oneMinusShift = oneMinusShift ≫ PbinaryLeft := by
  rw [oneMinusShift_eq]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.add_comp,
    Category.id_comp, Category.comp_id, PbinaryLeft_shift, PbinaryRight_shift]
  abel

/-- A finite section of the actual sequence quotient. -/
def Pfinite (n : ℕ) : (free ℤ).obj (LightProfinite.of PUnit).toCondensed ⟶ P :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map
    (ConcreteCategory.ofHom (X := LightProfinite.of PUnit) (Y := ℕ∪{∞})
      ⟨fun _ => OnePoint.some n, continuous_const⟩) ≫ P_proj

@[simp] theorem Pfinite_binaryLeft (n : ℕ) :
    Pfinite n ≫ PbinaryLeft = Pfinite (2 * n + 1) := by
  simp only [Pfinite, Category.assoc, P_proj_sequencePMap, ← Functor.map_comp_assoc]
  rfl

@[simp] theorem Pfinite_oneMinusShift (n : ℕ) :
    Pfinite n ≫ oneMinusShift = Pfinite n - Pfinite (n + 1) := by
  rw [oneMinusShift_eq, Preadditive.comp_sub, Category.comp_id]
  congr 1
  simp only [Pfinite, Category.assoc, P_proj_sequencePMap, ← Functor.map_comp_assoc]
  rfl

end CWComparison
