/- GID: D5/S3/HomologicalAlgebra/Persistence/RealExtension
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit]
   utility: none
   digest: Consecutive arrows and real cells define actual persistence modules. -/

import D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalSplit
import D5.S3.HomologicalAlgebra.Persistence.FiniteIntervalDecomposition
import D5.S3.HomologicalAlgebra.Persistence.RealIntervalUniqueness
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace D5.S3.HomologicalAlgebra.Persistence.RealExtension

open CategoryTheory FiniteIntervalSplit

universe u v

variable {K : Type u} [Field K] {n : ℕ}

structure FiniteChain (K : Type u) [Field K] (length : ℕ) where
  object : Fin length → ModuleCat.{v} K
  arrow : ∀ index : Fin length, ∀ next : index.val + 1 < length,
    object index ⟶ object ⟨index.val + 1, next⟩

def paddedObject (chain : FiniteChain.{u, v} K n) (index : ℕ) : ModuleCat.{v} K :=
  if inside : index < n then chain.object ⟨index, inside⟩
  else if nonempty : 0 < n then chain.object ⟨n - 1, by omega⟩
  else ModuleCat.of K (ULift.{v} PUnit)

noncomputable def paddedArrow (chain : FiniteChain.{u, v} K n) (index : ℕ) :
    paddedObject chain index ⟶ paddedObject chain (index + 1) := by
  by_cases next : index + 1 < n
  · have inside : index < n := by omega
    exact eqToHom (by simp [paddedObject, inside]) ≫
      chain.arrow ⟨index, inside⟩ next ≫ eqToHom (by simp [paddedObject, next])
  · apply eqToHom
    by_cases inside : index < n
    · have last : index = n - 1 := by omega
      have nonempty : 0 < n := by omega
      simp only [paddedObject, dif_pos inside, dif_neg next, dif_pos nonempty]
      congr 1
      exact Fin.ext last
    · have outside : ¬ index + 1 < n := by omega
      simp [paddedObject, inside, outside]

noncomputable def chainFunctor (chain : FiniteChain.{u, v} K n) : Fin n ⥤ ModuleCat.{v} K :=
  let sequence := Functor.ofSequence (paddedArrow chain)
  let restricted := (show Monotone (fun index : Fin n => index.val) from
    fun _ _ ordered => ordered).functor ⋙ sequence
  restricted.copyObj chain.object (fun index => eqToIso (by
    simp [restricted, sequence, Functor.ofSequence, paddedObject, index.isLt]))

noncomputable def chainDiagram (chain : FiniteChain.{u, v} K n) :
    Diagram K (fun index => chain.object index) where
  map source target ordered := ((chainFunctor chain).map (homOfLE ordered)).hom
  identity index := by
    change ((chainFunctor chain).map (𝟙 index)).hom = LinearMap.id
    rw [CategoryTheory.Functor.map_id]
    rfl
  composition source middle target first second := by
    change (((chainFunctor chain).map (homOfLE first)) ≫
      ((chainFunctor chain).map (homOfLE second))).hom = _
    rw [← CategoryTheory.Functor.map_comp]
    rfl

variable {V : Fin n → Type v} [∀ index, AddCommGroup (V index)]
  [∀ index, Module K (V index)]

def zeroPrefixObject (_diagram : Diagram K V) : WithBot (Fin n) → ModuleCat.{v} K
  | ⊥ => ModuleCat.of K (ULift.{v} PUnit)
  | (index : Fin n) => ModuleCat.of K (V index)

noncomputable def zeroPrefix (diagram : Diagram K V) : WithBot (Fin n) ⥤ ModuleCat.{v} K where
  obj := zeroPrefixObject diagram
  map {source target} arrow := by
    cases source with
    | bot => exact ModuleCat.ofHom 0
    | coe source =>
      cases target with
      | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom arrow))
      | coe target =>
        exact ModuleCat.ofHom
          (diagram.map source target (WithBot.coe_le_coe.mp (leOfHom arrow)))
  map_id index := by
    cases index with
    | bot =>
      have : Subsingleton (zeroPrefixObject diagram ⊥) := by
        change Subsingleton (ULift.{v} PUnit)
        infer_instance
      ext vector
      exact Subsingleton.elim _ _
    | coe index =>
      change ModuleCat.ofHom (diagram.map index index le_rfl) = _
      rw [diagram.identity]
      rfl
  map_comp {source middle target} first second := by
    cases source with
    | bot =>
      have : Subsingleton (zeroPrefixObject diagram ⊥) := by
        change Subsingleton (ULift.{v} PUnit)
        infer_instance
      ext vector
      have zero : vector = 0 := Subsingleton.elim _ _
      subst vector
      simp
    | coe source =>
      cases middle with
      | bot => exact False.elim (WithBot.not_coe_le_bot source (leOfHom first))
      | coe middle =>
        cases target with
        | bot => exact False.elim (WithBot.not_coe_le_bot middle (leOfHom second))
        | coe target =>
          change ModuleCat.ofHom _ = ModuleCat.ofHom _ ≫ ModuleCat.ofHom _
          rw [← ModuleCat.ofHom_comp, diagram.composition]

structure Breakpoints (length : ℕ) where
  time : Fin length → ℝ
  increasing : StrictMono time

noncomputable def cell (grid : Breakpoints n) (time : ℝ) : WithBot (Fin n) := by
  classical
  exact Finset.univ.sup fun index => if grid.time index ≤ time then (index : WithBot (Fin n)) else ⊥

noncomputable def cellFunctor (grid : Breakpoints n) : ℝ ⥤ WithBot (Fin n) :=
  (show Monotone (cell grid) from by
    classical
    intro source target ordered
    apply Finset.sup_mono_fun
    intro index _
    by_cases born : grid.time index ≤ source
    · simp [born, born.trans ordered]
    · simp [born]).functor

noncomputable def realModule (diagram : Diagram K V) (grid : Breakpoints n) :
    ℝ ⥤ ModuleCat.{v} K := cellFunctor grid ⋙ zeroPrefix diagram

noncomputable def finiteModule (diagram : Diagram K V) : Fin n ⥤ ModuleCat.{v} K :=
  (show Monotone (fun index : Fin n => (index : WithBot (Fin n))) from
    fun _ _ ordered => WithBot.coe_le_coe.mpr ordered).functor ⋙ zeroPrefix diagram

noncomputable def samplingIso (diagram : Diagram K V) (grid : Breakpoints n) :
    grid.increasing.monotone.functor ⋙ realModule diagram grid ≅ finiteModule diagram := by
  classical
  have sample : ∀ index, cell grid (grid.time index) = (index : WithBot (Fin n)) := by
    intro index
    apply le_antisymm
    · apply Finset.sup_le
      intro other _
      by_cases born : grid.time other ≤ grid.time index
      · simp [born, grid.increasing.le_iff_le.mp born]
      · simp [born]
    · have included := Finset.le_sup (f := fun other =>
        if grid.time other ≤ grid.time index then (other : WithBot (Fin n)) else ⊥)
        (Finset.mem_univ index)
      change (index : WithBot (Fin n)) ≤ Finset.univ.sup _
      simpa only [if_pos le_rfl] using included
  let embedding := (show Monotone (fun index : Fin n => (index : WithBot (Fin n))) from
    fun _ _ ordered => WithBot.coe_le_coe.mpr ordered).functor
  let cells : grid.increasing.monotone.functor ⋙ cellFunctor grid ≅ embedding :=
    NatIso.ofComponents (fun index => eqToIso (sample index)) (fun _ => Subsingleton.elim _ _)
  exact CategoryTheory.Functor.isoWhiskerRight cells (zeroPrefix diagram)

noncomputable def realFamily (diagram : Diagram K V)
    (basis : FiniteIntervalDecomposition.IntervalBasis diagram) (grid : Breakpoints n) :
    RealIntervalUniqueness.IntervalFamily (ULift.{v} basis.Occurrence) where
  birth occurrence := grid.time (basis.birth occurrence.down)
  death occurrence := if next : (basis.last occurrence.down).val + 1 < n then
    (grid.time ⟨(basis.last occurrence.down).val + 1, next⟩ : WithTop ℝ) else ⊤
  positive occurrence := by
    classical
    split_ifs with next
    · apply WithTop.coe_lt_coe.mpr
      apply grid.increasing
      have ordered := basis.ordered occurrence.down
      change (basis.birth occurrence.down).val < (basis.last occurrence.down).val + 1
      omega
    · exact WithTop.coe_lt_top _

end D5.S3.HomologicalAlgebra.Persistence.RealExtension
