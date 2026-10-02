/- GID: D5/S3/HomologicalAlgebra/Persistence/RealDecomposition
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/RealDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/HomologicalAlgebra/Persistence/RealExtension,
     D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition,
     D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness]
   utility: none
   digest: Construct the actual natural real interval-sum isomorphism. -/

import D5.S3.HomologicalAlgebra.Persistence.RealExtension
import Mathlib.Algebra.Category.ModuleCat.Ulift

namespace D5.S3.HomologicalAlgebra.Persistence.RealDecomposition

open CategoryTheory Module FiniteIntervalSplit FiniteIntervalDecomposition RealExtension
  RealIntervalUniqueness

universe u v

variable {K : Type u} [Field K] {n : ℕ} {V : Fin n → Type v}
  [∀ index, AddCommGroup (V index)] [∀ index, Module K (V index)]

structure Decomposition (diagram : Diagram K V) (grid : Breakpoints n) where
  Occurrence : Type v
  finite : Fintype Occurrence
  family : IntervalFamily Occurrence
  isomorphism : realModule diagram grid ⋙ ModuleCat.uliftFunctor.{u} K ≅
    intervalSum (K := K) family

attribute [instance] Decomposition.finite

set_option backward.isDefEq.respectTransparency false in
noncomputable def decompose [∀ index, FiniteDimensional K (V index)]
    (diagram : Diagram K V) (grid : Breakpoints n) : Decomposition diagram grid := by
  classical
  let basis := Classical.choice (exists_interval_basis diagram)
  let family := realFamily diagram basis grid
  have born_test : ∀ (index : Fin n) (time : ℝ),
      (index : WithBot (Fin n)) ≤ cell grid time ↔ grid.time index ≤ time := by
    intro index time
    change (index : WithBot (Fin n)) ≤ Finset.univ.sup _ ↔ _
    rw [Finset.le_sup_iff (WithBot.bot_lt_coe index)]
    constructor
    · rintro ⟨other, _, below⟩
      by_cases born : grid.time other ≤ time
      · have ordered : index ≤ other := by simpa [born] using below
        exact (grid.increasing.monotone ordered).trans born
      · simp [born] at below
    · intro born
      exact ⟨index, Finset.mem_univ _, by simp [born]⟩
  have death_test : ∀ occurrence time,
      cell grid time ≤ (basis.last occurrence.down : WithBot (Fin n)) ↔
        (time : WithTop ℝ) < family.death occurrence := by
    intro occurrence time
    by_cases next : (basis.last occurrence.down).val + 1 < n
    · simp only [family, realFamily, dif_pos next]
      rw [WithTop.coe_lt_coe]
      constructor
      · intro below
        by_contra not_before
        have next_born := (born_test ⟨(basis.last occurrence.down).val + 1, next⟩ time).mpr
          (le_of_not_gt not_before)
        have impossible := WithBot.coe_le_coe.mp (next_born.trans below)
        change (basis.last occurrence.down).val + 1 ≤ (basis.last occurrence.down).val at impossible
        omega
      · intro before
        apply Finset.sup_le
        intro index _
        by_cases born : grid.time index ≤ time
        · have ordered := grid.increasing.lt_iff_lt.mp (born.trans_lt before)
          have below : index ≤ basis.last occurrence.down := by
            change index.val ≤ (basis.last occurrence.down).val
            change index.val < (basis.last occurrence.down).val + 1 at ordered
            omega
          simpa [born] using (WithBot.coe_le_coe.mpr below)
        · simp [born]
    · have bounded : cell grid time ≤ (basis.last occurrence.down : WithBot (Fin n)) := by
        apply Finset.sup_le
        intro index _
        by_cases born : grid.time index ≤ time
        · have below : index ≤ basis.last occurrence.down := by
            have range := index.isLt
            change index.val ≤ (basis.last occurrence.down).val
            omega
          simpa [born] using (WithBot.coe_le_coe.mpr below)
        · simp [born]
      simp [family, realFamily, next, bounded]
  have support_test : ∀ occurrence time,
      family.birth occurrence ≤ time ∧ (time : WithTop ℝ) < family.death occurrence ↔
        (basis.birth occurrence.down : WithBot (Fin n)) ≤ cell grid time ∧
          cell grid time ≤ (basis.last occurrence.down : WithBot (Fin n)) := by
    intro occurrence time
    change grid.time (basis.birth occurrence.down) ≤ time ∧ _ ↔ _
    rw [← born_test, ← death_test]
  have zero_coordinates : ∀ time, cell grid time = ⊥ →
      Subsingleton (intervalSpace (K := K) family time) := by
    intro time selected
    refine ⟨fun first second => ?_⟩
    ext occurrence
    have unsupported : ¬ (family.birth occurrence ≤ time ∧
        (time : WithTop ℝ) < family.death occurrence) := by
      intro supported
      have impossible := (support_test occurrence time).mp supported
      rw [selected] at impossible
      exact WithBot.not_coe_le_bot _ impossible.1
    rw [first.property occurrence unsupported, second.property occurrence unsupported]
  let vector_map : ∀ slot time, intervalSpace (K := K) family time →ₗ[K]
      ULift.{u} (zeroPrefixObject diagram slot) := fun slot time => by
    cases slot with
    | bot => exact 0
    | coe index =>
      change intervalSpace (K := K) family time →ₗ[K] ULift.{u} (V index)
      exact ULift.moduleEquiv.symm.toLinearMap.comp
        (∑ occurrence : basis.Occurrence,
          LinearMap.smulRight
            ((LinearMap.proj (ULift.up occurrence)).comp (intervalSpace family time).subtype)
            (basis.vectors occurrence index))
  have vector_map_bijective : ∀ slot time, cell grid time = slot →
      Function.Bijective (vector_map slot time) := by
    intro slot time selected
    cases slot with
    | bot =>
      have := zero_coordinates time selected
      have : Subsingleton (ULift.{u} (zeroPrefixObject diagram ⊥)) := by
        change Subsingleton (ULift.{u} (ULift.{v} PUnit))
        infer_instance
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun target =>
        ⟨0, Subsingleton.elim _ _⟩⟩
    | coe index =>
      let restriction : intervalSpace (K := K) family time ≃ₗ[K]
          ({occurrence // basis.birth occurrence ≤ index ∧ index ≤ basis.last occurrence} → K) := {
        toFun := fun coordinates occurrence => coordinates.val (ULift.up occurrence.val)
        invFun := fun coordinates => ⟨fun occurrence =>
          if supported : basis.birth occurrence.down ≤ index ∧ index ≤ basis.last occurrence.down
          then coordinates ⟨occurrence.down, supported⟩ else 0, by
            intro occurrence unsupported
            have absent : ¬ (basis.birth occurrence.down ≤ index ∧
                index ≤ basis.last occurrence.down) := by
              simpa [selected] using (support_test occurrence time).not.mp unsupported
            simp [absent]⟩
        left_inv := by
          intro coordinates
          ext occurrence
          by_cases supported : basis.birth occurrence.down ≤ index ∧
              index ≤ basis.last occurrence.down
          · simp [supported]
          · have absent : ¬ (family.birth occurrence ≤ time ∧
                (time : WithTop ℝ) < family.death occurrence) := by
              apply (support_test occurrence time).not.mpr
              simpa [selected] using supported
            simp [supported, coordinates.property occurrence absent]
        right_inv := by intro coordinates; funext occurrence; simp [occurrence.property]
        map_add' := by intro left right; rfl
        map_smul' := by intro scalar coordinates; rfl }
      have reconstruction : ∀ coordinates : intervalSpace (K := K) family time,
          (∑ occurrence : basis.Occurrence,
            coordinates.val (ULift.up occurrence) • basis.vectors occurrence index) =
          (basis.basis index).equivFun.symm (restriction coordinates) := by
        intro coordinates
        rw [Basis.equivFun_symm_apply]
        simp only [restriction, basis.basis_vectors]
        have complement : (∑ occurrence : {occurrence //
            ¬ (basis.birth occurrence ≤ index ∧ index ≤ basis.last occurrence)},
            coordinates.val (ULift.up occurrence.val) •
              basis.vectors occurrence.val index) = 0 := by
          apply Finset.sum_eq_zero
          intro occurrence _
          simp [basis.unsupported occurrence.val index occurrence.property]
        have total := Fintype.sum_subtype_add_sum_subtype
          (fun occurrence => basis.birth occurrence ≤ index ∧ index ≤ basis.last occurrence)
          (fun occurrence =>
            coordinates.val (ULift.up occurrence) • basis.vectors occurrence index)
        rw [complement, add_zero] at total
        exact total.symm
      have equality : vector_map (index : WithBot (Fin n)) time =
          (restriction.trans ((basis.basis index).equivFun.symm.trans
            ULift.moduleEquiv.symm)).toLinearMap := by
        apply LinearMap.ext
        intro coordinates
        let lifting : V index ≃ₗ[K] ULift.{u} (V index) :=
          (ULift.moduleEquiv (R := K)).symm
        have lifted := congrArg lifting (reconstruction coordinates)
        simpa only [vector_map, zeroPrefixObject, WithBot.recBotCoe_coe, id_eq,
          LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
          LinearMap.proj_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
          LinearEquiv.trans_apply, lifting, map_sum, map_smul] using lifted
      rw [equality]
      exact (restriction.trans ((basis.basis index).equivFun.symm.trans
        ULift.moduleEquiv.symm)).bijective
  let components : ∀ time, (intervalSum (K := K) family).obj time ≅
      (realModule diagram grid ⋙ ModuleCat.uliftFunctor.{u} K).obj time := fun time =>
    (LinearEquiv.ofBijective (vector_map (cell grid time) time)
      (vector_map_bijective (cell grid time) time rfl)).toModuleIso
  have square : ∀ source target (ordered : source ≤ target)
      (source_slot target_slot : WithBot (Fin n)),
      cell grid source = source_slot → cell grid target = target_slot →
      ∀ slot_ordered : source_slot ≤ target_slot,
      (vector_map target_slot target).comp (intervalArrow family source target ordered) =
        (ULift.moduleEquiv.symm.toLinearMap.comp
          (((zeroPrefix diagram).map (homOfLE slot_ordered)).hom.comp
            ULift.moduleEquiv.toLinearMap)).comp (vector_map source_slot source) := by
      intro source target ordered source_slot target_slot source_cell target_cell slot_ordered
      cases source_slot with
      | bot =>
        have := zero_coordinates source source_cell
        apply LinearMap.ext
        intro coordinates
        have zero : coordinates = 0 := Subsingleton.elim _ _
        subst coordinates
        simp
      | coe source_index =>
        cases target_slot with
        | bot =>
          exact False.elim (WithBot.not_coe_le_bot _ slot_ordered)
        | coe target_index =>
          apply LinearMap.ext
          intro coordinates
          apply ULift.ext
          simp [zeroPrefix, vector_map, zeroPrefixObject,
            map_sum, map_smul, basis.naturality]
          apply Finset.sum_congr rfl
          intro occurrence _
          by_cases born : basis.birth occurrence ≤ source_index
          · have survival : (target : WithTop ℝ) < family.death (ULift.up occurrence) ↔
                target_index ≤ basis.last occurrence := by
              simpa [target_cell] using (death_test (ULift.up occurrence) target).symm
            by_cases survives : target_index ≤ basis.last occurrence <;>
              simp [intervalArrow, born, survives, survival] <;> rfl
          · have absent : ¬ (family.birth (ULift.up occurrence) ≤ source ∧
                (source : WithTop ℝ) < family.death (ULift.up occurrence)) := by
              rw [support_test, source_cell]
              intro supported
              exact born (WithBot.coe_le_coe.mp supported.1)
            simp [intervalArrow, born, coordinates.property (ULift.up occurrence) absent]
            rfl
  let isomorphism : intervalSum (K := K) family ≅
      realModule diagram grid ⋙ ModuleCat.uliftFunctor.{u} K :=
    NatIso.ofComponents components (by
      intro source target arrow
      apply ModuleCat.hom_ext
      exact square source target (leOfHom arrow) (cell grid source) (cell grid target)
        rfl rfl (leOfHom ((cellFunctor grid).map arrow)))
  exact {
    Occurrence := ULift.{v} basis.Occurrence
    finite := inferInstance
    family := family
    isomorphism := isomorphism.symm }

end D5.S3.HomologicalAlgebra.Persistence.RealDecomposition
