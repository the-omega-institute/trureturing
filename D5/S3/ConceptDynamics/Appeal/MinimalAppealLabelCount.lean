/- GID: D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The maximum target diversity in a case fiber is the exact appeal label count. -/

import D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'minimal_appeal_label_count' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested repository search for `label`, `appeal`, fiber images, and
     minimal cardinalities found the adjacent appeal obstruction theorem and
     `Coding.FiberBinaryIdentification`, but no exact minimum-label theorem.
   * Exact upstream hits `fiberTargetValues` and `worstFiberDiversity` provide
     the fiber image and its maximum, so they are imported rather than
     redeclared. `Finset.equivFin`, `Fin.castLE_injective`, `Finset.le_sup`,
     and `Fintype.card_le_of_injective` provide the coding and cardinal bounds.
   * `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` is a pigeonhole
     alternative; the lower bound instead reuses the direct injective-cardinal
     lemma after choosing one state for each realized target value. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount

open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

/-- An appeal label makes the target exact when equal records and equal labels
force equal target outcomes. -/
def AppealDetermines {X B Y : Type*} {m : Nat}
    (record : X -> B) (target : X -> Y) (label : X -> Fin m) : Prop :=
  forall x y, record x = record y -> label x = label y -> target x = target y

/-- The maximum number of target outcomes in a record fiber is both attainable
by one finite appeal label and a lower bound for every such exact label. -/
theorem minimal_appeal_label_count
    {X B Y : Type*} [Fintype X] [Fintype B]
    (record : X -> B) (target : X -> Y) :
    (exists label : X -> Fin (worstFiberDiversity record target),
      AppealDetermines record target label) /\
    (forall {m : Nat} (label : X -> Fin m),
      AppealDetermines record target label ->
        worstFiberDiversity record target <= m) := by
  classical
  let values : B -> Finset Y := fiberTargetValues record target
  have target_mem_values (x : X) : target x ∈ values (record x) := by
    dsimp only [values, fiberTargetValues]
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩, rfl⟩
  have hcard (b : B) :
      (values b).card <= worstFiberDiversity record target := by
    calc
      (values b).card = fiberTargetDiversity record target b := rfl
      _ <= worstFiberDiversity record target :=
        Finset.le_sup (f := fiberTargetDiversity record target)
          (Finset.mem_univ b)
  let exactLabel : X -> Fin (worstFiberDiversity record target) := fun x =>
    Fin.castLE (hcard (record x))
      ((values (record x)).equivFin ⟨target x, target_mem_values x⟩)
  have code_transport {leftFiber rightFiber : B}
      (sameFiber : leftFiber = rightFiber)
      (left : values leftFiber) (right : values rightFiber)
      (sameValue : left.1 = right.1) :
      Fin.castLE (hcard leftFiber) ((values leftFiber).equivFin left) =
        Fin.castLE (hcard rightFiber) ((values rightFiber).equivFin right) := by
    subst rightFiber
    have sameMember : left = right := Subtype.ext sameValue
    subst right
    rfl
  have exactLabel_determines : AppealDetermines record target exactLabel := by
    intro x y sameRecord sameLabel
    let target_y_at_x : values (record x) :=
      ⟨target y, by
        rw [sameRecord]
        exact target_mem_values y⟩
    dsimp only [exactLabel] at sameLabel
    have transported_y :
        Fin.castLE (hcard (record y))
            ((values (record y)).equivFin ⟨target y, target_mem_values y⟩) =
          Fin.castLE (hcard (record x))
            ((values (record x)).equivFin target_y_at_x) := by
      exact code_transport sameRecord.symm _ target_y_at_x rfl
    have sameIndex :
        Fin.castLE (hcard (record x))
            ((values (record x)).equivFin ⟨target x, target_mem_values x⟩) =
          Fin.castLE (hcard (record x))
            ((values (record x)).equivFin target_y_at_x) :=
      sameLabel.trans transported_y
    have sameMember :
        (⟨target x, target_mem_values x⟩ : values (record x)) =
          target_y_at_x := by
      apply (values (record x)).equivFin.injective
      exact Fin.castLE_injective (hcard (record x)) sameIndex
    exact congrArg Subtype.val sameMember
  refine ⟨⟨exactLabel, exactLabel_determines⟩, ?_⟩
  intro m label labelDetermines
  change Finset.univ.sup (fiberTargetDiversity record target) <= m
  apply Finset.sup_le
  intro b _b_mem
  change (fiberTargetValues record target b).card <= m
  let representative : fiberTargetValues record target b -> X := fun value =>
    Classical.choose (Finset.mem_image.mp value.property)
  have representative_mem (value : fiberTargetValues record target b) :
      representative value ∈ Finset.univ.filter (fun x => record x = b) :=
    (Classical.choose_spec (Finset.mem_image.mp value.property)).1
  have representative_target (value : fiberTargetValues record target b) :
      target (representative value) = value.1 :=
    (Classical.choose_spec (Finset.mem_image.mp value.property)).2
  have label_injective : Function.Injective (fun value => label (representative value)) := by
    intro left right sameRepresentativeLabel
    apply Subtype.ext
    have sameRecord : record (representative left) = record (representative right) :=
      (Finset.mem_filter.mp (representative_mem left)).2.trans
        (Finset.mem_filter.mp (representative_mem right)).2.symm
    have sameTarget := labelDetermines (representative left) (representative right)
      sameRecord sameRepresentativeLabel
    simpa only [representative_target left, representative_target right] using sameTarget
  simpa using Fintype.card_le_of_injective
    (fun value => label (representative value)) label_injective

/-- Two outcomes under one original record require exactly two appeal labels. -/
example :
    (exists label : Bool -> Fin 2,
      AppealDetermines (fun _ : Bool => ()) id label) /\
    (forall {m : Nat} (label : Bool -> Fin m),
      AppealDetermines (fun _ : Bool => ()) id label ->
        2 <= m) := by
  have diversity_is_two :
      worstFiberDiversity (fun _ : Bool => ()) (id : Bool -> Bool) = 2 := by
    simp [worstFiberDiversity, fiberTargetDiversity, fiberTargetValues]
  rcases minimal_appeal_label_count (fun _ : Bool => ()) id with
    ⟨⟨label, labelDetermines⟩, lowerBound⟩
  constructor
  · refine ⟨fun x => Fin.cast diversity_is_two (label x), ?_⟩
    intro x y sameRecord sameLabel
    exact labelDetermines x y sameRecord
      (Fin.cast_injective diversity_is_two sameLabel)
  · intro m label candidateDetermines
    rw [← diversity_is_two]
    exact lowerBound label candidateDetermines

#print axioms minimal_appeal_label_count

end D5.S3.ConceptDynamics.Appeal.MinimalAppealLabelCount
