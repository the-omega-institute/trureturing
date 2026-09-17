/- GID: D5/S3/Arith/Congruence/ExactForestMessages
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ExactForestMessages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact bottom-up messages characterize simultaneous avoidance on finite forests. -/

import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.ExactForestMessages

open Classical in
/-- Exact bottom-up messages characterize feasibility on every finite forest.
The level is any strictly increasing parent-to-child ranking.
A child's message consists of the parent values that conflict with
every surviving child value. A simultaneous assignment exists exactly when
all root residual sets are nonempty. -/
theorem exact_forest_message_feasibility
    {V Y : Type*} [Fintype V] [DecidableEq Y]
    (parent : V → Option V) (level : V → ℕ)
    (parent_level : ∀ v p, parent v = some p → level p < level v)
    (domain pureBad : V → Finset Y) (forbidden : V → Y → Y → Prop) :
    ∃ (allowed : V → Finset Y) (message : V → Set Y),
      (∀ v, message v = {y | ∀ z ∈ allowed v, forbidden v y z}) ∧
      (∀ v, allowed v = (domain v \ pureBad v).filter
        (fun y => ∀ w, parent w = some v → y ∉ message w)) ∧
      ((∃ value : V → Y,
          (∀ v, value v ∈ domain v ∧ value v ∉ pureBad v) ∧
          ∀ v p, parent v = some p → ¬forbidden v (value p) (value v)) ↔
        ∀ v, parent v = none → (allowed v).Nonempty) := by
  classical
  let reverseLevel : V → ℕ := fun v => Finset.univ.sup level - level v
  have child_reverse_level (w v : V) (hw : parent w = some v) :
      reverseLevel w < reverseLevel v := by
    have hle : level w ≤ Finset.univ.sup level := Finset.le_sup (f := level) (Finset.mem_univ w)
    have hlt := parent_level w v hw
    dsimp [reverseLevel]
    omega
  let build : ∀ v : V, (∀ w : V, reverseLevel w < reverseLevel v → Finset Y) → Finset Y :=
    fun v previous => (domain v \ pureBad v).filter fun y =>
      ∀ w (hw : parent w = some v),
        ∃ z ∈ previous w (child_reverse_level w v hw), ¬forbidden w y z
  let allowed : V → Finset Y := (measure reverseLevel).wf.fix build
  have allowed_eq (v : V) :
      allowed v = (domain v \ pureBad v).filter (fun y =>
        ∀ w, parent w = some v → ∃ z ∈ allowed w, ¬forbidden w y z) := by
    exact (measure reverseLevel).wf.fix_eq build v
  let message : V → Set Y := fun v => {y | ∀ z ∈ allowed v, forbidden v y z}
  refine ⟨allowed, message, fun _ => rfl, ?_, ?_⟩
  · intro v
    rw [allowed_eq]
    ext y
    simp only [Finset.mem_filter, message, Set.mem_ofPred_eq, not_forall, exists_prop]
  · constructor
    · rintro ⟨value, hnode, hedge⟩
      have survives : ∀ v, value v ∈ allowed v := by
        intro v
        induction v using (measure reverseLevel).wf.induction with
        | h v ih =>
          rw [allowed_eq]
          refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr (hnode v), ?_⟩
          intro w hw
          exact ⟨value w, ih w (child_reverse_level w v hw), hedge w v hw⟩
      exact fun v _ => ⟨value v, survives v⟩
    · intro roots_nonempty
      have compatible (v p : V) (hp : parent v = some p)
          (y : {y // y ∈ allowed p}) :
          ∃ z, z ∈ allowed v ∧ ¬forbidden v y.val z := by
        have hy := (congrArg (fun s : Finset Y => y.val ∈ s) (allowed_eq p)).mp y.property
        exact (Finset.mem_filter.mp hy).2 v hp
      let next (v p : V) (hp : parent v = some p) (y : {y // y ∈ allowed p}) :
          {z // z ∈ allowed v ∧ ¬forbidden v y.val z} :=
        ⟨Classical.choose (compatible v p hp y), Classical.choose_spec (compatible v p hp y)⟩
      let extend : ∀ v : V,
          (∀ p : V, level p < level v → {y // y ∈ allowed p}) → {y // y ∈ allowed v} :=
        fun v previous =>
          match hp : parent v with
          | none => ⟨(roots_nonempty v hp).choose, (roots_nonempty v hp).choose_spec⟩
          | some p =>
            let z := next v p hp (previous p (parent_level v p hp))
            ⟨z.val, z.property.1⟩
      let assignment (v : V) : {y // y ∈ allowed v} := (measure level).wf.fix extend v
      refine ⟨fun v => (assignment v).val, ?_, ?_⟩
      · intro v
        have hy := (congrArg (fun s : Finset Y => (assignment v).val ∈ s)
          (allowed_eq v)).mp (assignment v).property
        exact Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1
      · intro v p hp
        change ¬forbidden v (assignment p).val (((measure level).wf.fix extend v).val)
        rw [(measure level).wf.fix_eq extend v]
        simp only [extend]
        split
        · next hnone => simp [hp] at hnone
        · next p' hp' =>
            have heq : p' = p := Option.some.inj (hp'.symm.trans hp)
            subst p'
            exact (next v p hp (assignment p)).property.2

#print axioms exact_forest_message_feasibility

end D5.S3.Arith.Congruence.ExactForestMessages
