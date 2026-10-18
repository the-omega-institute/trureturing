/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore]
   utility: none
   digest: Oriented whole-tree slot signatures transport paid execution and the original source law. -/


import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Probability.ProductMeasure

/-! Signatures include all potential read occurrences, with ordered branches,
terminal labels, phase parity, target and oriented spin slots distinguished. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Classical MeasureTheory

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

abbrev ReadPosition := List Bool
abbrev OrientedSlot := Option (ReadPosition × Bool)

namespace ReadTree

/-- False and true select the ordered zero and one branches. -/
def addressAt : ReadTree → ReadPosition → Option ℤ
  | .leaf _, _ => none
  | .read t _ _, [] => some t
  | .read _ z _, false :: p => z.addressAt p
  | .read _ _ o, true :: p => o.addressAt p

private def readPositions : ReadTree → Finset ReadPosition
  | .leaf _ => ∅
  | .read _ z o => insert []
      ((z.readPositions.image (List.cons false)) ∪ (o.readPositions.image (List.cons true)))

/-- Retain ordered branching, terminal labels and every node parity. -/
def paritySkeleton : ReadTree → ReadTree
  | .leaf a => .leaf a
  | .read t z o => .read (t % 2) z.paritySkeleton o.paritySkeleton

private theorem addressAt_mem (T : ReadTree) (p : ReadPosition) (t : ℤ)
    (h : T.addressAt p = some t) : p ∈ T.readPositions := by
  induction T generalizing p with
  | leaf a => simp [addressAt] at h
  | read a z o hz ho =>
    cases p with
    | nil => exact Finset.mem_insert_self _ _
    | cons b p =>
      cases b
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨p, hz p h, rfl⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨p, ho p h, rfl⟩))

theorem addressAt_skeleton (T : ReadTree) (p : ReadPosition) :
    T.paritySkeleton.addressAt p = (T.addressAt p).map (fun t => t % 2) := by
  induction T generalizing p with
  | leaf a => rfl
  | read t z o hz ho =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp only [paritySkeleton, addressAt, hz, ho]

end ReadTree

/-- Inactive or absent positions contribute redundant target slots. This total
indexing has the same equality data as restricting to active read positions. -/
def slotIndex (j φ : Bool) (T : ReadTree) : OrientedSlot → ℤ
  | none => targetIndex j φ
  | some (p, side) => match T.addressAt p with
    | none => targetIndex j φ
    | some t => if (t - φ.toInt) % 2 = 0 then
        (t - φ.toInt) / 2 + side.toInt else targetIndex j φ

/-- Full equality and inequality relations are recorded separately in each phase. -/
def SameSignature (j : Bool) (T T' : ReadTree) : Prop :=
  T.paritySkeleton = T'.paritySkeleton ∧
    ∀ φ : Bool, ∀ a b : OrientedSlot,
      (slotIndex j φ T a = slotIndex j φ T b ↔ slotIndex j φ T' a = slotIndex j φ T' b)

private theorem finite_slot_range (j φ : Bool) (T : ReadTree) :
    (Set.range (slotIndex j φ T)).Finite := by
  let slots : Finset OrientedSlot := insert none
    ((T.readPositions.product Finset.univ).image some)
  apply (slots.image (slotIndex j φ T)).finite_toSet.subset
  rintro z ⟨s, rfl⟩
  cases s with
  | none => exact Finset.mem_image.mpr ⟨none, Finset.mem_insert_self _ _, rfl⟩
  | some ps =>
    obtain ⟨p, side⟩ := ps
    cases ht : T.addressAt p with
    | none =>
      refine Finset.mem_image.mpr ⟨none, Finset.mem_insert_self _ _, ?_⟩
      simp only [slotIndex, ht]
    | some t =>
      exact Finset.mem_image.mpr ⟨some (p, side), Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(p, side), Finset.mem_product.mpr
          ⟨T.addressAt_mem p t ht, Finset.mem_univ _⟩, rfl⟩), rfl⟩

private theorem permutation_of_same_fibers {I : Type*} (f g : I → ℤ)
    (hf : (Set.range f).Finite) (h : ∀ a b, f a = f b ↔ g a = g b) :
    ∃ σ : Equiv.Perm ℤ, ∀ i, σ (f i) = g i := by
  letI := hf.fintype
  let rep : Set.range f → I := fun z => Classical.choose z.property
  have rep_spec (z : Set.range f) : f (rep z) = z := Classical.choose_spec z.property
  let gr : Set.range f → ℤ := fun z => g (rep z)
  have gr_injective : Function.Injective gr := by
    intro a b hab
    apply Subtype.ext
    have he := (h (rep a) (rep b)).mpr hab
    simpa only [rep_spec] using he
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun z : Set.range f => (z : ℤ)) gr Subtype.val_injective gr_injective
  refine ⟨σ, fun i => ?_⟩
  let z : Set.range f := ⟨f i, ⟨i, rfl⟩⟩
  exact (hσ z).trans ((h (rep z) i).mp (rep_spec z))

private theorem skeleton_execution_transport (T T' : ReadTree)
    (hshape : T.paritySkeleton = T'.paritySkeleton) (x y : ℤ → Bool)
    (hreplies : ∀ p t t', T.addressAt p = some t → T'.addressAt p = some t' → x t = y t') :
    (T.run x).output = (T'.run y).output ∧ (T.run x).paid = (T'.run y).paid := by
  induction T generalizing T' with
  | leaf a =>
    cases T' with
    | leaf b =>
      have : a = b := ReadTree.leaf.inj hshape
      subst b
      exact ⟨rfl, rfl⟩
    | read t z o => cases hshape
  | read t z o hz ho =>
    cases T' with
    | leaf b => cases hshape
    | read t' z' o' =>
      obtain ⟨hpar, hzero, hone⟩ := ReadTree.read.inj hshape
      have ht := hreplies [] t t' rfl rfl
      have hZ := hz z' hzero (fun p a b ha hb => hreplies (false :: p) a b ha hb)
      have hO := ho o' hone (fun p a b ha hb => hreplies (true :: p) a b ha hb)
      have out (a : ℤ) (b : Bool) (v : Execution) : (v.prepend a b).output = v.output := rfl
      simp only [ReadTree.run, ht]
      cases hy : y t' <;> simp only [hy, Bool.false_eq_true, ↓reduceIte, out,
        Execution.paid_prepend, hZ.1, hZ.2, hO.1, hO.2, and_self]

private theorem signature_observation_transport (j : Bool) (T T' : ReadTree)
    (h : SameSignature j T T') (φ : Bool) (σ : Equiv.Perm ℤ)
    (hσ : ∀ s, σ (slotIndex j φ T s) = slotIndex j φ T' s) (S : Spins) :
    observation j φ T (fun i => S (σ i)) = observation j φ T' S := by
  have htarget : σ (targetIndex j φ) = targetIndex j φ := hσ none
  have hrun := skeleton_execution_transport T T' h.1
    (visible φ (fun i => S (σ i))) (visible φ S) (by
      intro p t t' ht ht'
      have hs := congrArg (fun U : ReadTree => U.addressAt p) h.1
      rw [ReadTree.addressAt_skeleton, ReadTree.addressAt_skeleton, ht, ht'] at hs
      have hpar : t % 2 = t' % 2 := Option.some.inj hs
      by_cases active : (t - φ.toInt) % 2 = 0
      · have active' : (t' - φ.toInt) % 2 = 0 := by omega
        have hm := hσ (some (p, false))
        have hp := hσ (some (p, true))
        simp only [slotIndex, ht, ht', ite_eq_left active, ite_eq_left active',
          Bool.toInt_false, Bool.toInt_true, add_zero] at hm hp
        simp only [visible, ite_eq_left active, ite_eq_left active', hm, hp]
      · have active' : (t' - φ.toInt) % 2 ≠ 0 := by omega
        simp only [visible, ite_eq_right active, ite_eq_right active'])
  have hend : hidden φ (fun i => S (σ i)) j.toInt = hidden φ S j.toInt := by
    rw [actual_endpoint, actual_endpoint, htarget]
  simp only [observation, hend, hrun.1, hrun.2, Execution.returned]

private theorem spin_reindex_law (β : Bias) (σ : Equiv.Perm ℤ) :
    (spinLaw β).map (fun S : Spins => fun i => S (σ i)) = spinLaw β := by
  have hf : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => Bool) σ.symm) =
      (fun S : Spins => fun i => S (σ i)) := by
    funext S i
    simpa only [Equiv.symm_apply_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ℤ => Bool) σ.symm S (σ i)
  simpa only [spinLaw, hf] using
    Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => spinMarginal β) σ.symm

/-- Equality of whole signatures preserves the original full target/output/
return-indicator/paid-depth law, for every permitted bias. -/
theorem same_signature_observation_law (j : Bool) (T T' : ReadTree)
    (h : SameSignature j T T') (β : Bias) :
    (sourceLaw β).map (fun s => observation j s.1 T s.2) =
      (sourceLaw β).map (fun s => observation j s.1 T' s.2) := by
  have conditional (φ : Bool) :
      (spinLaw β).map (observation j φ T) = (spinLaw β).map (observation j φ T') := by
    obtain ⟨σ, hσ⟩ := permutation_of_same_fibers
      (slotIndex j φ T) (slotIndex j φ T') (finite_slot_range j φ T) (h.2 φ)
    have hm : Measurable (fun S : Spins => fun i => S (σ i)) := by fun_prop
    have hobs : Measurable (observation j φ T) :=
      (measurable_observation j T).comp (measurable_const.prodMk measurable_id)
    calc
      (spinLaw β).map (observation j φ T) =
          ((spinLaw β).map (fun S : Spins => fun i => S (σ i))).map (observation j φ T) := by
            rw [spin_reindex_law]
      _ = (spinLaw β).map (observation j φ T') := by
        rw [Measure.map_map hobs hm]
        congr 1
        funext S
        exact signature_observation_transport j T T' h φ σ hσ S
  ext B hB
  rw [Measure.map_apply (measurable_observation j T) hB,
    Measure.map_apply (measurable_observation j T') hB]
  rw [sourceLaw, Measure.prod_apply ((measurable_observation j T) hB),
    Measure.prod_apply ((measurable_observation j T') hB)]
  apply lintegral_congr
  intro φ
  have hobs (U : ReadTree) : Measurable (observation j φ U) :=
    (measurable_observation j U).comp (measurable_const.prodMk measurable_id)
  simpa only [Measure.map_apply (hobs T) hB, Measure.map_apply (hobs T') hB,
    Set.preimage_preimage, Function.comp_def]
    using congrArg (fun μ : Measure Observation => μ B) (conditional φ)

#print axioms same_signature_observation_law

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
