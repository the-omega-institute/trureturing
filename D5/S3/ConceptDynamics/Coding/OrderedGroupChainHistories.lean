/- GID: D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OrderedGroupChainHistories
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed ordered histories preserve group labels and original time. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.OrderedGroupChainHistories

open CountedGroupOverlap CountedGroupChainPaths EssentialWordRealization
open FixedBlockRigidity

universe u
variable {H : Type u} [Group H]

/-- The positive labels are listed in increasing time order. -/
def positiveLabels {n : ℕ} {A : GroupMat H n n} (x : Path A) : ℕ → List H
  | 0 => []
  | t + 1 => positiveLabels x t ++ [(x.val (t : ℤ)).label]

/-- The negative labels are inverted and listed in decreasing time order. -/
def negativeLabels {n : ℕ} {A : GroupMat H n n} (x : Path A) : ℕ → List H
  | 0 => []
  | t + 1 => negativeLabels x t ++ [(x.val (-((t + 1 : ℕ) : ℤ))).label⁻¹]

/-- The coordinate at zero is k; both signed tails use their actual ordered labels. -/
def anchoredCoordinate {n : ℕ} {A : GroupMat H n n} (x : Path A) (k : H) : ℤ → H
  | .ofNat t => k * (positiveLabels x t).prod
  | .negSucc t => k * (negativeLabels x (t + 1)).prod

@[simp] theorem anchored_zero {n : ℕ} {A : GroupMat H n n} (x : Path A) (k : H) :
    anchoredCoordinate x k 0 = k := by simp [anchoredCoordinate, positiveLabels]

private theorem anchored_positive_succ {n : ℕ} {A : GroupMat H n n}
    (x : Path A) (k : H) (t : ℕ) :
    anchoredCoordinate x k ((t + 1 : ℕ) : ℤ) =
      anchoredCoordinate x k (t : ℤ) * (x.val (t : ℤ)).label := by
  simp [anchoredCoordinate, positiveLabels, List.prod_append, mul_assoc]

private theorem anchored_negative_succ {n : ℕ} {A : GroupMat H n n}
    (x : Path A) (k : H) (t : ℕ) :
    anchoredCoordinate x k (-((t + 1 : ℕ) : ℤ)) =
      anchoredCoordinate x k (-(t : ℤ)) * (x.val (-((t + 1 : ℕ) : ℤ))).label⁻¹ := by
  have hc : -((t + 1 : ℕ) : ℤ) = Int.negSucc t := by omega
  rw [hc]
  cases t with
  | zero => simp [anchoredCoordinate, negativeLabels, positiveLabels]
  | succ t =>
    have hc' : -((t + 1 : ℕ) : ℤ) = Int.negSucc t := by omega
    rw [hc']
    simp [anchoredCoordinate, negativeLabels, List.prod_append, mul_assoc]
    exact congrArg (fun i => (x.val i).label) (by omega)

/-- This includes the seam from -1 to zero, without a periodicity premise. -/
theorem anchored_seam {n : ℕ} {A : GroupMat H n n}
    (x : Path A) (k : H) (t : ℤ) :
    anchoredCoordinate x k t * (x.val t).label = anchoredCoordinate x k (t + 1) := by
  cases t with
  | ofNat t => simpa using (anchored_positive_succ x k t).symm
  | negSucc t =>
    have h := anchored_negative_succ x k t
    have ht : -(↑(t + 1) : ℤ) + 1 = -(t : ℤ) := by omega
    have hc : Int.negSucc t = -((t + 1 : ℕ) : ℤ) := by omega
    rw [hc, ht]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      congrArg (fun g => g * (x.val (-((t + 1 : ℕ) : ℤ))).label) h

/-- The anchor and the one-step recurrence uniquely determine every signed coordinate. -/
theorem anchored_unique {n : ℕ} {A : GroupMat H n n}
    (x : Path A) (k : H) (g : ℤ → H) (h0 : g 0 = k)
    (hs : ∀ t, g t * (x.val t).label = g (t + 1)) :
    ∀ t, g t = anchoredCoordinate x k t := by
  have hp : ∀ t : ℕ, g (t : ℤ) = anchoredCoordinate x k (t : ℤ) := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ t ih =>
      rw [anchored_positive_succ, ← ih]
      simpa using (hs (t : ℤ)).symm
  have hn : ∀ t : ℕ, g (-(t : ℤ)) = anchoredCoordinate x k (-(t : ℤ)) := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ t ih =>
      rw [anchored_negative_succ, ← ih]
      have h := hs (-((t + 1 : ℕ) : ℤ))
      have ht : -(↑(t + 1) : ℤ) + 1 = -(t : ℤ) := by omega
      rw [ht] at h
      exact (eq_mul_inv_iff_mul_eq.mpr h)
  intro t
  cases t with
  | ofNat t => exact hp t
  | negSucc t => exact hn (t + 1)

/-- Forget only the evolving group coordinate; the numbered base edges are unchanged. -/
def forgetHistory {n : ℕ} {A : GroupMat H n n}
    (z : History (expandedGraph A)) : Path A :=
  ⟨fun t => (z.val t).1, fun t => congrArg Prod.fst (z.property t)⟩

/-- Lift an arbitrary legal base path from its group coordinate at zero. -/
def anchoredHistory {n : ℕ} {A : GroupMat H n n} (x : Path A) (k : H) :
    History (expandedGraph A) :=
  ⟨fun t => (x.val t, anchoredCoordinate x k t),
    fun t => Prod.ext (x.property t) (anchored_seam x k t)⟩

/-- The unrestricted anchored-coordinate equivalence on all integers. -/
def anchoredEquiv {n : ℕ} (A : GroupMat H n n) :
    History (expandedGraph A) ≃ Path A × H where
  toFun z := (forgetHistory z, (z.val 0).2)
  invFun p := anchoredHistory p.1 p.2
  left_inv z := by
    apply Subtype.ext
    funext t
    apply Prod.ext
    · rfl
    · exact (anchored_unique (forgetHistory z) (z.val 0).2 (fun i => (z.val i).2)
        rfl (fun i => congrArg Prod.snd (z.property i)) t).symm
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact anchored_zero p.1 p.2

section Topology
variable [TopologicalSpace H] [IsTopologicalGroup H]

private theorem positive_continuous {n : ℕ} {A : GroupMat H n n} (t : ℕ) :
    Continuous (fun x : Path A => (positiveLabels x t).prod) := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    simp only [positiveLabels, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    exact ih.mul ((continuous_of_discreteTopology : Continuous (Edge.label (M := A))).comp
      ((continuous_apply (t : ℤ)).comp continuous_subtype_val))

private theorem negative_continuous {n : ℕ} {A : GroupMat H n n} (t : ℕ) :
    Continuous (fun x : Path A => (negativeLabels x t).prod) := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    simp only [negativeLabels, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    exact ih.mul (((continuous_of_discreteTopology : Continuous (Edge.label (M := A))).comp
      ((continuous_apply (-((t + 1 : ℕ) : ℤ))).comp continuous_subtype_val)).inv)

private theorem anchored_continuous {n : ℕ} {A : GroupMat H n n} (t : ℤ) :
    Continuous (fun p : Path A × H => anchoredCoordinate p.1 p.2 t) := by
  cases t with
  | ofNat t => exact continuous_snd.mul ((positive_continuous t).comp continuous_fst)
  | negSucc t => exact continuous_snd.mul ((negative_continuous (t + 1)).comp continuous_fst)

/-- Signed reconstruction and forgetting are continuous for the product topology. -/
def anchoredHomeomorph {n : ℕ} (A : GroupMat H n n) :
    History (expandedGraph A) ≃ₜ Path A × H where
  toEquiv := anchoredEquiv A
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply continuous_pi
      intro t
      exact ((continuous_apply t).comp continuous_subtype_val).fst
    · exact ((continuous_apply (0 : ℤ)).comp continuous_subtype_val).snd
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (((continuous_apply t).comp (continuous_subtype_val.comp continuous_fst))).prodMk
      (anchored_continuous t)

/-- Anchored coordinates turn the positive one-step shift into the actual skew step. -/
theorem anchored_time {n : ℕ} (A : GroupMat H n n) (z : History (expandedGraph A)) :
    anchoredHomeomorph A (FiniteWindowTableCriterion.shift (expandedGraph A) z) =
      step A (anchoredHomeomorph A z) := by
  apply Prod.ext
  · rfl
  · exact (congrArg Prod.snd (z.property 0)).symm

end Topology

section OrderedSteps
variable [Fintype H] [LinearOrder H] {n m : ℕ}
variable (U : GroupMat H n m) (V : GroupMat H m n)
open FiniteWindowTableCriterion

@[simp] theorem ordered_split_join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    orderedSplit U V (orderedJoin U V a b h) = (a, b) := by
  rcases a with ⟨i, j, g, c⟩
  rcases b with ⟨j', k, l, d⟩
  cases h
  let e := Equiv.sigmaCongrRight (fun g => orderedFiberEquiv U V i k g)
  let p : Σ g : H, Fiber U V i k g := ⟨g * l, j, g, c, by simpa using d⟩
  let rebuild : (Σ g : H, Fiber U V i k g) → Edge U × Edge V := fun q =>
    (⟨i, q.2.1, q.2.2.1, q.2.2.2.1⟩, ⟨q.2.1, k, q.2.2.1⁻¹ * q.1, q.2.2.2.2⟩)
  change rebuild (e (e.symm p)) = _
  rw [Equiv.apply_symm_apply]
  simp [rebuild, p]

@[simp] theorem ordered_join_split (a : Edge (U * V)) :
    orderedJoin U V (orderedSplit U V a).1 (orderedSplit U V a).2 (by rfl) = a := by
  rcases a with ⟨i, k, g, c⟩
  let e := Equiv.sigmaCongrRight (fun g => orderedFiberEquiv U V i k g)
  let q := e ⟨g, c⟩
  let p : Σ g : H, Fiber U V i k g :=
    ⟨q.2.2.1 * (q.2.2.1⁻¹ * q.1), q.2.1, q.2.2.1, q.2.2.2.1,
      by simpa [mul_assoc] using q.2.2.2.2⟩
  have hp : p = q := by
    let rearrange : (Σ g : H, Fiber U V i k g) ≃
        Σ j : Fin m, Σ h : H, Fin ((U i j).coeff h) ×
          (Σ g : H, Fin ((V j k).coeff (h⁻¹ * g))) := {
      toFun z := ⟨z.2.1, z.2.2.1, z.2.2.2.1, z.1, z.2.2.2.2⟩
      invFun z := ⟨z.2.2.2.1, z.1, z.2.1, z.2.2.1, z.2.2.2.2⟩
      left_inv z := by rcases z with ⟨g,j,h,a,b⟩; rfl
      right_inv z := by rcases z with ⟨j,h,a,g,b⟩; rfl }
    apply rearrange.injective
    change (⟨q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.1 * (q.2.2.1⁻¹ * q.1), _⟩ :
      Σ j : Fin m, Σ h : H, Fin ((U i j).coeff h) ×
        (Σ g : H, Fin ((V j k).coeff (h⁻¹ * g)))) =
      ⟨q.2.1, q.2.2.1, q.2.2.2.1, q.1, q.2.2.2.2⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · rfl
        · apply Sigma.ext
          · simp
          · exact cast_heq _ q.2.2.2.2
  let rebuild : (Σ g : H, Fin (((U * V) i k).coeff g)) → Edge (U * V) :=
    fun z => ⟨i, k, z.1, z.2⟩
  change rebuild (e.symm p) = rebuild ⟨g, c⟩
  rw [hp, Equiv.symm_apply_apply]

private theorem ordered_split_label (a : Edge (U * V)) :
    (orderedSplit U V a).1.label * (orderedSplit U V a).2.label = a.label := by
  simp [orderedSplit]

/-- Every actual three-edge input has a legal forward seam. -/
theorem ordered_forward_seam : Seam (countedExpansion (U * V))
    (countedExpansion (V * U)) (orderedForward U V) := by
  have hjoin {a b : ℕ} (U : GroupMat H a b) (V : GroupMat H b a)
      (e : Edge U) (f : Edge V) (h : e.target = f.source) :
      (orderedJoin U V e f h).label = e.label * f.label := rfl
  intro w
  apply Prod.ext
  · rfl
  · change ((w.edge 0).2 * (orderedSplit U V (w.edge 0).1).1.label) *
        (orderedJoin V U (orderedSplit U V (w.edge 0).1).2
          (orderedSplit U V (w.edge 1).1).1 (congrArg Prod.fst (w.legal 0 (by decide)))).label =
      (w.edge 1).2 * (orderedSplit U V (w.edge 1).1).1.label
    rw [hjoin]
    have hs := congrArg Prod.snd (w.legal 0 (by decide))
    change (w.edge 0).2 * (w.edge 0).1.label = (w.edge 1).2 at hs
    rw [← mul_assoc, mul_assoc (w.edge 0).2, ordered_split_label, hs]

/-- The inverse seam uses the central coordinate and the preceding U half. -/
theorem ordered_backward_seam : Seam (countedExpansion (V * U))
    (countedExpansion (U * V)) (orderedBackward U V) := by
  have hjoin {a b : ℕ} (U : GroupMat H a b) (V : GroupMat H b a)
      (e : Edge U) (f : Edge V) (h : e.target = f.source) :
      (orderedJoin U V e f h).label = e.label * f.label := rfl
  intro w
  apply Prod.ext
  · rfl
  · change ((w.edge 1).2 * (orderedSplit V U (w.edge 0).1).2.label⁻¹) *
        (orderedJoin U V (orderedSplit V U (w.edge 0).1).2
          (orderedSplit V U (w.edge 1).1).1 (congrArg Prod.fst (w.legal 0 (by decide)))).label =
      (w.edge 2).2 * (orderedSplit V U (w.edge 1).1).2.label⁻¹
    rw [hjoin]
    have hs := congrArg Prod.snd (w.legal 1 (by decide))
    change (w.edge 1).2 * (w.edge 1).1.label = (w.edge 2).2 at hs
    rw [← hs, ← ordered_split_label V U (w.edge 1).1]
    simp [mul_assoc]

/-- Both centers are recovered by the same prescribed numbered-edge tables. -/
theorem ordered_local_criterion : LocalCriterion (orderedOverlapInput U V) := by
  refine ⟨ordered_forward_seam U V, ordered_backward_seam U V, ?_, ?_⟩
  · intro w
    apply Prod.ext
    · simp [orderedOverlapInput, orderedBackward, mapBlock, orderedForward, sliceWord]
    · simp only [orderedOverlapInput, orderedBackward, mapBlock, orderedForward, sliceWord,
        ordered_split_join]
      simp [mul_assoc]
  · intro w
    apply Prod.ext
    · simp [orderedOverlapInput, orderedForward, mapBlock, orderedBackward, sliceWord]
    · simp only [orderedOverlapInput, orderedForward, mapBlock, orderedBackward, sliceWord,
        ordered_split_join]
      simp [mul_assoc]

/-- The actual tables define a homeomorphism even when a history carrier is empty. -/
noncomputable def orderedHistoryHomeomorph [TopologicalSpace H] [DiscreteTopology H] :
    History (expandedGraph (U * V)) ≃ₜ History (expandedGraph (V * U)) where
  toFun := applyTable (a := 0) (b := 1) _ _ (orderedForward U V) (ordered_forward_seam U V)
  invFun := applyTable (a := 1) (b := 0) _ _ (orderedBackward U V) (ordered_backward_seam U V)
  left_inv := (inverse_of_local (orderedOverlapInput U V) (ordered_local_criterion U V)).1
  right_inv := (inverse_of_local (orderedOverlapInput U V) (ordered_local_criterion U V)).2
  continuous_toFun := applyTable_continuous _ _ _ _
  continuous_invFun := applyTable_continuous _ _ _ _

/-- Multiplication on the left acts on each group coordinate of a finite word. -/
def leftWord {a : ℕ} (A : GroupMat H a a) (h : H)
    {l : ℕ} (w : LegalWord (countedExpansion A) l) : LegalWord (countedExpansion A) l where
  edge i := ((w.edge i).1, h * (w.edge i).2)
  legal i hi := by
    apply Prod.ext
    · change (w.edge i).1.target = (w.edge ⟨i.val + 1, hi⟩).1.source
      exact congrArg Prod.fst (w.legal i hi)
    · change (h * (w.edge i).2) * (w.edge i).1.label = h * (w.edge ⟨i.val + 1, hi⟩).2
      simpa only [countedExpansion, mul_assoc] using congrArg (fun p => h * p.2) (w.legal i hi)

private theorem ordered_forward_group (h : H)
    (w : LegalWord (countedExpansion (U * V)) 2) :
    orderedForward U V (leftWord (U * V) h w) =
      ((orderedForward U V w).1, h * (orderedForward U V w).2) := by
  apply Prod.ext
  · rfl
  · simp [orderedForward, leftWord, mul_assoc]

private theorem ordered_backward_group (h : H)
    (w : LegalWord (countedExpansion (V * U)) 2) :
    orderedBackward U V (leftWord (V * U) h w) =
      ((orderedBackward U V w).1, h * (orderedBackward U V w).2) := by
  apply Prod.ext
  · rfl
  · simp [orderedBackward, leftWord, mul_assoc]

/-- The source base algorithm keeps the shared future U half-edge. -/
noncomputable def orderedBaseForward (x : Path (U * V)) : Path (V * U) :=
  ⟨fun i => orderedJoin V U (orderedSplit U V (x.val i)).2
      (orderedSplit U V (x.val (i + 1))).1 (x.property i), fun _ => rfl⟩

/-- The source inverse recovers U from i-1 and V from i. -/
noncomputable def orderedBaseBackward (y : Path (V * U)) : Path (U * V) :=
  ⟨fun i => orderedJoin U V (orderedSplit V U (y.val (i - 1))).2
      (orderedSplit V U (y.val i)).1 (by
        change (y.val (i - 1)).target = (y.val i).source
        simpa only [sub_add_cancel] using y.property (i - 1)),
    fun i => by
      change (orderedSplit V U (y.val i)).1.target =
        (orderedSplit V U (y.val (i + 1 - 1))).2.source
      have hi : i + 1 - 1 = i := by omega
      rw [hi]
      rfl⟩

private theorem base_left_inverse (x : Path (U * V)) :
    orderedBaseBackward U V (orderedBaseForward U V x) = x := by
  apply Subtype.ext
  funext i
  simp [orderedBaseForward, orderedBaseBackward]

private theorem base_right_inverse (y : Path (V * U)) :
    orderedBaseForward U V (orderedBaseBackward U V y) = y := by
  apply Subtype.ext
  funext i
  simp [orderedBaseForward, orderedBaseBackward]

/-- Both base algorithms act on the same numbered paths. -/
noncomputable def orderedBaseEquiv : Path (U * V) ≃ Path (V * U) where
  toFun := orderedBaseForward U V
  invFun := orderedBaseBackward U V
  left_inv := base_left_inverse U V
  right_inv := base_right_inverse U V

/-- The single-layer transfer is the actual label of the first U half at zero. -/
noncomputable def transfer (x : Path (U * V)) : H :=
  (orderedSplit U V (x.val 0)).1.label

private theorem base_shift (x : Path (U * V)) :
    orderedBaseForward U V (CountedGroupOverlap.shift (U * V) x) =
      CountedGroupOverlap.shift (V * U) (orderedBaseForward U V x) := by
  apply Subtype.ext
  funext i
  simp [orderedBaseForward, CountedGroupOverlap.shift, add_assoc]

/-- The current labels telescope across the prescribed ordered local split. -/
private theorem step_cocycle (x : Path (U * V)) :
    (x.val 0).label * transfer U V (CountedGroupOverlap.shift (U * V) x) =
      transfer U V x * ((orderedBaseForward U V x).val 0).label := by
  have hjoin {a b : ℕ} (U : GroupMat H a b) (V : GroupMat H b a)
      (e : Edge U) (f : Edge V) (h : e.target = f.source) :
      (orderedJoin U V e f h).label = e.label * f.label := rfl
  change (x.val 0).label * (orderedSplit U V (x.val (0 + 1))).1.label =
    (orderedSplit U V (x.val 0)).1.label *
      (orderedJoin V U (orderedSplit U V (x.val 0)).2
        (orderedSplit U V (x.val (0 + 1))).1 (x.property 0)).label
  rw [hjoin, ← ordered_split_label U V (x.val 0), mul_assoc]

section DiscreteTopology
variable [TopologicalSpace H] [DiscreteTopology H]

private theorem ordered_history_time (z : History (expandedGraph (U * V))) :
    orderedHistoryHomeomorph U V (FiniteWindowTableCriterion.shift _ z) =
      FiniteWindowTableCriterion.shift _ (orderedHistoryHomeomorph U V z) :=
  applyTable_shift (a := 0) (b := 1) _ _ (orderedForward U V) (ordered_forward_seam U V) z

private theorem ordered_history_group (h : H) (z : History (expandedGraph (U * V))) :
    orderedHistoryHomeomorph U V (groupHistory _ h z) =
      groupHistory _ h (orderedHistoryHomeomorph U V z) := by
  apply Subtype.ext
  funext i
  exact ordered_forward_group U V h (historyWindow _ z (i - 0) 2)

private theorem ordered_history_inverse_group (h : H) (z : History (expandedGraph (V * U))) :
    (orderedHistoryHomeomorph U V).symm (groupHistory _ h z) =
      groupHistory _ h ((orderedHistoryHomeomorph U V).symm z) := by
  apply Subtype.ext
  funext i
  exact ordered_backward_group U V h (historyWindow _ z (i - 1) 2)

/-- The exact anchored realization of the ordered overlap tables. -/
noncomputable def orderedSkewHomeomorph : Path (U * V) × H ≃ₜ Path (V * U) × H :=
  (anchoredHomeomorph (U * V)).symm.trans
    ((orderedHistoryHomeomorph U V).trans (anchoredHomeomorph (V * U)))

private theorem ordered_skew_apply (p : Path (U * V) × H) :
    orderedSkewHomeomorph U V p = (orderedBaseForward U V p.1, p.2 * transfer U V p.1) := by
  apply Prod.ext
  · apply Subtype.ext
    funext i
    simp [orderedSkewHomeomorph, anchoredHomeomorph, anchoredEquiv, forgetHistory,
      anchoredHistory, orderedHistoryHomeomorph, applyTable, historyWindow, orderedForward,
      orderedBaseForward]
  · simp [orderedSkewHomeomorph, anchoredHomeomorph, anchoredEquiv, anchoredHistory,
      orderedHistoryHomeomorph, applyTable, historyWindow, orderedForward, transfer]

private theorem ordered_skew_time (p : Path (U * V) × H) :
    orderedSkewHomeomorph U V (step (U * V) p) =
      step (V * U) (orderedSkewHomeomorph U V p) := by
  have ha : (anchoredHomeomorph (U * V)).symm (step (U * V) p) =
      FiniteWindowTableCriterion.shift _ ((anchoredHomeomorph (U * V)).symm p) := by
    apply (anchoredHomeomorph (U * V)).injective
    rw [Homeomorph.apply_symm_apply, anchored_time, Homeomorph.apply_symm_apply]
  simp only [orderedSkewHomeomorph, Homeomorph.trans_apply, ha,
    ordered_history_time, anchored_time]

private theorem ordered_skew_group (h : H) (p : Path (U * V) × H) :
    orderedSkewHomeomorph U V (EquivariantOverlapRecoding.translate h p) =
      EquivariantOverlapRecoding.translate h (orderedSkewHomeomorph U V p) := by
  have hanchor {a : ℕ} (A : GroupMat H a a) (h : H)
      (z : History (expandedGraph A)) :
      anchoredHomeomorph A (groupHistory A h z) =
        EquivariantOverlapRecoding.translate h (anchoredHomeomorph A z) := rfl
  have ha : (anchoredHomeomorph (U * V)).symm
      (EquivariantOverlapRecoding.translate h p) =
      groupHistory (U * V) h ((anchoredHomeomorph (U * V)).symm p) := by
    apply (anchoredHomeomorph (U * V)).injective
    rw [Homeomorph.apply_symm_apply, hanchor, Homeomorph.apply_symm_apply]
  simp only [orderedSkewHomeomorph, Homeomorph.trans_apply, ha,
    ordered_history_group, hanchor]

end DiscreteTopology
end OrderedSteps

section Chains
open FiniteWindowTableCriterion
variable [Fintype H] [LinearOrder H]

/-- The same ordered step transported through the supplied factor equalities. -/
noncomputable def factorBaseStep {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (U : GroupMat H n m) (V : GroupMat H m n) (hA : A = U * V) (hB : B = V * U) :
    Path A ≃ Path B := by
  cases hA
  cases hB
  exact orderedBaseEquiv U V

noncomputable def factorTransfer {n m : ℕ} {A : GroupMat H n n}
    (U : GroupMat H n m) (V : GroupMat H m n) (hA : A = U * V) (x : Path A) : H := by
  cases hA
  exact transfer U V x

/-- The base map is the composition of the original steps, in increasing layer order. -/
noncomputable def chainBaseEquiv : {n m L : ℕ} → {A : GroupMat H n n} →
    {B : GroupMat H m m} → (c : Chain H A B L) → Path A ≃ Path B
  | _, _, _, _, _, .nil _ => Equiv.refl _
  | _, _, _, _, _, .cons U V hA hB tail =>
      (factorBaseStep U V hA hB).trans (chainBaseEquiv tail)

/-- This list records each actual transfer at the path reached at that layer. -/
noncomputable def chainTransfers : {n m L : ℕ} → {A : GroupMat H n n} →
    {B : GroupMat H m m} → (c : Chain H A B L) → Path A → List H
  | _, _, _, _, _, .nil _, _ => []
  | _, _, _, _, _, .cons U V hA hB tail, x =>
      factorTransfer U V hA x :: chainTransfers tail (factorBaseStep U V hA hB x)

/-- Gamma is List.prod in the given layer order, with no commutative reordering. -/
noncomputable def chainGamma {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (x : Path A) : H := (chainTransfers c x).prod

section DiscreteTopology
variable [TopologicalSpace H] [DiscreteTopology H]

noncomputable def factorHistoryStep {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (U : GroupMat H n m) (V : GroupMat H m n) (hA : A = U * V) (hB : B = V * U) :
    History (expandedGraph A) ≃ₜ History (expandedGraph B) := by
  cases hA
  cases hB
  exact orderedHistoryHomeomorph U V

noncomputable def factorSkewStep {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (U : GroupMat H n m) (V : GroupMat H m n) (hA : A = U * V) (hB : B = V * U) :
    Path A × H ≃ₜ Path B × H := by
  cases hA
  cases hB
  exact orderedSkewHomeomorph U V

/-- The inverse applies the inverse of each original step in reverse layer order. -/
noncomputable def chainHistoryHomeomorph : {n m L : ℕ} → {A : GroupMat H n n} →
    {B : GroupMat H m m} → (c : Chain H A B L) →
    History (expandedGraph A) ≃ₜ History (expandedGraph B)
  | _, _, _, _, _, .nil _ => Homeomorph.refl _
  | _, _, _, _, _, .cons U V hA hB tail =>
      (factorHistoryStep U V hA hB).trans (chainHistoryHomeomorph tail)

/-- The product-coordinate construction composes these same actual ordered steps. -/
noncomputable def chainSkewHomeomorph : {n m L : ℕ} → {A : GroupMat H n n} →
    {B : GroupMat H m m} → (c : Chain H A B L) → Path A × H ≃ₜ Path B × H
  | _, _, _, _, _, .nil _ => Homeomorph.refl _
  | _, _, _, _, _, .cons U V hA hB tail =>
      (factorSkewStep U V hA hB).trans (chainSkewHomeomorph tail)

/-- The entire forward coordinate formula follows the actual ordered transfer list. -/
theorem chain_forward_formula {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (p : Path A × H) :
    chainSkewHomeomorph c p = (chainBaseEquiv c p.1, p.2 * chainGamma c p.1) := by
  induction c with
  | nil A => simp [chainSkewHomeomorph, chainBaseEquiv, chainGamma, chainTransfers]
  | cons U V hA hB tail ih =>
    cases hA
    cases hB
    simp only [chainSkewHomeomorph, Homeomorph.trans_apply, factorSkewStep,
      ordered_skew_apply, ih, chainBaseEquiv, factorBaseStep, Equiv.trans_apply,
      chainGamma, chainTransfers, factorTransfer, List.prod_cons]
    simp only [orderedBaseEquiv, Equiv.coe_fn_mk, mul_assoc]

/-- The displayed inverse uses the same Gamma evaluated at the recovered base path. -/
theorem chain_inverse_formula {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (p : Path B × H) :
    (chainSkewHomeomorph c).symm p =
      ((chainBaseEquiv c).symm p.1,
        p.2 * (chainGamma c ((chainBaseEquiv c).symm p.1))⁻¹) := by
  let q := (chainSkewHomeomorph c).symm p
  have hf := chain_forward_formula c q
  have hp : chainSkewHomeomorph c q = p := (chainSkewHomeomorph c).apply_symm_apply p
  have hb : q.1 = (chainBaseEquiv c).symm p.1 := by
    have h := congrArg Prod.fst (hf.symm.trans hp)
    exact (chainBaseEquiv c).injective (by simpa using h)
  apply Prod.ext
  · exact hb
  · have hk := congrArg Prod.snd (hf.symm.trans hp)
    change q.2 = _
    rw [← hb]
    exact eq_mul_inv_iff_mul_eq.mpr hk

/-- Anchored reconstruction identifies the expanded and product implementations exactly. -/
theorem chain_anchored_formula {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (z : History (expandedGraph A)) :
    anchoredHomeomorph B (chainHistoryHomeomorph c z) =
      chainSkewHomeomorph c (anchoredHomeomorph A z) := by
  induction c with
  | nil A => rfl
  | cons U V hA hB tail ih =>
    cases hA
    cases hB
    simp only [chainHistoryHomeomorph, chainSkewHomeomorph, Homeomorph.trans_apply,
      factorHistoryStep, factorSkewStep, ih, orderedSkewHomeomorph,
      Homeomorph.symm_apply_apply]

/-- Every original layer commutes with the positive one-step time action. -/
theorem chain_time {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (p : Path A × H) :
    chainSkewHomeomorph c (step A p) = step B (chainSkewHomeomorph c p) := by
  induction c with
  | nil A => rfl
  | cons U V hA hB tail ih =>
    cases hA
    cases hB
    simp only [chainSkewHomeomorph, Homeomorph.trans_apply, factorSkewStep,
      ordered_skew_time, ih]

/-- Left multiplication commutes with the actual ordered chain code. -/
theorem chain_group {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (h : H) (p : Path A × H) :
    chainSkewHomeomorph c (EquivariantOverlapRecoding.translate h p) =
      EquivariantOverlapRecoding.translate h (chainSkewHomeomorph c p) := by
  induction c with
  | nil A => rfl
  | cons U V hA hB tail ih =>
    cases hA
    cases hB
    simp only [chainSkewHomeomorph, Homeomorph.trans_apply, factorSkewStep,
      ordered_skew_group, ih]

/-- The base algorithm is a homeomorphism, with the same past-aligned inverse. -/
noncomputable def chainBaseHomeomorph {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) : Path A ≃ₜ Path B where
  toEquiv := chainBaseEquiv c
  continuous_toFun := by
    have hc := continuous_fst.comp ((anchoredHomeomorph B).continuous.comp
      ((chainHistoryHomeomorph c).continuous.comp ((anchoredHomeomorph A).symm.continuous.comp
        (continuous_id.prodMk (continuous_const (y := (1 : H)))))))
    convert hc using 1
    funext x
    simpa only [Equiv.toFun_as_coe, Function.comp_apply, id_eq, Homeomorph.apply_symm_apply, chain_forward_formula] using
      (congrArg Prod.fst (chain_anchored_formula c ((anchoredHomeomorph A).symm (x, 1)))).symm
  continuous_invFun := by
    have hc := continuous_fst.comp ((chainSkewHomeomorph c).symm.continuous.comp
      (continuous_id.prodMk (continuous_const (y := (1 : H)))))
    convert hc using 1
    funext y
    exact (congrArg Prod.fst (chain_inverse_formula c (y, 1))).symm

/-- Exact noncommutative telescoping, with no periodic or positive-length condition. -/
theorem chain_cocycle {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (x : Path A) :
    (x.val 0).label * chainGamma c (CountedGroupOverlap.shift A x) =
      chainGamma c x * ((chainBaseHomeomorph c x).val 0).label := by
  change (x.val 0).label * chainGamma c (CountedGroupOverlap.shift A x) =
    chainGamma c x * ((chainBaseEquiv c x).val 0).label
  induction c with
  | nil A => simp [chainGamma, chainTransfers, chainBaseEquiv]
  | cons U V hA hB tail ih =>
    cases hA
    cases hB
    change (x.val 0).label *
        (transfer U V (CountedGroupOverlap.shift (U * V) x) *
          chainGamma tail (orderedBaseForward U V (CountedGroupOverlap.shift (U * V) x))) =
      (transfer U V x * chainGamma tail (orderedBaseForward U V x)) *
        ((chainBaseEquiv tail (orderedBaseForward U V x)).val 0).label
    rw [base_shift, ← mul_assoc, step_cocycle, mul_assoc, ih, ← mul_assoc]

/-- The continuous transfer function is the actual finite ordered product. -/
theorem chain_gamma_continuous {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) : Continuous (chainGamma c) := by
  have hc := continuous_snd.comp ((chainSkewHomeomorph c).continuous.comp
    (continuous_id.prodMk (continuous_const (y := (1 : H)))))
  convert hc using 1
  funext x
  simpa using (congrArg Prod.snd (chain_forward_formula c (x, 1))).symm

/-- Expanded time is the original positive shift, independently at every layer. -/
theorem chain_history_time {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (z : History (expandedGraph A)) :
    chainHistoryHomeomorph c (FiniteWindowTableCriterion.shift _ z) =
      FiniteWindowTableCriterion.shift _ (chainHistoryHomeomorph c z) := by
  induction c with
  | nil A => rfl
  | cons U V hA hB tail ih =>
    cases hA
    cases hB
    simp only [chainHistoryHomeomorph, Homeomorph.trans_apply, factorHistoryStep,
      ordered_history_time, ih]

/-- Both expanded directions preserve the actual left action. -/
theorem chain_history_group {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (h : H) :
    (∀ z, chainHistoryHomeomorph c (groupHistory A h z) =
      groupHistory B h (chainHistoryHomeomorph c z)) ∧
    (∀ z, (chainHistoryHomeomorph c).symm (groupHistory B h z) =
      groupHistory A h ((chainHistoryHomeomorph c).symm z)) := by
  induction c with
  | nil A => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @cons n k m L A B C U V hA hB tail ih =>
    cases hA
    cases hB
    constructor
    · intro z
      simp only [chainHistoryHomeomorph, Homeomorph.trans_apply, factorHistoryStep,
        ordered_history_group, ih.1]
    · intro z
      change (orderedHistoryHomeomorph U V).symm
        ((chainHistoryHomeomorph tail).symm (groupHistory C h z)) =
        groupHistory (U * V) h ((orderedHistoryHomeomorph U V).symm
          ((chainHistoryHomeomorph tail).symm z))
      rw [ih.2, ordered_history_inverse_group]

private theorem ordered_history_forward_window {n m : ℕ}
    (U : GroupMat H n m) (V : GroupMat H m n) {a b : History (expandedGraph (U * V))} (i : ℤ)
    (h0 : a.val i = b.val i) (h1 : a.val (i + 1) = b.val (i + 1)) :
    (orderedHistoryHomeomorph U V a).val i = (orderedHistoryHomeomorph U V b).val i := by
  change orderedForward U V (FiniteWindowTableCriterion.historyWindow _ a (i - 0) 2) =
    orderedForward U V (FiniteWindowTableCriterion.historyWindow _ b (i - 0) 2)
  congr 1
  apply FiniteWindowTableCriterion.legalWord_ext
  funext t
  fin_cases t
  · simpa [FiniteWindowTableCriterion.historyWindow] using h0
  · simpa [FiniteWindowTableCriterion.historyWindow] using h1

private theorem ordered_history_backward_window {n m : ℕ}
    (U : GroupMat H n m) (V : GroupMat H m n) {a b : History (expandedGraph (V * U))} (i : ℤ)
    (h0 : a.val (i - 1) = b.val (i - 1)) (h1 : a.val i = b.val i) :
    ((orderedHistoryHomeomorph U V).symm a).val i =
      ((orderedHistoryHomeomorph U V).symm b).val i := by
  change orderedBackward U V (FiniteWindowTableCriterion.historyWindow _ a (i - 1) 2) =
    orderedBackward U V (FiniteWindowTableCriterion.historyWindow _ b (i - 1) 2)
  congr 1
  apply FiniteWindowTableCriterion.legalWord_ext
  funext t
  fin_cases t
  · simpa [FiniteWindowTableCriterion.historyWindow] using h0
  · simpa [FiniteWindowTableCriterion.historyWindow] using h1

/-- Direct forward-algorithm induction gives exactly the interval [i,i+L]. -/
theorem chain_forward_window {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (z w : History (expandedGraph A)) (i : ℤ)
    (h : ∀ t : ℤ, i ≤ t → t ≤ i + (L : ℤ) → z.val t = w.val t) :
    (chainHistoryHomeomorph c z).val i = (chainHistoryHomeomorph c w).val i := by
  induction c generalizing i with
  | nil A => exact h i (by omega) (by omega)
  | @cons n k m L A B C U V hA hB tail ih =>
    cases hA
    cases hB
    change (chainHistoryHomeomorph tail (orderedHistoryHomeomorph U V z)).val i =
      (chainHistoryHomeomorph tail (orderedHistoryHomeomorph U V w)).val i
    apply ih
    intro t ht0 ht1
    apply ordered_history_forward_window U V t
    · exact h t ht0 (by omega)
    · exact h (t + 1) (by omega) (by omega)

/-- Direct reverse-layer induction gives the inverse interval [i-L,i]. -/
theorem chain_inverse_window {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (z w : History (expandedGraph B)) (i : ℤ)
    (h : ∀ t : ℤ, i - (L : ℤ) ≤ t → t ≤ i → z.val t = w.val t) :
    ((chainHistoryHomeomorph c).symm z).val i = ((chainHistoryHomeomorph c).symm w).val i := by
  induction c generalizing i with
  | nil A => exact h i (by omega) (by omega)
  | @cons n k m L A B C U V hA hB tail ih =>
    cases hA
    cases hB
    change ((orderedHistoryHomeomorph U V).symm ((chainHistoryHomeomorph tail).symm z)).val i =
      ((orderedHistoryHomeomorph U V).symm ((chainHistoryHomeomorph tail).symm w)).val i
    apply ordered_history_backward_window U V i
    · apply ih
      intro t ht0 ht1
      exact h t (by omega) (by omega)
    · apply ih
      intro t ht0 ht1
      exact h t (by omega) ht1

end DiscreteTopology

private theorem ordered_base_window {n m : ℕ} (U : GroupMat H n m) (V : GroupMat H m n)
    (x y : Path (U * V)) (i : ℤ) (h0 : x.val i = y.val i)
    (h1 : x.val (i + 1) = y.val (i + 1)) :
    (orderedBaseForward U V x).val i = (orderedBaseForward U V y).val i := by
  dsimp only [orderedBaseForward]
  simp only [h0, h1]

/-- The transfer list uses exactly the initial base window [0,L-1], including L=0. -/
theorem chain_gamma_window {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    (c : Chain H A B L) (x y : Path A)
    (h : ∀ t : ℤ, 0 ≤ t → t ≤ (L : ℤ) - 1 → x.val t = y.val t) :
    chainGamma c x = chainGamma c y := by
  induction c with
  | nil A => rfl
  | @cons n k m L A B C U V hA hB tail ih =>
    cases hA
    cases hB
    change transfer U V x * chainGamma tail (orderedBaseForward U V x) =
      transfer U V y * chainGamma tail (orderedBaseForward U V y)
    congr 1
    · unfold transfer
      rw [h 0 (by omega) (by omega)]
    · apply ih
      intro t ht0 ht1
      apply ordered_base_window U V x y t
      · exact h t ht0 (by omega)
      · exact h (t + 1) (by omega) (by omega)

end Chains

#print axioms anchoredHomeomorph
#print axioms orderedHistoryHomeomorph
#print axioms chainHistoryHomeomorph
#print axioms chainSkewHomeomorph
#print axioms chainBaseHomeomorph
#print axioms chain_gamma_continuous
#print axioms chain_forward_formula
#print axioms chain_inverse_formula
#print axioms chain_anchored_formula
#print axioms chain_time
#print axioms chain_group
#print axioms chain_history_time
#print axioms chain_history_group
#print axioms chain_cocycle
#print axioms chain_forward_window
#print axioms chain_inverse_window
#print axioms chain_gamma_window

end D5.S3.ConceptDynamics.Coding.OrderedGroupChainHistories
