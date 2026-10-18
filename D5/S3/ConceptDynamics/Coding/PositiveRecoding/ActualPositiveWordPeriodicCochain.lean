/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual-history charts, endpoint-corrected positive-word gyration and signed time translation. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.CountedRelativeGyrationTransport
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.TypedPositiveSplitWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ActualPositiveWordPeriodicCochain
open scoped BigOperators
open EssentialWordRealization TwoSidedFiniteInduction
open TypedPositiveSplitWord ZeroWindowRelabeling
open CountedMatrixOverlap (CountMat Path)
open CountedOrderTypeGyration
open CountedRelativeGyrationTransport
open SplitTowerTranslation
open StandardBeamHomeomorphisms (translate translate_add translate_zero)

/-- Use the already supplied full outgoing edge identification as a chart.
It is bijective on EVERY vertex and parallel edge, including empty fibres. -/
def matrix (F : Presentation) : CountMat (Fintype.card F.V) (Fintype.card F.V) :=
  OutSplitNumberedRecoding.R F.graph (id : F.E → F.E) *
    OutSplitNumberedRecoding.S F.graph (id : F.E → F.E)

def chart (F : Presentation) : Relabel (countedGraph (matrix F)) F.graph := outOld F F id

private theorem chart_iterate (F : Presentation) (q : ℕ) (x : Path (matrix F)) :
    (chart F).homeomorph ((CountedMatrixOverlap.shift (matrix F))^[q] x) =
      (FiniteWindowTableCriterion.shift F.graph)^[q] ((chart F).homeomorph x) := by
  have h : Function.Semiconj (chart F).homeomorph
      (CountedMatrixOverlap.shift (matrix F)) (FiniteWindowTableCriterion.shift F.graph) :=
    fun x => relabel_homeomorph_time (chart F) 1 x
  exact h.iterate_right q x

private theorem chart_minimalPeriod (F : Presentation) (x : Path (matrix F)) :
    Function.minimalPeriod (FiniteWindowTableCriterion.shift F.graph) ((chart F).homeomorph x) =
      Function.minimalPeriod (CountedMatrixOverlap.shift (matrix F)) x := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro q
  change (FiniteWindowTableCriterion.shift F.graph)^[q] ((chart F).homeomorph x) =
    (chart F).homeomorph x ↔ (CountedMatrixOverlap.shift (matrix F))^[q] x = x
  rw [← chart_iterate]
  exact (chart F).homeomorph.injective.eq_iff




/-- The carrier is the actual original signed history, with its true forward
minimal period; it is not a residue word or a quotient of edge identities. -/
abbrev Primitive (F : Presentation) (d : ℕ) :=
  {x : Hist F // Function.minimalPeriod (FiniteWindowTableCriterion.shift F.graph) x = d}

def primitiveChart (F : Presentation) (d : ℕ) : PrimitivePath (matrix F) d ≃ Primitive F d where
  toFun x := ⟨(chart F).homeomorph x.val,(chart_minimalPeriod F x.val).trans x.property⟩
  invFun x := ⟨(chart F).homeomorph.symm x.val,by
    have h := chart_minimalPeriod F ((chart F).homeomorph.symm x.val)
    rw [(chart F).homeomorph.apply_symm_apply,x.property] at h
    exact h.symm⟩
  left_inv x := Subtype.ext ((chart F).homeomorph.symm_apply_apply x.val)
  right_inv x := Subtype.ext ((chart F).homeomorph.apply_symm_apply x.val)


/-- Pull back the EXISTING orbit relation through the actual primitive chart.
Chart equivariance identifies it with forward reachability on actual histories. -/
def orbitSetoid (F : Presentation) (d : ℕ) [NeZero d] : Setoid (Primitive F d) :=
  Setoid.comap (primitiveChart F d).symm (actualPathOrbitSetoid (matrix F))

abbrev Orbit (F : Presentation) (d : ℕ) [NeZero d] := Quotient (orbitSetoid F d)

def orbitChart (F : Presentation) (d : ℕ) [NeZero d] :
    ActualPathOrbit (matrix F) d ≃ Orbit F d where
  toFun := Quotient.map (primitiveChart F d) (by
    intro x y h
    change SamePathOrbit ((primitiveChart F d).symm (primitiveChart F d x))
      ((primitiveChart F d).symm (primitiveChart F d y))
    change SamePathOrbit x y at h
    simpa only [Equiv.symm_apply_apply] using h)
  invFun := Quotient.map (primitiveChart F d).symm (fun _ _ h => h)
  left_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ ((primitiveChart F d).symm (primitiveChart F d x)) = _
    rw [Equiv.symm_apply_apply]
  right_inv o := by
    refine Quotient.inductionOn o ?_
    intro x
    change Quotient.mk _ (primitiveChart F d ((primitiveChart F d).symm x)) = _
    rw [Equiv.apply_symm_apply]

instance orbitFintype (F : Presentation) (d : ℕ) [NeZero d] : Fintype (Orbit F d) :=
  Fintype.ofEquiv _ (orbitChart F d)




/-- Transport a given actual history equivalence into the fixed counted
charts. Equivariance is an actual coordinate theorem of the supplied maps. -/
def inCharts {F H : Presentation} (P : Hist F ≃ Hist H)
    (hP : ∀ s x, P (time F.graph s x) = time H.graph s (P x)) :
    TimedEquiv (matrix F) (matrix H) where
  equiv := (chart F).homeomorph.toEquiv.trans (P.trans (chart H).homeomorph.symm.toEquiv)
  time s x := by
    change (chart H).homeomorph.symm
      (P ((chart F).homeomorph (time _ s x))) = _
    rw [relabel_homeomorph_time,hP,relabel_inverse_time]
    rfl

def relabelMap {F H : Presentation} (r : Relabel F.graph H.graph) :
    TimedEquiv (matrix F) (matrix H) :=
  inCharts r.homeomorph.toEquiv (relabel_homeomorph_time r)

/-- Comparison from the precise ranked R*S (or S*R) basis into F's fixed
basis. The actual r.edge and r.vertex are used; this number need not be zero. -/
def chartComparison {F : Presentation} {n : ℕ} {A : CountMat n n}
    (r : Relabel (countedGraph A) F.graph) : TimedEquiv A (matrix F) where
  equiv := r.homeomorph.toEquiv.trans (chart F).homeomorph.symm.toEquiv
  time s x := by
    change (chart F).homeomorph.symm (r.homeomorph (time _ s x)) = _
    rw [relabel_homeomorph_time,relabel_inverse_time]
    rfl

def wordMap {F H : Presentation} (w : Word F H) : TimedEquiv (matrix F) (matrix H) :=
  inCharts w.eval.toEquiv (Word.eval_time w)




theorem wordMap_comp {F H K : Presentation} (u : Word F H) (v : Word H K) :
    wordMap (.comp u v) = (wordMap u).comp (wordMap v) := by
  apply TimedEquiv.ext
  intro x
  change (chart K).homeomorph.symm (v.eval (u.eval ((chart F).homeomorph x))) =
    (chart K).homeomorph.symm (v.eval ((chart H).homeomorph
      ((chart H).homeomorph.symm (u.eval ((chart F).homeomorph x)))))
  rw [(chart H).homeomorph.apply_symm_apply]

theorem wordMap_positive {F H : Presentation} {n m : ℕ}
    (R : CountMat n m) (S : CountMat m n)
    (old : Relabel (counted (R*S)) F.graph) (next : Relabel (counted (S*R)) H.graph) :
    wordMap (Word.positive R S old next) =
      ((chartComparison old).symm.comp (TimedEquiv.elementary R S)).comp (chartComparison next) := by
  apply TimedEquiv.ext
  intro x
  rfl

/-- The full endpoint correction. Dropping either comparison term would
change the actual ordinary positive letter. -/
theorem positive_gyration {F H : Presentation} {n m : ℕ}
    (R : CountMat n m) (S : CountMat m n)
    (old : Relabel (counted (R*S)) F.graph) (next : Relabel (counted (S*R)) H.graph)
    (d : ℕ) [NeZero d] :
    (wordMap (Word.positive R S old next)).gyration d =
      -(chartComparison old).gyration d + relativeForwardGyration (d := d) R S +
        (chartComparison next).gyration d := by
  rw [wordMap_positive,TimedEquiv.gyration_basis_change,
    TimedEquiv.gyration_symm,TimedEquiv.gyration_elementary]

/-- Actual finite cochain, with the relabeling term at EVERY relabel leaf and
both ranked-basis corrections at EVERY positive leaf. -/
def cochain (d : ℕ) [NeZero d] : ∀ {F H : Presentation}, Word F H → ZMod d
  | _,_,.relabel r => (relabelMap r).gyration d
  | _,_,.positive R S old next =>
      -(chartComparison old).gyration d + relativeForwardGyration (d := d) R S +
        (chartComparison next).gyration d
  | _,_,.comp u v => cochain d u+cochain d v

theorem word_gyration : ∀ {F H : Presentation} (w : Word F H) (d : ℕ) [NeZero d],
    (wordMap w).gyration d = cochain d w
  | _,_,.relabel r,d,_ => rfl
  | _,_,.positive R S old next,d,_ => positive_gyration R S old next d
  | _,_,.comp u v,d,_ => by
      rw [wordMap_comp,TimedEquiv.gyration_comp,word_gyration u,word_gyration v] <;> rfl

def reduceSix : ZMod 6 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3)

/-- Intrinsic loop gyration, written in an existing finite actual-history
chart. The conjugacy law proves chart independence; representative boundary
cancellation is recorded in the accompanying repair exposition. -/
def historyGyration {F : Presentation} (h : Hist F ≃ Hist F)
    (ht : ∀ s x, h (time F.graph s x) = time F.graph s (h x))
    (d : ℕ) [NeZero d] : ZMod d := (inCharts h ht).gyration d

/-- Transfer primitive-history agreement through the SAME existing chart
at both ends. No comparison between different choices of charts is used. -/
theorem historyGyration_congr_on_primitive {F : Presentation}
    (h k : Hist F ≃ Hist F)
    (ht : ∀ s x, h (time F.graph s x) = time F.graph s (h x))
    (kt : ∀ s x, k (time F.graph s x) = time F.graph s (k x))
    (d : ℕ) [NeZero d]
    (hag : ∀ x : Primitive F d, h x.val = k x.val) :
    historyGyration h ht d = historyGyration k kt d := by
  unfold historyGyration
  apply TimedEquiv.gyration_congr
  intro x
  change (chart F).homeomorph.symm (h ((chart F).homeomorph x.val)) =
    (chart F).homeomorph.symm (k ((chart F).homeomorph x.val))
  exact congrArg (chart F).homeomorph.symm (hag (primitiveChart F d x))

theorem time_corrected_word {F : Presentation} (w : Word F F) (s : ℤ)
    (h : Hist F ≃ Hist F)
    (ht : ∀ t x, h (time F.graph t x) = time F.graph t (h x))
    (hh : ∀ x, h x = time F.graph s (w.eval x)) (d : ℕ) [NeZero d] :
    historyGyration h ht d = cochain d w + (Fintype.card (Orbit F d) : ZMod d)*(s : ZMod d) := by
  have he : inCharts h ht = (wordMap w).comp (TimedEquiv.timeEquiv (matrix F) s) := by
    apply TimedEquiv.ext
    intro x
    change (chart F).homeomorph.symm (h ((chart F).homeomorph x)) =
      time (countedGraph (matrix F)) s
        ((chart F).homeomorph.symm (w.eval ((chart F).homeomorph x)))
    rw [hh,relabel_inverse_time]
  rw [historyGyration,he,TimedEquiv.gyration_comp,word_gyration,TimedEquiv.gyration_time]
  rw [Fintype.card_congr (orbitChart F d)]




end D5.S3.ConceptDynamics.Coding.ActualPositiveWordPeriodicCochain
