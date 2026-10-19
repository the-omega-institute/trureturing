/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit-factor recodings retain the original parallel-edge rank. -/

/- Unit-factor recodings preserve the original edge number. The ranking argument reuses Finset.orderEmbOfFin_unique and fiber_number_lt_iff, including empty fibers. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.CountedRelativeGyrationTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.RankedTimeRecoding
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding
open CountedMatrixOverlap
open CountedOrderTypeGyration
open CountedRelativeGyrationTransport

/-- Literal transport of numbered edges through an equality of matrices. -/
def edgeCast {n : ℕ} {A B : CountMat n n} (h : A = B) : Edge A ≃ Edge B :=
  Equiv.cast (congrArg (fun M : CountMat n n => Edge M) h)

theorem edgeCast_symm_apply {n : ℕ} {A B : CountMat n n} (h : A = B) (a : Edge B) :
    edgeCast h (edgeCast h.symm a) = a := by cases h; rfl

theorem edgeCast_source {n : ℕ} {A B : CountMat n n} (h : A = B) (a : Edge A) :
    (edgeCast h a).source = a.source := by cases h; rfl

theorem edgeCast_target {n : ℕ} {A B : CountMat n n} (h : A = B) (a : Edge A) :
    (edgeCast h a).target = a.target := by cases h; rfl

theorem edgeCast_number {n : ℕ} {A B : CountMat n n} (h : A = B) (a : Edge A) :
    (edgeCast h a).number.val = a.number.val := by cases h; rfl

def castTimed {n : ℕ} {A B : CountMat n n} (h : A = B) : TimedEquiv A B := by
  cases h
  exact TimedEquiv.refl A

theorem cast_coordinate {n : ℕ} {A B : CountMat n n} (h : A = B)
    (x : Path A) (t : ℤ) :
    ((castTimed h).equiv x).val t = edgeCast h (x.val t) := by
  cases h
  rfl

theorem cast_gyration {n d : ℕ} [NeZero d] {A B : CountMat n n} (h : A = B) :
    (castTimed h).gyration d = 0 := by
  cases h
  exact TimedEquiv.gyration_refl A d

/-- There is exactly one identity edge at this vertex; its actual number is 0. -/
def identityEdge {n : ℕ} (i : Fin n) : Edge (1 : CountMat n n) :=
  ⟨i,i,⟨0,by simp⟩⟩

/-- Consumed rank helper. This is direct reuse of the public finite ordered
embedding uniqueness theorem, not a second proof of that library result. -/
theorem rank_identity {q : ℕ} (f : Fin q → Fin q) (hf : StrictMono f) :
    f = id := by
  have h₁ := Finset.orderEmbOfFin_unique
    (show (Finset.univ : Finset (Fin q)).card = q by simp)
    (fun i => Finset.mem_univ (f i)) hf
  have h₂ := Finset.orderEmbOfFin_unique
    (show (Finset.univ : Finset (Fin q)).card = q by simp)
    (fun i : Fin q => Finset.mem_univ i) (show StrictMono (id : Fin q → Fin q) from
      fun _ _ h => h)
  exact h₁.trans h₂.symm

/-- Lex ranking really retains the original A-edge number in A*I.
Only the identity half-edge is collapsed, including empty fibres. -/
theorem join_right_identity {n : ℕ} (A : CountMat n n) (a : Edge A) :
    edgeCast (Matrix.mul_one A) (join A 1 a (identityEdge a.target) rfl) = a := by
  rcases a with ⟨i,k,a⟩
  let h : (A*1) i k = A i k := congrArg (fun M : CountMat n n => M i k) (Matrix.mul_one A)
  let p : Fin (A i k) → Fiber A 1 i k := fun q => ⟨k,q,⟨0,by simp⟩⟩
  let f : Fin (A i k) → Fin (A i k) := fun q =>
    Fin.cast h ((fiberEquiv A 1 i k).symm (p q))
  have hf : StrictMono f := by
    intro q r hqr
    change (fiberEquiv A 1 i k).symm (p q) < (fiberEquiv A 1 i k).symm (p r)
    apply (fiber_number_lt_iff A 1 i k (p q) (p r)).mpr
    exact Sigma.Lex.right _ _ (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hqr))
  have ha : f a = a := congrFun (rank_identity f hf) a
  apply edge_eq_coordinates
  · exact edgeCast_source _ _
  · exact edgeCast_target _ _
  · exact (edgeCast_number _ _).trans (congrArg Fin.val ha)

/-- The same rank argument for I*A uses the other coordinate of the pair.
This is not inferred from the A*I case or from beam-action equality. -/
theorem join_left_identity {n : ℕ} (A : CountMat n n) (a : Edge A) :
    edgeCast (Matrix.one_mul A) (join 1 A (identityEdge a.source) a rfl) = a := by
  rcases a with ⟨i,k,a⟩
  let h : (1*A) i k = A i k := congrArg (fun M : CountMat n n => M i k) (Matrix.one_mul A)
  let p : Fin (A i k) → Fiber 1 A i k := fun q => ⟨i,⟨0,by simp⟩,q⟩
  let f : Fin (A i k) → Fin (A i k) := fun q =>
    Fin.cast h ((fiberEquiv 1 A i k).symm (p q))
  have hf : StrictMono f := by
    intro q r hqr
    change (fiberEquiv 1 A i k).symm (p q) < (fiberEquiv 1 A i k).symm (p r)
    apply (fiber_number_lt_iff 1 A i k (p q) (p r)).mpr
    exact Sigma.Lex.right _ _ (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hqr⟩))
  have ha : f a = a := congrFun (rank_identity f hf) a
  apply edge_eq_coordinates
  · exact edgeCast_source _ _
  · exact edgeCast_target _ _
  · exact (edgeCast_number _ _).trans (congrArg Fin.val ha)

theorem split_right_identity {n : ℕ} (A : CountMat n n) (a : Edge A) :
    split A 1 (edgeCast (Matrix.mul_one A).symm a) = (a,identityEdge a.target) := by
  have hj : edgeCast (Matrix.mul_one A).symm a = join A 1 a (identityEdge a.target) rfl := by
    apply (edgeCast (Matrix.mul_one A)).injective
    rw [edgeCast_symm_apply, join_right_identity]
  rw [hj, split_join]


/-- Actual forward convention: the S-half at t joins the R-half at t+1. -/
theorem recoding_time {n : ℕ} (A : CountMat n n) :
    ((castTimed (Matrix.mul_one A).symm).comp (TimedEquiv.elementary A 1)).comp
      (castTimed (Matrix.one_mul A)) = TimedEquiv.timeEquiv A 1 := by
  apply TimedEquiv.ext
  intro x
  apply Subtype.ext
  funext t
  change (((castTimed (Matrix.one_mul A)).equiv
    ((elementaryHomeomorph A 1) ((castTimed (Matrix.mul_one A).symm).equiv x))).val t) = _
  rw [cast_coordinate]
  change edgeCast (Matrix.one_mul A)
    ((elementaryHomeomorph A 1 ((castTimed (Matrix.mul_one A).symm).equiv x)).val t) =
      x.val (t+1)
  simp only [elementary_coordinate, cast_coordinate, split_right_identity]
  simpa only [x.property t] using join_left_identity A (x.val (t+1))


/-- The genuine original-ranked primitive-orbit sum, at ALL nonzero periods. -/
theorem relative_time {n d : ℕ} [NeZero d] (A : CountMat n n) :
    relativeForwardGyration (d := d) A 1 =
      (Fintype.card (ActualPathOrbit A d) : ZMod d) := by
  have h := congrArg (fun u => u.gyration d) (recoding_time A)
  simpa only [TimedEquiv.gyration_comp, cast_gyration, zero_add, add_zero,
    TimedEquiv.gyration_elementary, TimedEquiv.gyration_time, Int.cast_one, mul_one] using h


end SourceOnly.RankedTimeRecoding
