/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleRoutes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irreducible original routes pay rectangular-word occurrence. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectangleOccurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.Arborescence
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.Combinatorics.Quiver.Path

/-! Bounded original labelled routes and their same-law visible occurrence payment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Classical ENNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

private def emptyRoute (θ : Presentation H) (r : H) : LabelledRoute θ r r where
  length := 0
  states _ := r
  labels i := nomatch i
  first := rfl
  last := rfl
  positive i := nomatch i

private def append_label (θ : Presentation H) (h s r : H) (a : LabelledRoute θ h s)
    (x : Bool) (he : 0 < θ.matrix x s r) : LabelledRoute θ h r where
  length := a.length+1
  states := Fin.snoc a.states r
  labels := Fin.snoc a.labels x
  first := by simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc] using a.first
  last := Fin.snoc_last _ _
  positive i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last, a.last] using he
    · simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using a.positive j

omit [MeasurableSpace H] [MeasurableSingletonClass H] in
private theorem route_of_positive_path (θ : Presentation H) {h r : H}
    (p : @Quiver.Path H (Matrix.toQuiver (θ.matrix false+θ.matrix true)) h r) :
    ∃ a : LabelledRoute θ h r,
      a.length = @Quiver.Path.length H (Matrix.toQuiver (θ.matrix false+θ.matrix true)) h r p ∧
      List.ofFn a.states = @Quiver.Path.vertices H (Matrix.toQuiver (θ.matrix false+θ.matrix true)) h r p := by
  letI := Matrix.toQuiver (θ.matrix false+θ.matrix true)
  induction p with
  | nil => exact ⟨emptyRoute θ h,rfl,by simp [emptyRoute, Quiver.Path.vertices]⟩
  | @cons s t p e ih =>
    obtain ⟨a,ha,hv⟩ := ih
    have hs : 0 < θ.matrix false s t + θ.matrix true s t := e.down
    obtain ⟨x,hx⟩ : ∃ x : Bool, 0 < θ.matrix x s t := by
      by_cases hf : 0 < θ.matrix false s t
      · exact ⟨false,hf⟩
      · exact ⟨true,by linarith [le_of_not_gt hf]⟩
    refine ⟨append_label θ _ _ _ a x hx, congrArg Nat.succ ha, ?_⟩
    change List.ofFn (Fin.snoc a.states t) = p.vertices.concat t
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, hv]

private theorem short_route (θ : Presentation H)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j)
    (h r : H) : ∃ a : LabelledRoute θ h r,
      a.length < Fintype.card H ∧ Function.Injective a.states := by
  letI := Matrix.toQuiver (θ.matrix false+θ.matrix true)
  letI : Quiver.RootedConnected h := ⟨fun j => by
    obtain ⟨n,hn⟩ := hirr h j
    obtain ⟨⟨p,_⟩⟩ := (Matrix.pow_apply_pos_iff_nonempty_path
      (fun i j => add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _)) n h j).mp hn
    exact ⟨p⟩⟩
  let p := Quiver.shortestPath h r
  have hs := Quiver.Path.isStrictlySimple_of_shortest p (Quiver.shortest_path_spec h)
  have hb := Quiver.Path.length_le_card_minus_one_of_isSimple p hs
  obtain ⟨a,ha,hv⟩ := route_of_positive_path θ p
  have hi : Function.Injective a.states := List.nodup_ofFn.mp (hv.symm ▸ hs)
  have hc : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨h⟩
  exact ⟨a, by omega, hi⟩

omit [MeasurableSpace H] [MeasurableSingletonClass H] in
private theorem one_incoming_zero (θ : Presentation H) (hpos : ∀ h, 0 < θ.initial h)
    (r : H) (hout : ∃ k, 0 < θ.matrix true r k) : ∀ s, θ.matrix true s r = 0 := by
  obtain ⟨k,hk⟩ := hout
  intro s
  have hz := congrFun (congrFun (trim_no11 θ) (⟨s,hpos s⟩ : Positive θ))
    (⟨k,hpos k⟩ : Positive θ)
  change (∑ l : Positive θ, θ.matrix true s l.val * θ.matrix true l.val k) = 0 at hz
  have hle : θ.matrix true s r * θ.matrix true r k ≤ 0 := by
    rw [← hz]
    exact Finset.single_le_sum (fun (l : Positive θ) _ => mul_nonneg (θ.matrix_nonneg true s l.val)
      (θ.matrix_nonneg true l.val k)) (Finset.mem_univ (⟨r,hpos r⟩ : Positive θ))
  nlinarith [θ.matrix_nonneg true s r]

private theorem first_one_outgoing (θ : Presentation H) (w : List Bool)
    (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows)
    (hw : w.head? = some true) : ∃ k, 0 < θ.matrix true r k := by
  obtain ⟨x,xs,rfl⟩ := List.exists_cons_of_ne_nil (show w ≠ [] from fun he => by simp [he] at hw)
  have hx : x = true := by simpa only [List.head?_cons, Option.some.injEq] using hw
  subst x
  obtain ⟨j,hj⟩ := R.cols_nonempty
  have hp := R.positive r hr j hj
  change 0 < (θ.matrix true * product θ xs) r j at hp
  rw [Matrix.mul_apply] at hp
  obtain ⟨k,_,hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ =>
    mul_nonneg (θ.matrix_nonneg _ _ _) (product_nonneg θ xs k j))).mp hp
  exact ⟨k,pos_of_mul_pos_left hk (product_nonneg θ xs k j)⟩

/-- If the source rectangle word starts with one, its row state cannot have
received an incoming one under the actual irreducible original law. -/
theorem first_one_incoming_past_null (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows)
    (hw : w.head? = some true) (t : ℤ) :
    J {z | state t z = r ∧ z.2 (t-1) = true} = 0 := by
  have hz := one_incoming_zero θ (irreducible_initial_positive θ hirr) r
    (first_one_outgoing θ w R r hr hw)
  let E (s : H) := MarkedPredictiveQuotient.cylinder (t-1) 1
    (Fin.cons s (fun _ => r)) (fun _ => true)
  have hnull (s : H) : J (E s) = 0 := by
    apply (ENNReal.toReal_eq_zero_iff _).mp ?_ |>.resolve_right (measure_ne_top _ _)
    change J.real (E s) = 0
    rw [hc]
    simp [pathMass,hz]
  apply measure_mono_null (t := ⋃ s, E s) ?_ (measure_iUnion_null hnull)
  intro z h
  refine Set.mem_iUnion.mpr ⟨z.1 (t-1),?_,?_⟩
  · intro i
    fin_cases i <;> simpa [state] using (by first | rfl | exact h.1 : _)
  · intro i
    fin_cases i
    simpa using h.2

/-- Bounded positive original routes, with the first-one seam paid by a final zero
edge, give the actual visible success-event bound on an irreducible class. -/
theorem irreducible_rectangle_occurrence (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows) :
    ∃ a : ∀ h, LabelledRoute θ h r,
      (a r).length = 0 ∧ (∀ h, (a h).length ≤ Fintype.card H) ∧
      (∀ h, w.head? = some false → (a h).length < Fintype.card H) ∧
      (∀ h, h ≠ r → w.head? = some true →
        (List.ofFn (a h).labels).getLast? = some false) ∧
      (∀ h, Function.Injective (a h).states) ∧
      (w.head? = some true → ∀ s, θ.matrix true s r = 0) ∧
      (let ε := selectedEpsilon θ w r a
       let b := w.length + Fintype.card H
       0 < ε ∧ ε ≤ 1 ∧
       (∀ (t : ℤ) (h : H), 0 < θ.initial h →
         ENNReal.ofReal ε ≤ futureLaw J t h (success w b)) ∧
       (∀ (t : ℤ) (h : H) (A : Set (ℕ → H × Bool)), MeasurableSet A →
         ENNReal.ofReal ε * J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A)) ≤
           J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' success w b)))) := by
  have hcard : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨r⟩
  have hpos := irreducible_initial_positive θ hirr
  have routes (h : H) : ∃ a : LabelledRoute θ h r,
      Function.Injective a.states ∧ a.length ≤ Fintype.card H ∧ (h = r → a.length = 0) ∧
      (w.head? = some false → a.length < Fintype.card H) ∧
      (h ≠ r → w.head? = some true → (List.ofFn a.labels).getLast? = some false) := by
    obtain ⟨a,ha,hi⟩ := short_route θ hirr h r
    have he : h = r → a.length = 0 := by
      intro he
      have hf : a.states 0 = a.states (Fin.last a.length) := by rw [a.first,a.last,he]
      have hz := congrArg Fin.val (hi hf)
      simpa using hz.symm
    refine ⟨a,hi,ha.le,he,fun _ => ha,?_⟩
    intro hne hw
    have hn : a.length ≠ 0 := by
      intro hz
      have hf : (0 : Fin (a.length+1)) = Fin.last a.length := Fin.ext (by simpa using hz.symm)
      exact hne (a.first.symm.trans ((congrArg a.states hf).trans a.last))
    have hl : a.labels ⟨a.length-1,by omega⟩ = false := by
      cases hx : a.labels ⟨a.length-1,by omega⟩ with
      | false => rfl
      | true =>
        have hp := a.positive ⟨a.length-1,by omega⟩
        have hf : (⟨a.length-1,by omega⟩ : Fin a.length).succ = Fin.last a.length := Fin.ext (by simp; omega)
        rw [hx,hf,a.last,one_incoming_zero θ hpos r (first_one_outgoing θ w R r hr hw)] at hp
        exact (lt_irrefl 0 hp).elim
    simpa [List.getLast?_eq_getElem?, List.getElem?_eq_getElem, hn] using
      (show ∃ hn : 0 < a.length, a.labels ⟨a.length-1, by omega⟩ = false from
        ⟨Nat.pos_of_ne_zero hn, hl⟩)
  choose a ha using routes
  have hb (h : H) := (ha h).2
  refine ⟨a,(hb r).2.1 rfl,(fun h => (hb h).1),(fun h => (hb h).2.2.1),
    (fun h => (hb h).2.2.2),(fun h => (ha h).1),
    (fun hw => one_incoming_zero θ hpos r (first_one_outgoing θ w R r hr hw)),?_⟩
  exact original_rectangle_occurrence θ J hc w R r hr a (fun h => (hb h).1)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
