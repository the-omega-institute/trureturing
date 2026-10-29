/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleRoutes
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalRectangleRoutes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Irreducibility supplies bounded positive original labelled routes for rectangular-word occurrence. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Classical
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

private theorem bounded_positive_power (A : Matrix H H ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (i j : H) (hp : ∃ n : ℕ, 0 < (A^n) i j) :
    ∃ n < Fintype.card H, 0 < (A^n) i j := by
  letI : Nonempty H := ⟨i⟩
  by_contra hh
  have hz (n : ℕ) (hn : n < Fintype.card H) : (A^n) i j = 0 := by
    exact le_antisymm (le_of_not_gt (fun hn' => hh ⟨n,hn,hn'⟩))
      (Matrix.pow_apply_nonneg hA n i j)
  obtain ⟨n,hn⟩ := hp
  have hc : A.charpoly ≠ 1 := by
    intro he
    have hd := congrArg Polynomial.natDegree he
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_one] at hd
    exact (Fintype.card_ne_zero : Fintype.card H ≠ 0) hd
  have hd : (Polynomial.X^n %ₘ A.charpoly).natDegree < Fintype.card H := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using
      Polynomial.natDegree_modByMonic_lt (Polynomial.X^n) A.charpoly_monic hc
  have he : (A^n) i j = 0 := by
    rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hd]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun k hk => by rw [hz k (Finset.mem_range.mp hk), mul_zero]
  exact (ne_of_gt hn) he

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

private theorem route_of_positive_path (θ : Presentation H) {h r : H}
    (p : @Quiver.Path H (Matrix.toQuiver (θ.matrix false+θ.matrix true)) h r) :
    ∃ a : LabelledRoute θ h r, a.length = p.length := by
  induction p with
  | nil => exact ⟨emptyRoute θ h,rfl⟩
  | cons p e ih =>
    obtain ⟨a,ha⟩ := ih
    have hs : 0 < θ.matrix false _ _ + θ.matrix true _ _ := e.down
    obtain ⟨x,hx⟩ : ∃ x : Bool, 0 < θ.matrix x _ _ := by
      by_cases hf : 0 < θ.matrix false _ _
      · exact ⟨false,hf⟩
      · exact ⟨true,by linarith [le_of_not_gt hf]⟩
    exact ⟨append_label θ _ _ _ a x hx, congrArg Nat.succ ha⟩

private theorem route_of_positive_power (θ : Presentation H) (n : ℕ) (h r : H)
    (hp : 0 < ((θ.matrix false+θ.matrix true)^n) h r) :
    ∃ a : LabelledRoute θ h r, a.length = n := by
  obtain ⟨⟨p,he⟩⟩ := (Matrix.pow_apply_pos_iff_nonempty_path
    (fun i j => add_nonneg (θ.matrix_nonneg false i j) (θ.matrix_nonneg true i j))
      n h r).mp hp
  obtain ⟨a,ha⟩ := route_of_positive_path θ p
  exact ⟨a,ha.trans he⟩

private theorem short_route (θ : Presentation H)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j)
    (h r : H) : ∃ a : LabelledRoute θ h r, a.length < Fintype.card H := by
  obtain ⟨n,hn,hp⟩ := bounded_positive_power (θ.matrix false+θ.matrix true)
    (fun i j => add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _)) h r (hirr h r)
  obtain ⟨a,ha⟩ := route_of_positive_power θ n h r hp
  exact ⟨a,ha ▸ hn⟩

private def append_zero (θ : Presentation H) (h s r : H) (a : LabelledRoute θ h s)
    (he : 0 < θ.matrix false s r) : LabelledRoute θ h r :=
  append_label θ h s r a false he

private theorem zero_predecessor (θ : Presentation H) (hpos : ∀ h, 0 < θ.initial h)
    (r : H) (hout : ∃ k, 0 < θ.matrix true r k) : ∃ s, 0 < θ.matrix false s r := by
  obtain ⟨k,hk⟩ := hout
  have hnr (s : H) : θ.matrix true s r = 0 := by
    have hz := congrFun (congrFun (trim_no11 θ) (⟨s,hpos s⟩ : Positive θ))
      (⟨k,hpos k⟩ : Positive θ)
    change (∑ l : Positive θ, θ.matrix true s l.val * θ.matrix true l.val k) = 0 at hz
    have hle : θ.matrix true s r * θ.matrix true r k ≤ 0 := by
      rw [← hz]
      exact Finset.single_le_sum (fun (l : Positive θ) _ => mul_nonneg (θ.matrix_nonneg true s l.val)
        (θ.matrix_nonneg true l.val k)) (Finset.mem_univ (⟨r,hpos r⟩ : Positive θ))
    nlinarith [θ.matrix_nonneg true s r]
  have hs : 0 < ∑ s, θ.initial s * (θ.matrix false s r+θ.matrix true s r) := by
    rw [θ.stationary]
    exact hpos r
  obtain ⟨s,_,hs⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ => mul_nonneg
    (θ.initial_nonneg s) (add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _)))).mp hs
  rw [hnr s,add_zero] at hs
  exact ⟨s,pos_of_mul_pos_right hs (θ.initial_nonneg s)⟩

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
  exact ⟨k,pos_of_mul_pos_right hk (product_nonneg θ xs k j)⟩

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
      a.length ≤ Fintype.card H ∧ (h = r → a.length = 0) ∧
      (w.head? = some false → a.length < Fintype.card H) ∧
      (h ≠ r → w.head? = some true → (List.ofFn a.labels).getLast? = some false) := by
    by_cases he : h = r
    · subst h
      exact ⟨emptyRoute θ r,Nat.zero_le _,fun _ => rfl,fun _ => hcard,
        fun hn => (hn rfl).elim⟩
    · by_cases ht : w.head? = some true
      · obtain ⟨s,hs⟩ := zero_predecessor θ hpos r (first_one_outgoing θ w R r hr ht)
        obtain ⟨a,ha⟩ := short_route θ hirr h s
        refine ⟨append_zero θ h s r a hs,Nat.succ_le_of_lt ha,fun hh => (he hh).elim,
          ?_,?_⟩
        · intro hf
          rw [ht] at hf
          cases hf
        · intro _ _
          simp only [append_zero, append_label, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
            List.getLast?_concat]
      · obtain ⟨a,ha⟩ := short_route θ hirr h r
        exact ⟨a,ha.le,fun hh => (he hh).elim,fun _ => ha,fun _ hh => (ht hh).elim⟩
  choose a ha using routes
  refine ⟨a,(ha r).2.1 rfl,(fun h => (ha h).1),(fun h => (ha h).2.2.1),
    (fun h => (ha h).2.2.2),?_⟩
  exact original_rectangle_occurrence θ J hc w R r hr a (fun h => (ha h).1)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
