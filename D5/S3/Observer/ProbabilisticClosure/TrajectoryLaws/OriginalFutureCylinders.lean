/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original marked cylinders factor at the emitted-bit boundary with the actual finite future masses. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- All future outputs on the original emitted-bit clock, starting at the cut. -/
def future (t : ℤ) (z : PathSpace H) : ℕ → Bool := fun k => z.2 (t + k)

/-- All hidden and visible coordinates strictly before the cut. -/
def past (t : ℤ) (z : PathSpace H) : ℕ → H × Bool :=
  fun k => (z.1 (t - (k + 1)), z.2 (t - (k + 1)))

def state (t : ℤ) (z : PathSpace H) : H := z.1 t

private def joinHidden (m n : ℕ) (h : Fin (m + 1) → H) (k : Fin n → H) :
    Fin (m + n + 1) → H := Fin.append (m := m) (n := n+1) (Fin.init h) (Fin.cons (h (Fin.last m)) k)

private theorem join_left (m n : ℕ) (h : Fin (m + 1) → H) (k : Fin n → H)
    (j : Fin (m + 1)) : joinHidden m n h k ⟨j.val, by omega⟩ = h j := by
  by_cases hj : j.val < m
  · have he : (⟨j.val, by omega⟩ : Fin (m + n + 1)) =
        Fin.castAdd (n + 1) (⟨j.val, hj⟩ : Fin m) := rfl
    rw [he]
    simp only [joinHidden, Fin.append_left, Fin.init]
    apply congrArg h
    exact Fin.ext rfl
  · have he : (⟨j.val, by omega⟩ : Fin (m + n + 1)) =
        Fin.natAdd m (0 : Fin (n + 1)) := by ext; dsimp; omega
    rw [he]
    simp only [joinHidden, Fin.append_right, Fin.cons_zero]
    apply congrArg h
    apply Fin.ext
    dsimp
    omega

private theorem join_right (m n : ℕ) (h : Fin (m + 1) → H) (k : Fin n → H)
    (j : Fin (n + 1)) : joinHidden m n h k ⟨m + j.val, by omega⟩ =
      (Fin.cons (h (Fin.last m)) k : Fin (n+1) → H) j := by
  change Fin.append _ _ (Fin.natAdd m j) = _
  exact Fin.append_right _ _ j

private theorem path_concat (M : Bool → Matrix H H ℝ) (m n : ℕ)
    (h : Fin (m + 1) → H) (k : Fin n → H) (w : Fin m → Bool) (v : Fin n → Bool) :
    pathMass M (m+n) (joinHidden m n h k) (Fin.append w v) =
      pathMass M m h w * pathMass M n (Fin.cons (h (Fin.last m)) k) v := by
  unfold pathMass
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.append_left]
    have h1 := join_left m n h k i.castSucc
    have h2 := join_left m n h k i.succ
    convert congrArg₂ (M (w i)) h1 h2 using 1 <;> congr 2 <;> apply Fin.ext <;> rfl
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.append_right]
    have h1 := join_right m n h k i.castSucc
    have h2 := join_right m n h k i.succ
    convert congrArg₂ (M (v i)) h1 h2 using 1 <;> congr 2 <;> apply Fin.ext <;> omega

/-- Splitting an actual marked past cylinder at its last hidden state leaves the
original finite future row mass, at every integer emitted-bit cut. -/
theorem past_future_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (m n : ℕ)
    (h : Fin (m+1) → H) (w : Fin m → Bool) (v : Fin n → Bool) :
    J.real (MarkedPredictiveQuotient.cylinder (t-m) m h w ∩
      Prod.snd ⁻¹' visibleCylinder t n v) =
      θ.initial (h 0) * pathMass θ.matrix m h w *
        futureMass θ.matrix (h (Fin.last m)) n v := by
  let f (k : Fin n → H) := MarkedPredictiveQuotient.cylinder (t-m) (m+n)
    (joinHidden m n h k) (Fin.append w v)
  have he : MarkedPredictiveQuotient.cylinder (t-m) m h w ∩
      Prod.snd ⁻¹' visibleCylinder t n v = ⋃ k, f k := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion,
      MarkedPredictiveQuotient.cylinder, visibleCylinder, Set.mem_setOf_eq, f]
    constructor
    · rintro ⟨⟨hh,hw⟩,hv⟩
      let k : Fin n → H := fun i => z.1 (t + (i.val + 1 : ℕ))
      refine ⟨k,?_,?_⟩
      · intro j
        by_cases hj : j.val ≤ m
        · exact (hh ⟨j.val, by omega⟩).trans
            (join_left m n h k ⟨j.val, by omega⟩).symm
        · let i : Fin n := ⟨j.val-m-1, by omega⟩
          have he : j = ⟨m + i.succ.val, by omega⟩ := by
            apply Fin.ext
            dsimp [i]
            omega
          have hj' := join_right m n h k i.succ
          have ht : t - (m:ℤ) + (m + (i.val + 1) : ℕ) =
              t + (i.val + 1 : ℕ) := by push_cast; omega
          rw [he]
          exact (congrArg z.1 ht).trans (by simpa only [Fin.cons_succ, k] using hj'.symm)
      · intro j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · rw [Fin.append_left]
          exact hw i
        · rw [Fin.append_right]
          simpa only [Fin.val_natAdd, Nat.cast_add, ← add_assoc, sub_add_cancel] using hv i
    · rintro ⟨k,hh,hw⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro j
        exact (hh ⟨j.val, by omega⟩).trans (join_left m n h k j)
      · intro j
        simpa only [Fin.append_left, Fin.val_castAdd] using hw (Fin.castAdd n j)
      · intro j
        have hj := hw (Fin.natAdd m j)
        rw [Fin.append_right] at hj
        simpa only [Fin.val_natAdd, Nat.cast_add, ← add_assoc, sub_add_cancel] using hj
  have hd : Pairwise (fun k l => Disjoint (f k) (f l)) := by
    intro k l hne
    rw [Set.disjoint_left]
    intro z hz hz'
    apply hne
    funext i
    have hk := hz.1 (⟨m + i.succ.val, by omega⟩ : Fin (m+n+1))
    have hl := hz'.1 (⟨m + i.succ.val, by omega⟩ : Fin (m+n+1))
    rw [join_right, Fin.cons_succ] at hk hl
    exact hk.symm.trans hl
  have hm : ∀ k, MeasurableSet (f k) := fun k => cylinder_measurable _ _ _ _
  rw [he, measureReal_iUnion_fintype hd hm]
  have hi (k : Fin n → H) : joinHidden m n h k 0 = h 0 := join_left m n h k 0
  have hmass (k : Fin n → H) : J.real (f k) = θ.initial (h 0) *
      (pathMass θ.matrix m h w * pathMass θ.matrix n (Fin.cons (h (Fin.last m)) k) v) := by
    have hh := hc (t-m) (m+n) (joinHidden m n h k) (Fin.append w v)
    rw [hi, path_concat] at hh
    exact hh
  simp_rw [hmass, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_path_tails]

#print axioms past_future_mass

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
