/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleHalfLines
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleHalfLines
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite erased-record conditional bounds pass to the exact opposite half-lines. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ErasedExteriorFiltration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Filter
open scoped Classical Topology
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleHalfLines

private abbrev Visible := ℤ → Bool

private def leftField (k : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (leftWord k) inferInstance

private def rightField (n : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (rightWord n) inferInstance

private def beforeField : MeasurableSpace Visible :=
  MeasurableSpace.comap before inferInstance

private def afterField : MeasurableSpace Visible :=
  MeasurableSpace.comap after inferInstance

/-- The observed original chronological words, with the erased bit absent. -/
def recordField (k n : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (fun z => (leftWord k z,rightWord n z)) inferInstance

private theorem recordField_eq (k n : ℕ) : recordField k n = leftField k ⊔ rightField n := by
  exact MeasurableSpace.comap_prodMk _ _

private theorem leftField_succ (k : ℕ) : leftField k ≤ leftField (k+1) := by
  let f : (Fin (k+1) → Bool) → (Fin k → Bool) := fun v i => v i.succ
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : leftWord k = f ∘ leftWord (k+1) := by
    funext z i
    dsimp [leftWord,f]
    congr 1
    push_cast
    omega
  exact MeasurableSpace.comap_le_comap_of_eq_comp _ hf he

private theorem rightField_succ (n : ℕ) : rightField n ≤ rightField (n+1) := by
  let f : (Fin (n+1) → Bool) → (Fin n → Bool) := fun v i => v i.castSucc
  exact MeasurableSpace.comap_le_comap_of_eq_comp _
    (show Measurable f by dsimp [f]; fun_prop) rfl

private theorem leftField_le (k : ℕ) : leftField k ≤ (inferInstance : MeasurableSpace Visible) :=
  (show Measurable (leftWord k) by unfold leftWord; fun_prop).comap_le

private theorem rightField_le (n : ℕ) : rightField n ≤ (inferInstance : MeasurableSpace Visible) :=
  (show Measurable (rightWord n) by unfold rightWord; fun_prop).comap_le

private theorem beforeField_le : beforeField ≤ (inferInstance : MeasurableSpace Visible) :=
  (show Measurable before by unfold before; fun_prop).comap_le

private theorem afterField_le : afterField ≤ (inferInstance : MeasurableSpace Visible) :=
  (show Measurable after by unfold after; fun_prop).comap_le

private theorem leftField_sup : (⨆ k, leftField k) = beforeField := by
  apply le_antisymm
  · apply iSup_le
    intro k
    let f : (ℕ → Bool) → (Fin k → Bool) := fun v i => v (k-1-i.val)
    have hf : Measurable f := by dsimp [f]; fun_prop
    have he : leftWord k = f ∘ before := by
      funext z i
      dsimp [leftWord,f,before]
      congr 1
      have hi := i.isLt
      omega
    exact MeasurableSpace.comap_le_comap_of_eq_comp _ hf he
  · have hm (n : ℕ) : @Measurable Visible Bool (⨆ k, leftField k) inferInstance
        (fun z => before z n) := by
      have hh : Measurable[leftField (n+1)] (fun z => leftWord (n+1) z 0) :=
        (measurable_pi_apply 0).comp (Measurable.of_comap_le le_rfl)
      have hh' := hh.mono (le_iSup leftField (n+1)) le_rfl
      convert hh' using 1
      funext z
      dsimp [leftWord,before]
      congr 1
    letI : MeasurableSpace Visible := ⨆ k, leftField k
    exact (Measurable.of_eval hm).comap_le

private theorem rightField_sup : (⨆ n, rightField n) = afterField := by
  apply le_antisymm
  · apply iSup_le
    intro n
    let f : (ℕ → Bool) → (Fin n → Bool) := fun v i => v i.val
    exact MeasurableSpace.comap_le_comap_of_eq_comp _
      (show Measurable f by dsimp [f]; fun_prop) rfl
  · have hm (n : ℕ) : @Measurable Visible Bool (⨆ k, rightField k) inferInstance
        (fun z => after z n) := by
      have hh : Measurable[rightField (n+1)]
          (fun z => rightWord (n+1) z (Fin.last n)) :=
        (measurable_pi_apply (Fin.last n)).comp (Measurable.of_comap_le le_rfl)
      exact hh.mono (le_iSup rightField (n+1)) le_rfl
    letI : MeasurableSpace Visible := ⨆ k, rightField k
    exact (Measurable.of_eval hm).comap_le

private def growPast (n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Visible) where
  seq k := leftField k ⊔ rightField n
  mono' := fun i j hij => sup_le_sup
    ((monotone_nat_of_le_succ leftField_succ) hij) le_rfl
  le' k := sup_le (leftField_le k) (rightField_le n)

private def growFuture (k : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Visible) where
  seq n := leftField k ⊔ rightField n
  mono' := fun i j hij => sup_le_sup le_rfl
    ((monotone_nat_of_le_succ rightField_succ) hij)
  le' n := sup_le (leftField_le k) (rightField_le n)

private def finishFuture : Filtration ℕ (inferInstance : MeasurableSpace Visible) where
  seq n := beforeField ⊔ rightField n
  mono' := fun i j hij => sup_le_sup le_rfl
    ((monotone_nat_of_le_succ rightField_succ) hij)
  le' n := sup_le beforeField_le (rightField_le n)

private def finishPast : Filtration ℕ (inferInstance : MeasurableSpace Visible) where
  seq k := leftField k ⊔ afterField
  mono' := fun i j hij => sup_le_sup
    ((monotone_nat_of_le_succ leftField_succ) hij) le_rfl
  le' k := sup_le (leftField_le k) afterField_le

private theorem rightObservation_field (n : ℕ) :
    MeasurableSpace.comap (rightObservation n) inferInstance = beforeField ⊔ rightField n := by
  exact MeasurableSpace.comap_prodMk _ _

private theorem leftObservation_field (k : ℕ) :
    MeasurableSpace.comap (leftObservation k) inferInstance = leftField k ⊔ afterField := by
  exact MeasurableSpace.comap_prodMk _ _

private theorem exterior_field :
    MeasurableSpace.comap exterior inferInstance = beforeField ⊔ afterField := by
  exact MeasurableSpace.comap_prodMk _ _

private theorem past_limit (P : Measure Visible) [IsProbabilityMeasure P]
    (Y : Visible → ℝ) (n : ℕ) :
    ∀ᵐ z ∂P, Tendsto (fun k => (P[Y | recordField k n]) z) atTop
      (𝓝 ((P[Y | MeasurableSpace.comap (rightObservation n) inferInstance]) z)) := by
  have he : (⨆ k, growPast n k) = MeasurableSpace.comap (rightObservation n) inferInstance := by
    simp only [growPast, ← iSup_sup, leftField_sup, rightObservation_field]
  simpa only [he, growPast, ← recordField_eq] using
    (tendsto_ae_condExp (μ := P) (ℱ := growPast n) Y)

private theorem future_limit (P : Measure Visible) [IsProbabilityMeasure P]
    (Y : Visible → ℝ) (k : ℕ) :
    ∀ᵐ z ∂P, Tendsto (fun n => (P[Y | recordField k n]) z) atTop
      (𝓝 ((P[Y | MeasurableSpace.comap (leftObservation k) inferInstance]) z)) := by
  have he : (⨆ n, growFuture k n) = MeasurableSpace.comap (leftObservation k) inferInstance := by
    simp only [growFuture, ← sup_iSup, rightField_sup, leftObservation_field]
  simpa only [he, growFuture, ← recordField_eq] using
    (tendsto_ae_condExp (μ := P) (ℱ := growFuture k) Y)

private theorem full_future_limit (P : Measure Visible) [IsProbabilityMeasure P]
    (Y : Visible → ℝ) :
    ∀ᵐ z ∂P, Tendsto
      (fun n => (P[Y | MeasurableSpace.comap (rightObservation n) inferInstance]) z)
      atTop (𝓝 ((P[Y | MeasurableSpace.comap exterior inferInstance]) z)) := by
  have he : (⨆ n, finishFuture n) = MeasurableSpace.comap exterior inferInstance := by
    simp only [finishFuture, ← sup_iSup, rightField_sup, exterior_field]
  simpa only [he, finishFuture, ← rightObservation_field] using
    (tendsto_ae_condExp (μ := P) (ℱ := finishFuture) Y)

private theorem full_past_limit (P : Measure Visible) [IsProbabilityMeasure P]
    (Y : Visible → ℝ) :
    ∀ᵐ z ∂P, Tendsto
      (fun k => (P[Y | MeasurableSpace.comap (leftObservation k) inferInstance]) z)
      atTop (𝓝 ((P[Y | MeasurableSpace.comap exterior inferInstance]) z)) := by
  have he : (⨆ k, finishPast k) = MeasurableSpace.comap exterior inferInstance := by
    simp only [finishPast, ← iSup_sup, leftField_sup, exterior_field]
  simpa only [he, finishPast, ← leftObservation_field] using
    (tendsto_ae_condExp (μ := P) (ℱ := finishPast) Y)

/-- Finite conditional-expectation comparisons pass to the same-measure full
exterior posterior and the two exact one-sided observations. On the left the
past is completed first, then the future; on the right the order is reversed.
The fixed bounds B_L and B_R are unchanged through both limits. -/
theorem finite_record_bounds_to_half_lines
    (P : Measure Visible) [IsProbabilityMeasure P] (Y : Visible → ℝ) (j : ℕ)
    (B_L B_R : Visible → ℝ)
    (hL : ∀ k n, j ≤ k → ∀ᵐ z ∂P,
      |(P[Y | recordField k n]) z - (P[Y | recordField j n]) z| ≤ B_L z)
    (hR : ∀ k n, j ≤ n → ∀ᵐ z ∂P,
      |(P[Y | recordField k n]) z - (P[Y | recordField k j]) z| ≤ B_R z) :
    (∀ᵐ z ∂P, |(P[Y | MeasurableSpace.comap exterior inferInstance]) z -
      (P[Y | MeasurableSpace.comap (leftObservation j) inferInstance]) z| ≤ B_L z) ∧
    (∀ᵐ z ∂P, |(P[Y | MeasurableSpace.comap exterior inferInstance]) z -
      (P[Y | MeasurableSpace.comap (rightObservation j) inferInstance]) z| ≤ B_R z) := by
  have firstL (n : ℕ) : ∀ᵐ z ∂P,
      |(P[Y | MeasurableSpace.comap (rightObservation n) inferInstance]) z -
        (P[Y | recordField j n]) z| ≤ B_L z := by
    have hall : ∀ᵐ z ∂P, ∀ k, j ≤ k →
        |(P[Y | recordField k n]) z - (P[Y | recordField j n]) z| ≤ B_L z :=
      ae_all_iff.mpr fun k => by
        by_cases hk : j ≤ k
        · exact (hL k n hk).mono fun z hz _ => hz
        · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
    filter_upwards [past_limit P Y n,hall] with z hz hb
    exact le_of_tendsto ((hz.sub tendsto_const_nhds).abs)
      (eventually_atTop.mpr ⟨j,fun k hk => hb k hk⟩)
  have firstR (k : ℕ) : ∀ᵐ z ∂P,
      |(P[Y | MeasurableSpace.comap (leftObservation k) inferInstance]) z -
        (P[Y | recordField k j]) z| ≤ B_R z := by
    have hall : ∀ᵐ z ∂P, ∀ n, j ≤ n →
        |(P[Y | recordField k n]) z - (P[Y | recordField k j]) z| ≤ B_R z :=
      ae_all_iff.mpr fun n => by
        by_cases hn : j ≤ n
        · exact (hR k n hn).mono fun z hz _ => hz
        · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
    filter_upwards [future_limit P Y k,hall] with z hz hb
    exact le_of_tendsto ((hz.sub tendsto_const_nhds).abs)
      (eventually_atTop.mpr ⟨j,fun n hn => hb n hn⟩)
  constructor
  · filter_upwards [full_future_limit P Y, future_limit P Y j, ae_all_iff.mpr firstL]
      with z hf hl hb
    exact le_of_tendsto ((hf.sub hl).abs) (Filter.Eventually.of_forall hb)
  · filter_upwards [full_past_limit P Y, past_limit P Y j, ae_all_iff.mpr firstR]
      with z hf hr hb
    exact le_of_tendsto ((hf.sub hr).abs) (Filter.Eventually.of_forall hb)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleHalfLines
