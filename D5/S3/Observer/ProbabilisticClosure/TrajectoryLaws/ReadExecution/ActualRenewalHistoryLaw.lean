/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalHistoryLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual finite raw history determines every epoch prefix and its cylinder law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw
open ActualRenewalStopping ActualRenewalPrefixLaw

variable {S R Ω : Type*}

private def fillGaps {n : ℕ} (v : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : j < n then v ⟨j, h⟩ else 0

private def clippedIndex {n : ℕ} (u : ℕ) (v : Fin n → ℕ) (t : ℕ) : Fin (cut u v) :=
  if h : t < cut u v then ⟨t, h⟩ else ⟨0, by unfold cut; omega⟩

/-- The literal epoch prefix, including epoch zero. -/
def epochHistory (labels : Set S) (update : S → Bool → R → S)
    (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (n : ℕ) (ω : Ω) : Fin (n + 1) → S :=
  fun j => epoch labels update (I ω) (ξ ω) (τ ω) (K ω) j.val

private def localHistory (labels : Set S) (update : S → Bool → R → S)
    (n : ℕ) (a : ℕ × (Fin n → ℕ)) (p : S × (Fin (cut a.1 a.2) → R)) :
    Fin (n + 1) → S :=
  fun j => epoch labels update p.1 (fun t => p.2 (clippedIndex a.1 a.2 t))
    a.1 (fillGaps a.2) j.val

private theorem local_history_eq (labels : Set S) (update : S → Bool → R → S)
    (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (n : ℕ) (a : ℕ × (Fin n → ℕ)) (ω : Ω)
    (ha : ω ∈ sourceSlice τ K n a) :
    localHistory labels update n a (rawPrefix I ξ (cut a.1 a.2) ω) =
      epochHistory labels update I τ K ξ n ω := by
  have hgap (j : ℕ) (hj : j < n) : fillGaps a.2 j = K ω j := by
    simp only [fillGaps, dif_pos hj]
    exact (ha.2 ⟨j, hj⟩).symm
  have hc (j : ℕ) (hj : j ≤ n) :
      clock a.1 (fillGaps a.2) j = clock (τ ω) (K ω) j := by
    induction j with
    | zero => simp only [clock, ha.1]
    | succ j ih => rw [clock, clock, ih (by omega), hgap j (by omega)]
  have hcut : clock (τ ω) (K ω) n = cut a.1 a.2 := by
    rw [clock_cut, ha.1]
    congr 1
    exact funext ha.2
  have hcoin (t : ℕ) (ht : t < cut a.1 a.2) :
      (rawPrefix I ξ (cut a.1 a.2) ω).2 (clippedIndex a.1 a.2 t) = ξ ω t := by
    simp only [rawPrefix, clippedIndex, dif_pos ht]
  have hstate (j : ℕ) (hj : j ≤ n) :
      epoch labels update (I ω)
          (fun t => (rawPrefix I ξ (cut a.1 a.2) ω).2 (clippedIndex a.1 a.2 t))
          a.1 (fillGaps a.2) j =
        epoch labels update (I ω) (ξ ω) (τ ω) (K ω) j := by
    induction j with
    | zero =>
      rw [(actual_words labels update _ _ _ _).1,
        (actual_words labels update _ _ _ _).1, ha.1]
      congr 1
      funext t
      apply hcoin
      have : a.1 + 1 ≤ cut a.1 a.2 := by unfold cut; omega
      omega
    | succ j ih =>
      rw [(actual_words labels update _ _ _ _).2,
        (actual_words labels update _ _ _ _).2,
        hgap j (by omega), ih (by omega)]
      congr 1
      funext t
      rw [hc j (by omega)]
      apply hcoin
      have hb := (clock_strict (τ ω) (K ω)).monotone hj
      simp only [clock] at hb
      omega
  funext j
  exact hstate j.val (by omega)

section Measurability
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace R]
    (labels : Set S) (update : S → Bool → R → S)
    (heff : ∀ b, Measurable (fun p : S × R => effective labels update p.1 b p.2))

private theorem local_history_measurable (n : ℕ) (a : ℕ × (Fin n → ℕ)) :
    Measurable (localHistory labels update n a) := by
  have hr (t : ℕ) : Measurable (fun p : S × (Fin (cut a.1 a.2) → R) =>
      run labels update p.1 (fun t => p.2 (clippedIndex a.1 a.2 t))
        a.1 (fillGaps a.2) t) := by
    induction t with
    | zero => exact measurable_fst
    | succ t ih =>
      exact (heff (sourceBit a.1 (fillGaps a.2) t)).comp
        (ih.prodMk ((measurable_pi_apply (clippedIndex a.1 a.2 t)).comp measurable_snd))
  exact measurable_pi_iff.mpr fun j => hr _

/-- On each finite source slice every ordinary epoch-history event is an event
    of the initial state and coins strictly before the actual next-block cut.
    Source coordinates may also be observed; the next gap is excluded. -/
theorem actual_history_locality
    (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (n : ℕ) (B : Set ((ℕ × (Fin n → ℕ)) × (Fin (n + 1) → S)))
    (hB : MeasurableSet B) :
    ∃ D : (a : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut a.1 a.2) → R)),
      (∀ a, MeasurableSet (D a)) ∧
      {ω | ((τ ω, fun j : Fin n => K ω j.val),
          epochHistory labels update I τ K ξ n ω) ∈ B} =
        pastEvent I τ K ξ n D := by
  let D := fun a : ℕ × (Fin n → ℕ) =>
    (fun p => (a, localHistory labels update n a p)) ⁻¹' B
  refine ⟨D, fun a => hB.preimage
    (measurable_const.prodMk (local_history_measurable labels update heff n a)), ?_⟩
  ext ω
  simp only [pastEvent, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_setOf_eq]
  constructor
  · intro h
    let a : ℕ × (Fin n → ℕ) := (τ ω, fun j => K ω j.val)
    have ha : ω ∈ sourceSlice τ K n a := ⟨rfl, fun _ => rfl⟩
    refine ⟨a, ha, ?_⟩
    change (a, localHistory labels update n a (rawPrefix I ξ (cut a.1 a.2) ω)) ∈ B
    rw [local_history_eq labels update I τ K ξ n a ω ha]
    exact h
  · rintro ⟨a, ha, h⟩
    change (a, localHistory labels update n a (rawPrefix I ξ (cut a.1 a.2) ω)) ∈ B at h
    rw [local_history_eq labels update I τ K ξ n a ω ha] at h
    have he : (τ ω, fun j : Fin n => K ω j.val) = a :=
      Prod.ext ha.1 (funext ha.2)
    rwa [he]

end Measurability
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw
