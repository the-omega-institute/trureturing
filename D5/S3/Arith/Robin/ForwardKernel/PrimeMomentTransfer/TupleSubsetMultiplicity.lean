/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Subsets of tuple ranges have uniformly bounded multiplicity in finite boxes. -/

import D5.S0.Diagonal.RecordExtensionCount
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! Counting finite-box tuples containing a prescribed set of values. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

lemma forced_tuple_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (S : Finset α) (R : Finset ι) (v : ι → α) :
    ((Fintype.piFinset (fun _ : ι => S)).filter
      (fun d => ∀ i ∈ R, d i = v i)).card ≤ S.card ^ (Fintype.card ι - R.card) := by
  classical
  let T := (Fintype.piFinset (fun _ : ι => S)).filter
    (fun d => ∀ i ∈ R, d i = v i)
  change T.card ≤ _
  by_cases hT : T.Nonempty
  · obtain ⟨d, hd⟩ := hT
    let prescribed : ι → ↥S := fun i =>
      ⟨d i, Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i⟩
    letI : Finite (D5.S0.Diagonal.RecordExtensionCount.RecordExtensions R prescribed) := by
      unfold D5.S0.Diagonal.RecordExtensionCount.RecordExtensions
      infer_instance
    let f : ↥T → D5.S0.Diagonal.RecordExtensionCount.RecordExtensions R prescribed :=
      fun e => ⟨fun i =>
        ⟨e.val i, Fintype.mem_piFinset.mp (Finset.mem_filter.mp e.property).1 i⟩,
        by
          intro i hi
          apply Subtype.ext
          exact ((Finset.mem_filter.mp e.property).2 i hi).trans
            ((Finset.mem_filter.mp hd).2 i hi).symm⟩
    have hf : Function.Injective f := by
      intro e g h
      apply Subtype.ext
      funext i
      exact congrArg (fun x => (x.val i).val) h
    calc
      T.card = Nat.card ↥T := by simp
      _ ≤ Nat.card (D5.S0.Diagonal.RecordExtensionCount.RecordExtensions R prescribed) :=
        Nat.card_le_card_of_injective f hf
      _ = _ := by
        rw [D5.S0.Diagonal.RecordExtensionCount.record_extension_card,
          Fintype.card_coe]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.card_empty]
    exact Nat.zero_le _

/-- A prescribed set of `r` values can occur in a box tuple at most `k^r K^(k-r)` times.
The factor `k^r` counts possible choices of positions for those values. -/
theorem tuple_range_superset_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] [Nonempty α] (S R : Finset α) :
    ((Fintype.piFinset (fun _ : ι => S)).filter
      (fun d => R ⊆ Finset.univ.image d)).card ≤
        (Fintype.card ι) ^ R.card * S.card ^ (Fintype.card ι - R.card) := by
  classical
  let E : Finset (R → ι) := Finset.univ.filter Function.Injective
  let T := Fintype.piFinset (fun _ : ι => S)
  let U : (R → ι) → Finset (ι → α) := fun e =>
    T.filter (fun d => ∀ v : R, d (e v) = v.val)
  have hcover : T.filter (fun d => R ⊆ Finset.univ.image d) ⊆ E.biUnion U := by
    intro d hd
    have hr := (Finset.mem_filter.mp hd).2
    have hx (v : R) : ∃ i : ι, d i = v.val := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hr v.property)
      exact ⟨i, hi⟩
    choose e he using hx
    apply Finset.mem_biUnion.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, he⟩⟩
    intro v w hvw
    apply Subtype.ext
    exact (he v).symm.trans ((congrArg d hvw).trans (he w))
  have hU (e : R → ι) (he : e ∈ E) :
      (U e).card ≤ S.card ^ (Fintype.card ι - R.card) := by
    have hinj := (Finset.mem_filter.mp he).2
    let I : Finset ι := Finset.univ.image e
    let v : ι → α := fun i => if h : ∃ x : R, e x = i then h.choose.val else
      Classical.choice (inferInstance : Nonempty α)
    have hv (x : R) : v (e x) = x.val := by
      simp only [v, dite_eq_left (show ∃ y : R, e y = e x from ⟨x, rfl⟩)]
      congr 1
      apply hinj
      exact (Exists.choose_spec (show ∃ y : R, e y = e x from ⟨x, rfl⟩))
    have hsub : U e ⊆ T.filter (fun d => ∀ i ∈ I, d i = v i) := by
      intro d hd
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, ?_⟩
      intro i hi
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
      rw [hv]
      exact (Finset.mem_filter.mp hd).2 x
    have hI : I.card = R.card := by simp [I, Finset.card_image_of_injective _ hinj]
    exact (Finset.card_le_card hsub).trans (by
      simpa only [hI] using forced_tuple_card_le S I v)
  calc
    _ ≤ (E.biUnion U).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ E, (U e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E, S.card ^ (Fintype.card ι - R.card) := Finset.sum_le_sum hU
    _ = E.card * S.card ^ (Fintype.card ι - R.card) := by simp
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Summing an error over every subset of a tuple range costs only the number of unused
coordinates. The estimate is valid for every subfamily of the box, hence for interval boxes. -/
theorem sum_tuple_subsets_le (k : ℕ) (S : Finset ℕ)
    (T : Finset (Fin k → ℕ))
    (hT : T ⊆ Fintype.piFinset (fun _ : Fin k => S))
    (e : Finset ℕ → ℝ) (he : ∀ R, 0 ≤ e R) :
    (∑ d ∈ T, ∑ R ∈ (Finset.univ.image d).powerset, e R) ≤
      (k : ℝ) ^ k * ∑ r ∈ Finset.range (k + 1), (S.card : ℝ) ^ (k - r) *
        ∑ R ∈ S.powersetCard r, e R := by
  classical
  have hsize (d : Fin k → ℕ) : (Finset.univ.image d).card ≤ k := by
    exact Finset.card_image_le.trans (by simp)
  have hsplit (d : Fin k → ℕ) :
      (∑ R ∈ (Finset.univ.image d).powerset, e R) =
        ∑ r ∈ Finset.range (k + 1), ∑ R ∈ (Finset.univ.image d).powersetCard r, e R := by
    symm
    simp_rw [Finset.powersetCard_eq_filter]
    apply Finset.sum_fiberwise_of_maps_to
    intro R hR
    exact Finset.mem_range.mpr (by
      have := (Finset.card_le_card (Finset.mem_powerset.mp hR)).trans (hsize d)
      omega)
  have hbox (d : Fin k → ℕ) (hd : d ∈ T) : Finset.univ.image d ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Fintype.mem_piFinset.mp (hT hd) i
  have hsum (d : Fin k → ℕ) (hd : d ∈ T) (r : ℕ) :
      (∑ R ∈ (Finset.univ.image d).powersetCard r, e R) =
        ∑ R ∈ S.powersetCard r, if R ⊆ Finset.univ.image d then e R else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext R
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨⟨h.1.trans (hbox d hd), h.2⟩, h.1⟩,
      fun h => ⟨h.2, h.1.2⟩⟩
  have hc (r : ℕ) (hr : r ∈ Finset.range (k + 1)) (R : Finset ℕ)
      (hR : R ∈ S.powersetCard r) :
      ((T.filter (fun d => R ⊆ Finset.univ.image d)).card : ℝ) ≤
        (k : ℝ) ^ k * (S.card : ℝ) ^ (k - r) := by
    have hsub : T.filter (fun d => R ⊆ Finset.univ.image d) ⊆
        (Fintype.piFinset (fun _ : Fin k => S)).filter
          (fun d => R ⊆ Finset.univ.image d) := Finset.filter_subset_filter _ hT
    have h := (Finset.card_le_card hsub).trans
      (tuple_range_superset_card_le (ι := Fin k) S R)
    have hRr := (Finset.mem_powersetCard.mp hR).2
    simp only [Fintype.card_fin, hRr] at h
    have hp : k ^ r ≤ k ^ k := by
      have hrk : r ≤ k := by have := Finset.mem_range.mp hr; omega
      by_cases hk : k = 0
      · have hr0 : r = 0 := by omega
        simp [hk, hr0]
      · exact Nat.pow_le_pow_right (by omega) hrk
    exact_mod_cast h.trans (Nat.mul_le_mul_right _ hp)
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r ∈ Finset.range (k + 1), ∑ R ∈ S.powersetCard r,
        ((T.filter (fun d => R ⊆ Finset.univ.image d)).card : ℝ) * e R := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ∑ d ∈ T, ∑ R ∈ S.powersetCard r,
            if R ⊆ Finset.univ.image d then e R else 0 :=
          Finset.sum_congr rfl (fun d hd => hsum d hd r)
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro R _
          rw [← Finset.sum_filter]
          simp
    _ ≤ ∑ r ∈ Finset.range (k + 1), ∑ R ∈ S.powersetCard r,
        ((k : ℝ) ^ k * (S.card : ℝ) ^ (k - r)) * e R := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.sum_le_sum (fun R hR => mul_le_mul_of_nonneg_right (hc r hr R hR) (he R))
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
