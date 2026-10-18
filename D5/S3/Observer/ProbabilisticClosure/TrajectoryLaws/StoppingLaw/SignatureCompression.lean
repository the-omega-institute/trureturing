/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/ComponentPacking/TargetFixedPacking]
   utility: none
   digest: A single bias-independent tree relabeling preserves both phase signatures within a uniform window. -/


import D5.S3.Combinatorics.Graph.ComponentPacking.TargetFixedPacking
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

/-! Both phase packings assign one actual address to every potential node before execution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Classical MeasureTheory
open D5.S3.Combinatorics.Graph.ComponentPacking

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

namespace ReadTree

/-- Count occurrences, including repeated addresses and mutually incompatible branches. -/
def readCount : ReadTree → ℕ
  | .leaf _ => 0
  | .read _ z o => z.readCount + o.readCount + 1

/-- Relabel every occurrence while preserving the ordered tree and all terminals. -/
private def relabel (f : ℤ → ℤ) : ReadTree → ReadTree
  | .leaf a => .leaf a
  | .read t z o => .read (f t) (z.relabel f) (o.relabel f)

private theorem relabel_height (f : ℤ → ℤ) (T : ReadTree) :
    (T.relabel f).height = T.height := by
  induction T with
  | leaf _ => rfl
  | read t z o hz ho => simp only [relabel, height, hz, ho]

private theorem relabel_addresses (f : ℤ → ℤ) (T : ReadTree) :
    (T.relabel f).addresses = T.addresses.image f := by
  induction T with
  | leaf _ => simp [relabel, addresses]
  | read t z o hz ho => simp only [relabel, addresses, hz, ho,
      Finset.image_insert, Finset.image_union]

private theorem addressAt_relabel (f : ℤ → ℤ) (T : ReadTree) (p : ReadPosition) :
    (T.relabel f).addressAt p = (T.addressAt p).map f := by
  induction T generalizing p with
  | leaf _ => rfl
  | read t z o hz ho =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp only [relabel, addressAt, hz, ho]

theorem addressAt_in_addresses (T : ReadTree) (p : ReadPosition) (t : ℤ)
    (h : T.addressAt p = some t) : t ∈ T.addresses := by
  induction T generalizing p with
  | leaf _ => simp [addressAt] at h
  | read a z o hz ho =>
    cases p with
    | nil => have : a = t := Option.some.inj h; subst t; exact Finset.mem_insert_self _ _
    | cons b p =>
      cases b
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hz p h))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ho p h))

private theorem addresses_card_le_readCount (T : ReadTree) : T.addresses.card ≤ T.readCount := by
  induction T with
  | leaf _ => simp [addresses, readCount]
  | read t z o hz ho =>
    have h₁ := Finset.card_insert_le t (z.addresses ∪ o.addresses)
    have h₂ := Finset.card_union_le z.addresses o.addresses
    change (insert t (z.addresses ∪ o.addresses)).card ≤ z.readCount + o.readCount + 1
    omega

private theorem readCount_height_bound (T : ReadTree) : T.readCount + 1 ≤ 2 ^ T.height := by
  induction T with
  | leaf _ => simp [readCount, height]
  | read t z o hz ho =>
    have hz' : 2 ^ z.height ≤ 2 ^ max z.height o.height :=
      Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have ho' : 2 ^ o.height ≤ 2 ^ max z.height o.height :=
      Nat.pow_le_pow_right (by decide) (le_max_right _ _)
    simp only [readCount, height, pow_succ]
    omega

private theorem skeleton_relabel (f : ℤ → ℤ) (T : ReadTree)
    (hf : ∀ t ∈ T.addresses, f t % 2 = t % 2) :
    (T.relabel f).paritySkeleton = T.paritySkeleton := by
  induction T with
  | leaf _ => rfl
  | read t z o hz ho =>
    have ht := hf t (Finset.mem_insert_self _ _)
    have hZ := hz (fun a ha => hf a (Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)))
    have hO := ho (fun a ha => hf a (Finset.mem_insert_of_mem (Finset.mem_union_right _ ha)))
    simp only [relabel, paritySkeleton, ht, hZ, hO]

end ReadTree

private def addressParity (t : ℤ) : Bool := decide (t % 2 = 1)

private theorem parity_value (t : ℤ) : (addressParity t).toInt = t % 2 := by
  have hlo := Int.emod_nonneg t (by decide : (2 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos t (by decide : (0 : ℤ) < 2)
  by_cases h : t % 2 = 1 <;> simp [addressParity, h] <;> omega

private theorem parity_of_active (t : ℤ) (φ : Bool)
    (active : (t - φ.toInt) % 2 = 0) : addressParity t = φ := by
  cases φ
  · change (t - 0) % 2 = 0 at active
    have ht : t % 2 = 0 := by omega
    simp [addressParity, ht]
  · change (t - 1) % 2 = 0 at active
    have ht : t % 2 = 1 := by omega
    simp [addressParity, ht]

private def phaseEdges (T : ReadTree) (φ : Bool) : Finset ℤ :=
  (T.addresses.filter (fun t => addressParity t = φ)).image (fun t => (t - φ.toInt) / 2)

private def phasePacking (j : Bool) (T : ReadTree) (φ : Bool) :
    CanonicalTargetPacking (phaseEdges T φ) (targetIndex j φ) :=
  Classical.choice (canonical_target_fixed_packing (phaseEdges T φ) (targetIndex j φ))

private def compressedAddress (j : Bool) (T : ReadTree) (t : ℤ) : ℤ :=
  2 * (phasePacking j T (addressParity t)).map ((t - (addressParity t).toInt) / 2) +
    (addressParity t).toInt

/-- This map has no bias parameter and produces a single actual integer tree. -/
def compressedTree (j : Bool) (T : ReadTree) : ReadTree := T.relabel (compressedAddress j T)

private theorem packed_target (j : Bool) (T : ReadTree) (φ : Bool) :
    (phasePacking j T φ).map (targetIndex j φ) = targetIndex j φ :=
  (phasePacking j T φ).fixed_target _
    (phasePacking j T φ).intervals.target_bounds.1
    (phasePacking j T φ).intervals.target_bounds.2

private theorem compressed_parity (j : Bool) (T : ReadTree) (t : ℤ) :
    compressedAddress j T t % 2 = t % 2 := by
  have hp := parity_value t
  unfold compressedAddress
  omega

private theorem phase_edge_mem (T : ReadTree) (t : ℤ) (ht : t ∈ T.addresses) :
    (t - (addressParity t).toInt) / 2 ∈ phaseEdges T (addressParity t) :=
  Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩, rfl⟩

private theorem slot_in_occupied (j φ : Bool) (T : ReadTree) (s : OrientedSlot) :
    slotIndex j φ T s ∈ occupiedVertices (phaseEdges T φ) (targetIndex j φ) := by
  cases s with
  | none => exact Finset.mem_insert_self _ _
  | some ps =>
    obtain ⟨p, side⟩ := ps
    cases ht : T.addressAt p with
    | none =>
      simpa only [slotIndex, ht, occupiedVertices] using
        (Finset.mem_insert_self (targetIndex j φ)
          (phaseEdges T φ ∪ (phaseEdges T φ).image (fun e => e + 1)))
    | some t =>
      by_cases active : (t - φ.toInt) % 2 = 0
      · have hp : addressParity t = φ := parity_of_active t φ active
        have he : (t - φ.toInt) / 2 ∈ phaseEdges T φ := by
          simpa only [hp] using phase_edge_mem T t (T.addressAt_in_addresses p t ht)
        cases side
        · simpa only [slotIndex, ht, occupiedVertices, ite_eq_left active,
            Bool.toInt_false, add_zero] using
            Finset.mem_insert_of_mem (Finset.mem_union_left
              ((phaseEdges T φ).image (fun e => e + 1)) he)
        · simpa only [slotIndex, ht, occupiedVertices, ite_eq_left active, Bool.toInt_true] using
            Finset.mem_insert_of_mem (Finset.mem_union_right (phaseEdges T φ)
              (Finset.mem_image.mpr ⟨(t - φ.toInt) / 2, he, rfl⟩))
      · simpa only [slotIndex, ht, occupiedVertices, ite_eq_right active] using
          (Finset.mem_insert_self (targetIndex j φ)
            (phaseEdges T φ ∪ (phaseEdges T φ).image (fun e => e + 1)))

private theorem packed_slot (j φ : Bool) (T : ReadTree) (s : OrientedSlot) :
    (phasePacking j T φ).map (slotIndex j φ T s) = slotIndex j φ (compressedTree j T) s := by
  cases s with
  | none => exact packed_target j T φ
  | some ps =>
    obtain ⟨p, side⟩ := ps
    have hr := ReadTree.addressAt_relabel (compressedAddress j T) T p
    change (compressedTree j T).addressAt p = (T.addressAt p).map (compressedAddress j T) at hr
    cases ht : T.addressAt p with
    | none =>
      simp only [ht, Option.map_none] at hr
      simpa only [slotIndex, ht, hr] using packed_target j T φ
    | some t =>
      simp only [ht, Option.map_some] at hr
      have hpar := compressed_parity j T t
      by_cases active : (t - φ.toInt) % 2 = 0
      · have hp : addressParity t = φ := parity_of_active t φ active
        have new_active : (compressedAddress j T t - φ.toInt) % 2 = 0 := by
          unfold compressedAddress
          rw [hp]
          omega
        have edge_pres := (phasePacking j T φ).edge_preserving _
          (by simpa only [hp] using phase_edge_mem T t (T.addressAt_in_addresses p t ht))
        have half : (compressedAddress j T t - φ.toInt) / 2 =
            (phasePacking j T φ).map ((t - φ.toInt) / 2) := by
          unfold compressedAddress
          rw [hp]
          omega
        cases side <;> simp only [slotIndex, ht, hr, ite_eq_left active,
          ite_eq_left new_active, Bool.toInt_false, Bool.toInt_true, add_zero, half, edge_pres]
      · have new_inactive : (compressedAddress j T t - φ.toInt) % 2 ≠ 0 := by omega
        simpa only [slotIndex, ht, hr, ite_eq_right active, ite_eq_right new_inactive]
          using packed_target j T φ

/-- The same bias-independent tree preserves both complete signatures and every
formal height, and all its potential addresses lie in the stated uniform window. -/
theorem bounded_signature_relabeling (j : Bool) (T : ReadTree) (k : ℕ)
    (hk : T.height ≤ k) :
    SameSignature j T (compressedTree j T) ∧ (compressedTree j T).height = T.height ∧
      ∀ t ∈ (compressedTree j T).addresses,
        j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
          t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1 := by
  have same : SameSignature j T (compressedTree j T) := by
    refine ⟨(T.skeleton_relabel _ (fun t _ => compressed_parity j T t)).symm, ?_⟩
    intro φ a b
    rw [← packed_slot j φ T a, ← packed_slot j φ T b]
    exact ⟨congrArg (phasePacking j T φ).map, fun h =>
      (phasePacking j T φ).injective (slot_in_occupied j φ T a)
        (slot_in_occupied j φ T b) h⟩
  refine ⟨same, ReadTree.relabel_height _ T, ?_⟩
  intro t ht
  rw [compressedTree, ReadTree.relabel_addresses] at ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  let φ := addressParity a
  have he := phase_edge_mem T a ha
  have hb := (phasePacking j T φ).edge_bounds _ he
  have hm : (phaseEdges T φ).card ≤ 2 ^ k - 1 := by
    have h₁ := Finset.card_image_le (s := T.addresses.filter (fun t => addressParity t = φ))
      (f := fun t => (t - φ.toInt) / 2)
    have h₂ := Finset.card_filter_le T.addresses (fun t => addressParity t = φ)
    have h₃ := T.addresses_card_le_readCount
    have h₄ := T.readCount_height_bound
    have h₅ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk
    change (phaseEdges T φ).card ≤ (T.addresses.filter (fun t => addressParity t = φ)).card at h₁
    omega
  have base : 2 * targetIndex j φ + φ.toInt = j.toInt ∨
      2 * targetIndex j φ + φ.toInt = j.toInt + 1 := by
    cases j <;> cases φ <;> norm_num [targetIndex]
  change j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤
      2 * (phasePacking j T φ).map ((a - φ.toInt) / 2) + φ.toInt ∧
    2 * (phasePacking j T φ).map ((a - φ.toInt) / 2) + φ.toInt ≤
      j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1
  dsimp only [φ] at *
  omega

#print axioms bounded_signature_relabeling

private theorem selector_signature_law {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (T S : U → ReadTree) (hT : Measurable T) (hS : Measurable S)
    (h : ∀ u, SameSignature j (T u) (S u)) :
    ((sourceLaw β).prod ν).map (selectorJoint j T) =
      ((sourceLaw β).prod ν).map (selectorJoint j S) := by
  ext B hB
  rw [Measure.map_apply (measurable_selectorJoint j T hT) hB,
    Measure.map_apply (measurable_selectorJoint j S hS) hB,
    Measure.prod_apply_symm ((measurable_selectorJoint j T hT) hB),
    Measure.prod_apply_symm ((measurable_selectorJoint j S hS) hB)]
  apply lintegral_congr
  intro u
  have hBu : MeasurableSet ((Prod.mk u) ⁻¹' B) :=
    (measurable_const.prodMk measurable_id) hB
  have he := congrArg (fun μ : Measure Observation => μ ((Prod.mk u) ⁻¹' B))
    (same_signature_observation_law j (T u) (S u) (h u) β)
  simpa only [Measure.map_apply (measurable_observation j (T u)) hBu,
    Measure.map_apply (measurable_observation j (S u)) hBu, selectorJoint,
    Set.preimage_preimage, Function.comp_def] using he

private theorem normalized_actual_radius {U : Type*} [MeasurableSpace U]
    (R : RawRule U) (k : ℕ) (hc : R.TotalCap k) (j : Bool) (ρ : ℕ)
    (hb : ∀ u : U, ∀ t ∈ (R.normalize k u).addresses, |t - j.toInt| ≤ (ρ : ℤ)) :
    R.WithinActualRadius j ρ := by
  intro φ S u n r hr a ha
  have hv := (R.normalization_pointwise k hc φ S u).1
  have hmem := R.completes_record_subset u (visible φ S) hv hr a ha
  exact hb u a.1 ((R.normalize k u).record_addresses (visible φ S) a hmem)

/-- Arbitrary completed input rules have representatives on the unchanged seed
space. Full joint law, nonreturn payment and all formal address bounds are retained. -/
private theorem compress_completed_rule {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (β : Bias) (j : Bool) (k : ℕ)
    (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν)) (hc : Q.TotalCap k) :
    ∃ R : RawRule U, R.Lawful ∧ R.TotalCap k ∧ R.fullLaw β j ν = Q.fullLaw β j ν ∧
      R.WithinActualRadius j (2 ^ (k + 1) - 1) ∧
      (k = 0 → R.WithinActualRadius j 0) ∧
      ∀ u : U, (R.normalize k u).height ≤ k ∧
        ∀ t ∈ (R.normalize k u).addresses,
          j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
            t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1 := by
  obtain ⟨T, hm, he⟩ := Q.normalization_version ((sourceLaw β).prod ν) hQ k
  let T₀ : U → ReadTree := fun u => (T u).val
  let S : U → ReadTree := fun u => compressedTree j (T₀ u)
  have hT₀ : Measurable T₀ := measurable_subtype_coe.comp hm
  have hS : Measurable S := (measurable_of_countable (compressedTree j)).comp hT₀
  have hcap (u : U) : (S u).height ≤ k := by
    rw [(bounded_signature_relabeling j (T₀ u) k (T u).property).2.1]
    exact (T u).property
  let R := RawRule.realize S
  have hcR : R.TotalCap k := RawRule.realize_cap S k hcap
  have formal (u : U) : (R.normalize k u).height ≤ k ∧
      ∀ t ∈ (R.normalize k u).addresses,
        j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
          t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1 := by
    change ((RawRule.realize S).normalize k u).height ≤ k ∧ _
    rw [RawRule.normalize_realize S k u (hcap u)]
    exact ⟨hcap u, (bounded_signature_relabeling j (T₀ u) k (T u).property).2.2⟩
  refine ⟨R, RawRule.realize_lawful S hS, hcR, ?_, ?_, ?_, formal⟩
  · have hj : Q.completedJoint j =ᵐ[(sourceLaw β).prod ν] selectorJoint j T₀ := by
      filter_upwards [he] with p hp
      rw [Q.completed_joint_normalize k hc j p, hp]
      rfl
    calc
      R.fullLaw β j ν = ((sourceLaw β).prod ν).map (selectorJoint j S) :=
        RawRule.fullLaw_realize S k hcap β j ν
      _ = ((sourceLaw β).prod ν).map (selectorJoint j T₀) :=
        (selector_signature_law β j ν T₀ S hT₀ hS
          (fun u => (bounded_signature_relabeling j (T₀ u) k (T u).property).1)).symm
      _ = Q.fullLaw β j ν := (Measure.map_congr hj).symm
  · apply normalized_actual_radius R k hcR j
    intro u t ht
    have hb := (formal u).2 t ht
    have hp : 0 < 2 ^ k := pow_pos (by decide) _
    have heq : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by rw [pow_succ]; omega
    rw [← heq]
    push_cast
    exact abs_le.mpr ⟨by omega, by omega⟩
  · intro hk
    apply normalized_actual_radius R k hcR j
    intro u t ht
    have hh := (formal u).1
    cases htree : R.normalize k u with
    | leaf a => simp [htree, ReadTree.addresses] at ht
    | read a z o => simp only [htree, ReadTree.height] at hh; omega

/-- The comparison class fixes the entire seed space and full joint law, while
allowing different adaptive rules and imposing only an actual address radius. -/
def UniversalRadius {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) (k ρ : ℕ) : Prop :=
  ∀ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) → Q.TotalCap k →
    ∃ R : CompletedRule U, R.Lawful ((sourceLaw β).prod ν) ∧ R.TotalCap k ∧
      R.fullLaw β j ν = Q.fullLaw β j ν ∧ R.CompletedWithinActualRadius j ρ

private theorem universal_radius_upper {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (k : ℕ) :
    UniversalRadius β j ν k (2 ^ (k + 1) - 1) := by
  intro Q hQ hc
  obtain ⟨R, hR, hcap, hlaw, hradius, _⟩ :=
    compress_completed_rule ν β j k Q hQ hc
  refine ⟨CompletedRule.fromRaw R, CompletedRule.fromRaw_lawful R hR _, ?_, hlaw, ?_⟩
  · intro s u
    exact hcap s.1 s.2 u
  · intro s u n r hr a ha
    exact hradius s.1 s.2 u n r hr a ha

private theorem universal_radius_exists {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (k : ℕ) :
    ∃ ρ : ℕ, UniversalRadius β j ν k ρ := ⟨_, universal_radius_upper β j ν k⟩

/-- A least natural radius is taken only after uniform nonemptiness is proved. -/
def rhoLaw {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (k : ℕ) : ℕ :=
  Nat.find (universal_radius_exists β j ν k)

private theorem universal_radius_lower {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℕ) (hρ : UniversalRadius β j ν k ρ) :
    2 * k + 1 ≤ ρ := by
  have hw := CompletedRule.completed_stopping_witness_exact_radius β j k hk ν
  obtain ⟨W, hW, hcW, hlawW, _⟩ := hw.1
  obtain ⟨P, hP, hcP, hlawP, hradiusP⟩ := hρ W hW hcW
  exact hw.2 ⟨P, hP, hcP, hlawP.trans hlawW, hradiusP⟩

/-- Uniform compression uses the original seed and actual replies. The same
construction supplies the universal upper bound and the exact small budgets. -/
theorem completed_rule_uniform_compression {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (β : Bias) (j : Bool) (k : ℕ) :
    (∀ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) → Q.TotalCap k →
      ∃ R : RawRule U, R.Lawful ∧ R.TotalCap k ∧ R.fullLaw β j ν = Q.fullLaw β j ν ∧
      R.WithinActualRadius j (2 ^ (k + 1) - 1) ∧
      (k = 0 → R.WithinActualRadius j 0) ∧
      ∀ u : U, (R.normalize k u).height ≤ k ∧
        ∀ t ∈ (R.normalize k u).addresses,
          j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
            t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1) ∧
    rhoLaw β j ν 0 = 0 ∧ rhoLaw β j ν 1 = 3 ∧
    (1 ≤ k → 2 * k + 1 ≤ rhoLaw β j ν k) ∧
    rhoLaw β j ν k ≤ 2 ^ (k + 1) - 1 := by
  have zero : UniversalRadius β j ν 0 0 := by
    intro A hA hcA
    obtain ⟨R, hR, hcap, hlaw, _, hzero, _⟩ :=
      compress_completed_rule ν β j 0 A hA hcA
    refine ⟨CompletedRule.fromRaw R, CompletedRule.fromRaw_lawful R hR _, ?_, hlaw, ?_⟩
    · intro s u
      exact hcap s.1 s.2 u
    · intro s u n r hr a ha
      exact hzero rfl s.1 s.2 u n r hr a ha
  have lower (n : ℕ) (hn : 1 ≤ n) : 2 * n + 1 ≤ rhoLaw β j ν n :=
    universal_radius_lower β j ν n hn _ (Nat.find_spec (universal_radius_exists β j ν n))
  have upper (n : ℕ) : rhoLaw β j ν n ≤ 2 ^ (n + 1) - 1 :=
    Nat.find_min' (universal_radius_exists β j ν n) (universal_radius_upper β j ν n)
  refine ⟨(fun Q hQ hc => compress_completed_rule ν β j k Q hQ hc),
    ?_, ?_, lower k, upper k⟩
  · exact Nat.le_zero.mp (Nat.find_min' (universal_radius_exists β j ν 0) zero)
  · have hl := lower 1 (by decide)
    have hu := upper 1
    norm_num at hl hu
    omega

#print axioms completed_rule_uniform_compression

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
