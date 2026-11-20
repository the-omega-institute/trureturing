/- GID: D5/S3/TotalVariation/ParityBiasComponents
   generality: G
   mirror-B: D5/B/S3/TotalVariation/ParityBiasComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-column affine parity laws have contractible sign components. -/

import D5.S3.TotalVariation.MinimumParityRealizations
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Contractible

/-! Connected components of the bias vectors realizing a fixed law at fixed columns and offset. -/

set_option autoImplicit false

open scoped BigOperators unitInterval

namespace D5.S3.TotalVariation.ParityBiasComponents

open D5.S3.TotalVariation.GroupedParityBias
open D5.S3.TotalVariation.MinimumParityInputs
open D5.S3.TotalVariation.MinimumParityRealizations
open D5.S3.TotalVariation.QuotientParitySpectrum

universe u v

variable {A : Type u} {L : Type v}
  [AddCommGroup A] [Fintype A] [Module (ZMod 2) A] [Fintype L]

/-- Signed bias vectors giving the reference law with the prescribed columns and offset. -/
def BiasFiber (c : L → A) (s : A) (q₀ : L → ℝ) : Set (L → ℝ) :=
  {q | (∀ i, |q i| ≤ 1) ∧ law c s q = law c s q₀}

private abbrev External (H : AddSubgroup A) (c : L → A) := {i : L // c i ∉ H}

private noncomputable def negativeProjection (H : AddSubgroup A) (c : L → A) (q : L → ℝ) :
    A ⧸ H := by
  classical
  exact ∑ i with q i < 0, QuotientAddGroup.mk' H (c i)

private theorem quotient_zero {H : AddSubgroup A} {a : A} :
    QuotientAddGroup.mk' H a = 0 ↔ a ∈ H := by
  change a ∈ (QuotientAddGroup.mk' H).ker ↔ a ∈ H
  rw [QuotientAddGroup.ker_mk']

private theorem fair_mem (c : L → A) (q : L → ℝ) (i : L) (hi : q i = 0) :
    c i ∈ fairSpan c q :=
  AddSubgroup.subset_closure ⟨i, hi, rfl⟩

private theorem law_iff_quotient_coordinates (c : L → A) (s : A) (q₀ q : L → ℝ) :
    let H := fairSpan c q₀
    let π := QuotientAddGroup.mk' H
    law c s q = law c s q₀ ↔ fairSpan c q = H ∧
      negativeProjection H c q = negativeProjection H c q₀ ∧
      ∀ a : A ⧸ H, a ≠ 0 → |groupBias (π ∘ c) q a| = |groupBias (π ∘ c) q₀ a| := by
  classical
  intro H π
  let two : ∀ a : A, a + a = 0 := ZModModule.add_self
  constructor
  · intro he
    have hH : fairSpan c q = H := by
      rw [fairSpan_eq_spectralAnnihilator two, he, ← fairSpan_eq_spectralAnnihilator two]
    refine ⟨hH, ?_, ?_⟩
    · let a := s + ∑ i with q i < 0, c i
      let b := s + ∑ i with q₀ i < 0, c i
      have ha (χ : AddChar A ℂ) (hn : moment (law c s q₀) χ ≠ 0) :
          0 < sign χ a * moment (law c s q₀) χ := by
        rw [← he]
        exact corrected_offset_positive two c s q χ (by rwa [he])
      have hb (χ : AddChar A ℂ) (hn : moment (law c s q₀) χ ≠ 0) :
          0 < sign χ b * moment (law c s q₀) χ :=
        corrected_offset_positive two c s q₀ χ hn
      have hm := signed_offsets_agree_modulo_annihilator two (law c s q₀) a b ha hb
      rw [← fairSpan_eq_spectralAnnihilator two c s q₀] at hm
      have hz : π (a - b) = 0 := quotient_zero.mpr hm
      dsimp only [a, b] at hz
      rw [map_sub, sub_eq_zero, map_add, map_add, add_right_inj, map_sum, map_sum] at hz
      exact hz
    · intro a ha
      have hq := visibleBias_recovered two c s q
      rw [hH, he] at hq
      exact (hq a ha).symm.trans (visibleBias_recovered two c s q₀ a ha)
  · rintro ⟨hH, hneg, hb⟩
    symm
    apply law_eq_of_matching_quotient_data two c s q₀ c s q hH
    · apply quotient_zero.mp
      change π ((s + ∑ i with q₀ i < 0, c i) - (s + ∑ i with q i < 0, c i)) = 0
      simp only [map_sub, map_add, map_sum, sub_eq_zero, add_right_inj]
      exact hneg.symm
    · intro a ha
      exact (hb a ha).symm

variable (c : L → A) (s : A) (q₀ : L → ℝ)

private theorem fiber_fairSpan (q : BiasFiber c s q₀) : fairSpan c q.val = fairSpan c q₀ :=
  ((law_iff_quotient_coordinates c s q₀ q.val).mp q.property.2).1

private theorem nonzero_external (q : BiasFiber c s q₀) (i : L)
    (hi : c i ∉ fairSpan c q₀) : q.val i ≠ 0 := by
  intro hz
  apply hi
  rw [← fiber_fairSpan c s q₀ q]
  exact fair_mem c q.val i hz

/-- The part of the fiber fixing the signs at all labels with nonzero quotient columns. -/
def signSector (p : BiasFiber c s q₀) : Set (BiasFiber c s q₀) :=
  {q | ∀ i, c i ∉ fairSpan c q₀ → (q.val i < 0 ↔ p.val i < 0)}

private theorem signSector_clopen (p : BiasFiber c s q₀) : IsClopen (signSector c s q₀ p) := by
  classical
  let H := fairSpan c q₀
  let ev (i : External H c) (q : BiasFiber c s q₀) := q.val i.val
  have hcont (i : External H c) : Continuous (ev i) :=
    (continuous_apply i.val).comp continuous_subtype_val
  have hset : signSector c s q₀ p = ⋂ i : External H c,
      if p.val i.val < 0 then (ev i) ⁻¹' Set.Iio 0 else (ev i) ⁻¹' Set.Ioi 0 := by
    ext q
    simp only [Set.mem_iInter]
    constructor
    · intro h i
      have hi := h i.val i.property
      split_ifs with hp
      · exact hi.mpr hp
      · exact lt_of_le_of_ne (le_of_not_gt (fun hn => hp (hi.mp hn)))
          (nonzero_external c s q₀ q i.val i.property).symm
    · intro h i hi
      specialize h ⟨i, hi⟩
      by_cases hp : p.val i < 0
      · exact iff_of_true (by simpa [hp, ev] using h) hp
      · exact iff_of_false (by
          have hq : 0 < q.val i := by simpa [hp, ev] using h
          exact not_lt.mpr hq.le) hp
  have hclosed : signSector c s q₀ p = ⋂ i : External H c,
      if p.val i.val < 0 then (ev i) ⁻¹' Set.Iic 0 else (ev i) ⁻¹' Set.Ici 0 := by
    rw [hset]
    congr 1
    funext i
    split_ifs
    · ext q
      exact lt_iff_le_and_ne.trans (and_iff_left (nonzero_external c s q₀ q i.val i.property))
    · ext q
      exact lt_iff_le_and_ne.trans (and_iff_left (nonzero_external c s q₀ q i.val i.property).symm)
  constructor
  · rw [hclosed]
    apply isClosed_iInter
    intro i
    split_ifs
    · exact isClosed_Iic.preimage (hcont i)
    · exact isClosed_Ici.preimage (hcont i)
  · rw [hset]
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact isOpen_Iio.preimage (hcont i)
    · exact isOpen_Ioi.preimage (hcont i)

private theorem projected_sign_agreement {H : AddSubgroup A} {q p : L → ℝ}
    (h : ∀ i, c i ∉ H → (q i < 0 ↔ p i < 0)) :
    negativeProjection H c q = negativeProjection H c p := by
  classical
  unfold negativeProjection
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c i ∈ H
  · have hzero := quotient_zero.mpr hi
    simp [hzero]
  · by_cases hp : p i < 0
    · simp [hp, (h i hi).mpr hp]
    · have hq : ¬ q i < 0 := fun hn => hp ((h i hi).mp hn)
      rw [ite_eq_right hq, ite_eq_right hp]

private noncomputable def deform (p q : L → ℝ) (t : unitInterval) (i : L) : ℝ := by
  classical
  exact if c i ∈ fairSpan c q₀ then (1 - t.val) * q i else
    (if p i < 0 then -1 else 1) *
      Real.exp ((1 - t.val) * Real.log |q i| + t.val * Real.log |p i|)

private theorem deform_external_abs {p q : L → ℝ} (t : unitInterval) (i : L)
    (hi : c i ∉ fairSpan c q₀) :
    |deform c q₀ p q t i| =
      Real.exp ((1 - t.val) * Real.log |q i| + t.val * Real.log |p i|) := by
  rw [deform, if_neg hi, abs_mul, abs_of_pos (Real.exp_pos _)]
  split_ifs <;> norm_num

private theorem deform_external_sign {p q : L → ℝ} (t : unitInterval) (i : L)
    (hi : c i ∉ fairSpan c q₀) :
    deform c q₀ p q t i < 0 ↔ p i < 0 := by
  rw [deform, if_neg hi]
  have hp := Real.exp_pos ((1 - t.val) * Real.log |q i| + t.val * Real.log |p i|)
  split_ifs with hh
  · exact iff_of_true (by simpa only [neg_one_mul, neg_lt_zero] using hp) hh
  · exact iff_of_false (by simpa only [one_mul, not_lt] using hp.le) hh

private theorem deform_fairSpan (p q : BiasFiber c s q₀) (t : unitInterval) :
    fairSpan c (deform c q₀ p.val q.val t) = fairSpan c q₀ := by
  classical
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, hz, rfl⟩
    by_contra h
    change c i ∉ fairSpan c q₀ at h
    have ha := deform_external_abs c q₀ (p := p.val) (q := q.val) t i h
    rw [hz, abs_zero] at ha
    exact (Real.exp_pos _).ne' ha.symm
  · rw [← fiber_fairSpan c s q₀ q]
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, hz, rfl⟩
    apply fair_mem c (deform c q₀ p.val q.val t) i
    have hi : c i ∈ fairSpan c q₀ := by
      rw [← fiber_fairSpan c s q₀ q]
      exact fair_mem c q.val i hz
    simp [deform, hi, hz]

private theorem deform_abs_le_one (p q : BiasFiber c s q₀) (t : unitInterval) (i : L) :
    |deform c q₀ p.val q.val t i| ≤ 1 := by
  classical
  have h₀ : 0 ≤ t.val := t.property.1
  have h₁ : t.val ≤ 1 := t.property.2
  by_cases hi : c i ∈ fairSpan c q₀
  · rw [deform, if_pos hi, abs_mul, abs_of_nonneg (sub_nonneg.mpr h₁)]
    exact mul_le_one₀ (by linarith) (abs_nonneg _) (q.property.1 i)
  · rw [deform_external_abs c q₀ t i hi, Real.exp_le_one_iff]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h₁)
        (Real.log_nonpos (abs_nonneg _) (q.property.1 i)))
      (mul_nonpos_of_nonneg_of_nonpos h₀ (Real.log_nonpos (abs_nonneg _) (p.property.1 i)))

private theorem deform_groupBias (p q : BiasFiber c s q₀) (t : unitInterval)
    (a : A ⧸ fairSpan c q₀) (ha : a ≠ 0) :
    let π := QuotientAddGroup.mk' (fairSpan c q₀)
    |groupBias (π ∘ c) (deform c q₀ p.val q.val t) a| = |groupBias (π ∘ c) q₀ a| := by
  classical
  intro π
  let F := @Finset.filter L (fun i => (π ∘ c) i = a)
    (fun _ => Classical.propDecidable _) Finset.univ
  have hnot (i : L) (hi : i ∈ F) : c i ∉ fairSpan c q₀ := by
    intro hm
    have he := (Finset.mem_filter.mp hi).2
    exact ha (he.symm.trans (quotient_zero.mpr hm))
  have hp := ((law_iff_quotient_coordinates c s q₀ p.val).mp p.property.2).2.2 a ha
  have hq := ((law_iff_quotient_coordinates c s q₀ q.val).mp q.property.2).2.2 a ha
  unfold groupBias at hp hq ⊢
  simp only [Finset.abs_prod] at hp hq ⊢
  change ∏ i ∈ F, |p.val i| = ∏ i ∈ F, |q₀ i| at hp
  change ∏ i ∈ F, |q.val i| = ∏ i ∈ F, |q₀ i| at hq
  change ∏ i ∈ F, |deform c q₀ p.val q.val t i| = ∏ i ∈ F, |q₀ i|
  rw [Finset.prod_congr rfl (fun i hi => deform_external_abs c q₀ t i (hnot i hi)), ← Real.exp_sum]
  have hlog (r : BiasFiber c s q₀) :
      Real.log (∏ i ∈ F, |r.val i|) = ∑ i ∈ F, Real.log |r.val i| :=
    Real.log_prod (fun i hi => abs_ne_zero.mpr (nonzero_external c s q₀ r i (hnot i hi)))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hlog q, ← hlog p, hp, hq]
  rw [← add_mul, sub_add_cancel, one_mul, Real.exp_log]
  apply Finset.prod_pos
  intro i hi
  apply abs_pos.mpr
  intro hz
  exact hnot i hi (fair_mem c q₀ i hz)

private theorem deform_in_sector (p : BiasFiber c s q₀) (q : signSector c s q₀ p)
    (t : unitInterval) :
    ∃ r : BiasFiber c s q₀, r.val = deform c q₀ p.val q.val.val t ∧
      r ∈ signSector c s q₀ p := by
  classical
  let d := deform c q₀ p.val q.val.val t
  have hlaw : law c s d = law c s q₀ := by
    apply (law_iff_quotient_coordinates c s q₀ d).mpr
    refine ⟨deform_fairSpan c s q₀ p q.val t, ?_, deform_groupBias c s q₀ p q.val t⟩
    exact (projected_sign_agreement c (deform_external_sign c q₀ t)).trans
      ((law_iff_quotient_coordinates c s q₀ p.val).mp p.property.2).2.1
  exact ⟨⟨d, deform_abs_le_one c s q₀ p q.val t, hlaw⟩, rfl, deform_external_sign c q₀ t⟩

private noncomputable def contract (p : BiasFiber c s q₀)
    (x : unitInterval × signSector c s q₀ p) : signSector c s q₀ p :=
  ⟨(deform_in_sector c s q₀ p x.2 x.1).choose,
    (deform_in_sector c s q₀ p x.2 x.1).choose_spec.2⟩

private theorem contract_val (p : BiasFiber c s q₀)
    (x : unitInterval × signSector c s q₀ p) :
    (contract c s q₀ p x).val.val = deform c q₀ p.val x.2.val.val x.1 :=
  (deform_in_sector c s q₀ p x.2 x.1).choose_spec.1

private theorem continuous_contract (p : BiasFiber c s q₀) :
    Continuous (contract c s q₀ p) := by
  classical
  refine continuous_induced_rng.mpr (continuous_induced_rng.mpr ?_)
  simp only [Function.comp_def, contract_val]
  apply continuous_pi
  intro i
  have hq : Continuous (fun x : unitInterval × signSector c s q₀ p => x.2.val.val i) :=
    (continuous_apply i).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have ht : Continuous (fun x : unitInterval × signSector c s q₀ p => x.1.val) :=
    continuous_subtype_val.comp continuous_fst
  by_cases hi : c i ∈ fairSpan c q₀
  · simp only [deform, ite_eq_left hi]
    exact (continuous_const.sub ht).mul hq
  · have hlog : Continuous
        (fun x : unitInterval × signSector c s q₀ p => Real.log |x.2.val.val i|) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have h : ContinuousAt Real.log |x.2.val.val i| :=
        Real.continuousAt_log (abs_ne_zero.mpr (nonzero_external c s q₀ x.2.val i hi))
      exact ContinuousAt.comp' (f := fun y : unitInterval × signSector c s q₀ p =>
        |y.2.val.val i|) (x := x) h hq.abs.continuousAt
    have he :=
      ((continuous_const.sub ht).mul hlog).add (ht.mul (continuous_const (y := Real.log |p.val i|)))
    rw [show (fun x : unitInterval × signSector c s q₀ p => deform c q₀ p.val x.2.val.val x.1 i)
          = fun x => (if p.val i < 0 then (-1 : ℝ) else 1) *
            Real.exp ((1 - x.1.val) * Real.log |x.2.val.val i| +
              x.1.val * Real.log |p.val i|) by funext x; simp only [deform, if_neg hi]]
    exact continuous_const.mul (Real.continuous_exp.comp he)

private theorem contract_zero (p : BiasFiber c s q₀) (q : signSector c s q₀ p) :
    contract c s q₀ p (0, q) = q := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  rw [contract_val]
  funext i
  by_cases hi : c i ∈ fairSpan c q₀
  · simp [deform, hi]
  · have ht : ((0 : unitInterval) : ℝ) = 0 := rfl
    have hne := nonzero_external c s q₀ q.val i hi
    have hsign := q.property i hi
    simp only [deform, if_neg hi, ht, sub_zero, one_mul, zero_mul, add_zero,
      Real.exp_log (abs_pos.mpr hne)]
    by_cases hp : p.val i < 0
    · rw [if_pos hp, neg_one_mul, abs_of_neg (hsign.mpr hp), neg_neg]
    · rw [if_neg hp, one_mul, abs_of_nonneg (le_of_not_gt (fun hn => hp (hsign.mp hn)))]

private theorem contract_one (p : BiasFiber c s q₀) (q : signSector c s q₀ p) :
    contract c s q₀ p (1, q) = contract c s q₀ p (1, ⟨p, fun _ _ => Iff.rfl⟩) := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  rw [contract_val, contract_val]
  funext i
  by_cases hi : c i ∈ fairSpan c q₀ <;> simp [deform, hi]

/-- A sign region of the fixed-law bias fiber contracts by scaling the fair-subgroup columns
and interpolating the logarithmic magnitudes on the other columns. -/
theorem signSector_contractible (p : BiasFiber c s q₀) : ContractibleSpace (signSector c s q₀ p) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨contract c s q₀ p (1, ⟨p, fun _ _ => Iff.rfl⟩), ?_⟩
  exact ⟨⟨⟨contract c s q₀ p, continuous_contract c s q₀ p⟩,
    contract_zero c s q₀ p, contract_one c s q₀ p⟩⟩

/-- Connected components of the fiber are exactly the regions with fixed external signs. -/
theorem connectedComponent_eq_signSector (p : BiasFiber c s q₀) :
    connectedComponent p = signSector c s q₀ p := by
  haveI := signSector_contractible c s q₀ p
  have hp : p ∈ signSector c s q₀ p := fun _ _ => Iff.rfl
  exact le_antisymm ((signSector_clopen c s q₀ p).connectedComponent_subset hp)
    ((isConnected_iff_connectedSpace.mpr inferInstance).subset_connectedComponent hp)

local instance quotientModule (H : AddSubgroup A) : Module (ZMod 2) (A ⧸ H) :=
  QuotientAddGroup.zmodModule (fun a => (ZModModule.char_nsmul_eq_zero 2 a) ▸ H.zero_mem)

private noncomputable def signLinearMap (H : AddSubgroup A) [Fintype (External H c)] :
    (External H c → ZMod 2) →ₗ[ZMod 2] A ⧸ H where
  toFun e := ∑ i : External H c, e i • QuotientAddGroup.mk' H (c i.val)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' k x := by simp [smul_smul, Finset.smul_sum]

private theorem signLinearMap_range (H : AddSubgroup A) [Fintype (External H c)] :
    LinearMap.range (signLinearMap c H) =
      Submodule.span (ZMod 2) (Set.range (fun i : External H c => QuotientAddGroup.mk' H (c i.val))) := by
  classical
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    change (∑ j : External H c, (if j = i then (1 : ZMod 2) else 0) •
      QuotientAddGroup.mk' H (c j.val)) = QuotientAddGroup.mk' H (c i.val)
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hji
      simp [hji]

private noncomputable def signs (H : AddSubgroup A) (q : L → ℝ) : External H c → ZMod 2 :=
  fun i => if q i.val < 0 then 1 else 0

private theorem sign_is_negative (H : AddSubgroup A) (q : L → ℝ) (i : External H c) :
    signs c H q i = 1 ↔ q i.val < 0 := by
  classical
  by_cases h : q i.val < 0 <;> simp [signs, h]

private theorem signLinearMap_signs (H : AddSubgroup A) [Fintype (External H c)] (q : L → ℝ) :
    signLinearMap c H (signs c H q) = negativeProjection H c q := by
  classical
  change (∑ i : External H c, signs c H q i • QuotientAddGroup.mk' H (c i.val)) =
    negativeProjection H c q
  have hs (i : External H c) : signs c H q i • QuotientAddGroup.mk' H (c i.val) =
      (if q i.val < 0 then QuotientAddGroup.mk' H (c i.val) else 0) := by
    by_cases hi : q i.val < 0 <;> simp [signs, hi]
  simp only [hs, negativeProjection, Finset.sum_filter]
  let term (i : L) := if q i < 0 then QuotientAddGroup.mk' H (c i) else 0
  change (∑ i : External H c, term i.val) = ∑ i, term i
  calc
    _ = ∑ i with c i ∉ H, term i :=
      (Finset.sum_subtype (Finset.univ.filter (fun i : L => c i ∉ H))
        (fun i => by simp) term).symm
    _ = _ := by
      apply Finset.sum_filter_of_ne
      intro i _ hn hi
      exact hn (by simp [term, quotient_zero.mpr hi])

private noncomputable def withSigns (H : AddSubgroup A)
    (q : L → ℝ) (e : External H c → ZMod 2) (i : L) : ℝ := by
  classical
  exact if hi : c i ∉ H then
    if e ⟨i, hi⟩ = 1 then -|q i| else |q i|
  else q i

private theorem withSigns_abs (H : AddSubgroup A) (q : L → ℝ)
    (e : External H c → ZMod 2) (i : L) : |withSigns c H q e i| = |q i| := by
  classical
  unfold withSigns
  split_ifs <;> simp

private theorem withSigns_signs (H : AddSubgroup A) (q : L → ℝ)
    (hq : ∀ i, c i ∉ H → q i ≠ 0) (e : External H c → ZMod 2) :
    signs c H (withSigns c H q e) = e := by
  classical
  funext i
  have hpos := abs_pos.mpr (hq i.val i.property)
  have hcases : e i = 0 ∨ e i = 1 := by
    have : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
    exact this _
  rcases hcases with h | h
  · have hn : ¬ ((withSigns c H q e) i.val < 0) := by
      simp [withSigns, i.property, h, not_lt.mpr hpos.le]
    simp [signs, hn, h]
  · have hn : (withSigns c H q e) i.val < 0 := by
      simpa [withSigns, i.property, h] using neg_lt_zero.mpr hpos
    simp [signs, hn, h]

private theorem signs_eq_iff_mem_sector (p q : BiasFiber c s q₀) :
    signs c (fairSpan c q₀) q.val = signs c (fairSpan c q₀) p.val ↔
      q ∈ signSector c s q₀ p := by
  constructor
  · intro he i hi
    let j : External (fairSpan c q₀) c := ⟨i, hi⟩
    rw [← sign_is_negative c _ q.val j, ← sign_is_negative c _ p.val j, he]
  · intro he
    funext i
    simp only [signs, propext (he i.val i.property)]

private theorem sign_assignment_realizable [Fintype (External (fairSpan c q₀) c)]
    (h₀ : ∀ i, |q₀ i| ≤ 1) (e : External (fairSpan c q₀) c → ZMod 2)
    (he : signLinearMap c (fairSpan c q₀) e =
      signLinearMap c (fairSpan c q₀) (signs c (fairSpan c q₀) q₀)) :
    ∃ p : BiasFiber c s q₀, signs c (fairSpan c q₀) p.val = e := by
  classical
  let H := fairSpan c q₀
  let q := withSigns c H q₀ e
  have hqmag (i : L) : |q i| = |q₀ i| := withSigns_abs c H q₀ e i
  have hqzero (i : L) : q i = 0 ↔ q₀ i = 0 := by
    rw [← abs_eq_zero, hqmag, abs_eq_zero]
  have hH : fairSpan c q = H := by simp only [fairSpan, hqzero, H]
  have hqsign : signs c H q = e := withSigns_signs c H q₀ (fun i hi hz => hi (fair_mem c q₀ i hz)) e
  refine ⟨⟨q, fun i => (hqmag i).trans_le (h₀ i), ?_⟩, hqsign⟩
  apply (law_iff_quotient_coordinates c s q₀ q).mpr
  refine ⟨hH, ?_, ?_⟩
  · rw [← signLinearMap_signs, hqsign, he, signLinearMap_signs]
  · intro a _
    simp only [groupBias, Finset.abs_prod, hqmag]

/-- The number of connected components of the fixed-column, fixed-offset fiber is two to
the nullity of the binary linear map given by the nonzero quotient columns. -/
theorem card_biasFiber_components (h₀ : ∀ i, |q₀ i| ≤ 1) :
    let H := fairSpan c q₀
    let J := External H c
    let r := Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun i : J => QuotientAddGroup.mk' H (c i.val))))
    Nat.card (Set.range (connectedComponent : BiasFiber c s q₀ → Set (BiasFiber c s q₀))) =
      2 ^ (Nat.card J - r) := by
  classical
  intro H J r
  let _ : Fintype J := Fintype.ofFinite _
  let f := signLinearMap c H
  let p₀ := signs c H q₀
  let S := {e : J → ZMod 2 // f e = f p₀}
  let D := Set.range (connectedComponent : BiasFiber c s q₀ → Set (BiasFiber c s q₀))
  have hs (p : BiasFiber c s q₀) : f (signs c H p.val) = f p₀ := by
    rw [signLinearMap_signs, signLinearMap_signs]
    exact ((law_iff_quotient_coordinates c s q₀ p.val).mp p.property.2).2.1
  let g (p : BiasFiber c s q₀) : S := ⟨signs c H p.val, hs p⟩
  have hg₁ : ∀ p q, connectedComponent p = connectedComponent q ↔ g p = g q := by
    intro p q
    rw [connectedComponent_eq_iff_mem, connectedComponent_eq_signSector, Subtype.ext_iff]
    exact (signs_eq_iff_mem_sector c s q₀ q p).symm
  let repr (x : D) : BiasFiber c s q₀ := x.property.choose
  have hrepr (x : D) : connectedComponent (repr x) = x.val := x.property.choose_spec
  let e : D ≃ S := Equiv.ofBijective (g ∘ repr) ⟨by
    intro x y h
    apply Subtype.ext
    rw [← hrepr x, ← hrepr y]
    exact (hg₁ _ _).mpr h, by
    intro x
    obtain ⟨p, hp⟩ := sign_assignment_realizable c s q₀ h₀ x.val x.property
    let y : D := ⟨connectedComponent p, p, rfl⟩
    refine ⟨y, ((hg₁ _ _).mp (hrepr y)).trans ?_⟩
    exact Subtype.ext hp⟩
  have hk : Nat.card S = Nat.card f.ker :=
    Nat.card_congr (f.toAddMonoidHom.fiberEquivKer p₀)
  have hdim := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, signLinearMap_range] at hdim
  have hker : Module.finrank (ZMod 2) f.ker = Nat.card J - r := by
    rw [Nat.card_eq_fintype_card]
    change r + Module.finrank (ZMod 2) f.ker = Fintype.card J at hdim
    omega
  let _ : Fintype f.ker := Fintype.ofFinite _
  calc
    Nat.card D = Nat.card S := Nat.card_congr e
    _ = Nat.card f.ker := hk
    _ = 2 ^ (Nat.card J - r) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hker]

end D5.S3.TotalVariation.ParityBiasComponents
