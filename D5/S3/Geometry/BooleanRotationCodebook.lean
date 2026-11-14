/- GID: D5/S3/Geometry/BooleanRotationCodebook
   generality: G
   mirror-B: D5/B/S3/Geometry/BooleanRotationCodebook
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle]
   utility: none
   digest: Boolean subset queries determine the exact signed simplex difference below the no-wrap threshold. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound

noncomputable section
open scoped BigOperators
namespace D5.S3.Geometry.BooleanRotationCodebook

/-- Circular distance from zero, with the literal period retained. -/
def circularError (L t : ℝ) : ℝ := ‖(t : AddCircle L)‖

private lemma small_nonnegative_close {L ε t : ℝ} (hε : 0 ≤ ε)
    (hL : 3 * ε < L) (ht : 0 ≤ t) (ht' : t ≤ 2 * ε)
    (h : circularError L t ≤ ε) : t ≤ ε := by
  rw [circularError, AddCircle.norm_eq] at h
  let k : ℤ := round (L⁻¹ * t)
  have hab : |t - (k : ℝ) * L| ≤ ε := h
  obtain ⟨hlo, hhi⟩ := abs_le.mp hab
  have hLp : 0 < L := by linarith
  have hk0 : 0 ≤ k := by
    by_contra hn
    have hk : k ≤ -1 := by omega
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right hkr hLp.le
    nlinarith
  have hk1 : k ≤ 0 := by
    by_contra hn
    have hk : 1 ≤ k := by omega
    have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right hkr hLp.le
    nlinarith
  have hk : k = 0 := le_antisymm hk1 hk0
  simpa [hk] using hhi

/-- A finite first crossing cannot jump across the forbidden circular gap. -/
theorem nonnegative_sum_no_wrap {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {L ε : ℝ} (hε : 0 ≤ ε) (hL : 3 * ε < L)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ ε)
    (hq : ∀ t ⊆ s, circularError L (∑ i ∈ t, a i) ≤ ε) :
    ∑ i ∈ s, a i ≤ ε := by
  induction s using Finset.induction_on with
  | empty => simpa using hε
  | @insert i s hi ih =>
    have hs : ∑ j ∈ s, a j ≤ ε := ih
      (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun t ht => hq t (ht.trans (Finset.subset_insert i s)))
    have hai := ha i (Finset.mem_insert_self i s)
    have hnon : 0 ≤ ∑ j ∈ insert i s, a j :=
      Finset.sum_nonneg (fun j hj => (ha j hj).1)
    apply small_nonnegative_close hε hL hnon
    · rw [Finset.sum_insert hi]
      linarith [hai.2]
    · exact hq _ (Finset.Subset.refl _)

/-- One subset is one Boolean query; all queries share the same residual vector. -/
def booleanError {ι : Type*} [Fintype ι] (L ε : ℝ) (a : ι → ℝ) : Prop :=
  ∀ s : Finset ι, circularError L (∑ i ∈ s, a i) ≤ ε

/-- The two signed masses of a residual vector. -/
def signedBody {ι : Type*} [Fintype ι] (ε : ℝ) (a : ι → ℝ) : Prop :=
  (∑ i, max (a i) 0) ≤ ε ∧ (∑ i, max (-a i) 0) ≤ ε

/-- Exact error fiber on principal representatives, for every finite dimension. -/
theorem exact_error_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L ε : ℝ} (hε : 0 ≤ ε) (hL : 3 * ε < L) (a : ι → ℝ)
    (ha : ∀ i, |a i| ≤ L / 2) : booleanError L ε a ↔ signedBody ε a := by
  have hLp : 0 < L := by linarith
  have hnorm (t : ℝ) (ht : |t| ≤ L / 2) : circularError L t = |t| := by
    exact (AddCircle.norm_coe_eq_abs_iff L hLp.ne').mpr (by simpa [abs_of_pos hLp] using ht)
  constructor
  · intro hq
    have hsmall (i : ι) : |a i| ≤ ε := by
      have hh := hq {i}
      simpa [Finset.sum_singleton, hnorm (a i) (ha i)] using hh
    have positive : ∑ i, max (a i) 0 ≤ ε := by
      let s := Finset.univ.filter (fun i => 0 ≤ a i)
      have heq : (∑ i ∈ s, a i) = ∑ i, max (a i) 0 := by
        simp only [s, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · exact (max_eq_left hi).symm
        · exact (max_eq_right (le_of_not_ge hi)).symm
      rw [← heq]
      exact nonnegative_sum_no_wrap s a hε hL
        (fun i hi => ⟨(Finset.mem_filter.mp hi).2, (le_abs_self _).trans (hsmall i)⟩)
        (fun t _ => hq t)
    have negative : ∑ i, max (-a i) 0 ≤ ε := by
      let s := Finset.univ.filter (fun i => 0 ≤ -a i)
      have heq : (∑ i ∈ s, -a i) = ∑ i, max (-a i) 0 := by
        simp only [s, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · exact (max_eq_left hi).symm
        · exact (max_eq_right (le_of_not_ge hi)).symm
      rw [← heq]
      apply nonnegative_sum_no_wrap s (fun i => -a i) hε hL
      · intro i hi
        exact ⟨(Finset.mem_filter.mp hi).2, (neg_le_abs _).trans (hsmall i)⟩
      · intro t _
        simpa [circularError, Finset.sum_neg_distrib] using hq t
    exact ⟨positive, negative⟩
  · rintro ⟨hp, hn⟩ s
    have upper : (∑ i ∈ s, a i) ≤ ε := calc
      _ ≤ ∑ i ∈ s, max (a i) 0 := Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i, max (a i) 0 := Finset.sum_le_univ_sum_of_nonneg (fun i => le_max_right _ _)
      _ ≤ ε := hp
    have lower : (∑ i ∈ s, -a i) ≤ ε := calc
      _ ≤ ∑ i ∈ s, max (-a i) 0 := Finset.sum_le_sum (fun i _ => le_max_left _ _)
      _ ≤ ∑ i, max (-a i) 0 := Finset.sum_le_univ_sum_of_nonneg (fun i => le_max_right _ _)
      _ ≤ ε := hn
    have hab : |∑ i ∈ s, a i| ≤ ε := by
      rw [Finset.sum_neg_distrib] at lower
      exact abs_le.mpr ⟨by linarith, upper⟩
    exact (show circularError L (∑ i ∈ s, a i) ≤ |∑ i ∈ s, a i| from
      QuotientAddGroup.norm_mk_le_norm).trans hab

open MeasureTheory Set
open scoped ENNReal
open D5.S3.Quantum.Measurement.ConditionalSubentropyGuessingBound (simplexCoords simplex_volume)

/-- The closed sign chamber with `p` positive and `q` negative coordinates. -/
def signedOrthant (p q : ℕ) (ε : ℝ) : Set ((Fin p ⊕ Fin q) → ℝ) :=
  {a | signedBody ε a ∧ (∀ i, 0 ≤ a (.inl i)) ∧ ∀ j, a (.inr j) ≤ 0}

private def splitSimplex (p q : ℕ) : Set ((Fin p ⊕ Fin q) → ℝ) :=
  {a | (∀ i, 0 ≤ a (.inl i)) ∧ (∑ i, a (.inl i)) ≤ 1 ∧
    (∀ j, 0 ≤ a (.inr j)) ∧ (∑ j, a (.inr j)) ≤ 1}

private lemma split_simplex_volume (p q : ℕ) :
    volume (splitSimplex p q) = (p.factorial : ℝ≥0∞)⁻¹ * (q.factorial : ℝ≥0∞)⁻¹ := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)
  have hm := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)
  have hs (n : ℕ) : MeasurableSet (simplexCoords (n + 1)) := by
    have hpos : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter (fun i : Fin n => isClosed_le continuous_const (continuous_apply i))
    exact (hpos.inter (isClosed_le
      (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)).measurableSet
  have heq : splitSimplex p q = e ⁻¹' (simplexCoords (p + 1) ×ˢ simplexCoords (q + 1)) := by
    ext a
    simp [splitSimplex, e, simplexCoords, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi, and_assoc]
  rw [heq, hm.measure_preimage (hs p |>.prod (hs q) |>.nullMeasurableSet), Measure.volume_eq_prod, Measure.prod_prod,
    simplex_volume, simplex_volume]

private def signedScale (p q : ℕ) (ε : ℝ) :
    (((Fin p ⊕ Fin q) → ℝ) →ₗ[ℝ] ((Fin p ⊕ Fin q) → ℝ)) :=
  Matrix.toLin' (Matrix.diagonal (Sum.elim (fun _ => ε) (fun _ => -ε)))

private lemma signed_scale_apply (p q : ℕ) (ε : ℝ) (a : (Fin p ⊕ Fin q) → ℝ) :
    signedScale p q ε a = fun i => Sum.elim (fun j => ε * a (.inl j))
      (fun j => -ε * a (.inr j)) i := by
  ext i
  cases i <;> simp [signedScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

private lemma signed_orthant_image (p q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    signedOrthant p q ε = signedScale p q ε '' splitSimplex p q := by
  have hε0 := hε.ne'
  ext a
  constructor
  · rintro ⟨⟨hp, hn⟩, ha, hb⟩
    let b : (Fin p ⊕ Fin q) → ℝ := Sum.elim (fun i => a (.inl i) / ε)
      (fun j => -a (.inr j) / ε)
    refine ⟨b, ?_, ?_⟩
    · have hp' : (∑ i, a (.inl i)) ≤ ε := by
        simpa [Fintype.sum_sum_type, max_eq_left, max_eq_right, ha, hb, neg_nonpos.mpr,
          neg_nonneg.mpr] using hp
      have hn' : (∑ j, -a (.inr j)) ≤ ε := by
        simpa [Fintype.sum_sum_type, max_eq_left, max_eq_right, ha, hb, neg_nonpos.mpr,
          neg_nonneg.mpr] using hn
      exact ⟨fun i => div_nonneg (ha i) hε.le,
        by simpa [b, ← Finset.sum_div] using (div_le_one hε).mpr hp',
        fun j => div_nonneg (neg_nonneg.mpr (hb j)) hε.le,
        by simpa [b, ← Finset.sum_div] using (div_le_one hε).mpr hn'⟩
    · rw [signed_scale_apply]
      ext i
      cases i <;> simp [b] <;> field_simp
  · rintro ⟨b, ⟨hb, hp, hc, hq⟩, rfl⟩
    rw [signed_scale_apply]
    have hp' := mul_le_mul_of_nonneg_left hp hε.le
    have hq' := mul_le_mul_of_nonneg_left hq hε.le
    have hpos (i) : 0 ≤ ε * b (.inl i) := mul_nonneg hε.le (hb i)
    have hneg (j) : -ε * b (.inr j) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) (hc j)
    have hinr (j) : 0 ≤ ε * b (.inr j) := mul_nonneg hε.le (hc j)
    refine ⟨⟨?_, ?_⟩, hpos, hneg⟩
    · simpa [Fintype.sum_sum_type, hpos, hinr, max_eq_left, max_eq_right,
        ← Finset.mul_sum] using hp'
    · simpa [Fintype.sum_sum_type, hpos, hinr, max_eq_left, max_eq_right,
        neg_nonpos.mpr, neg_nonneg.mpr, ← Finset.mul_sum] using hq'

/-- Exact Lebesgue volume in every closed sign chamber, including empty sides. -/
theorem signed_orthant_volume (p q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    volume (signedOrthant p q ε) =
      ENNReal.ofReal (ε ^ (p + q)) *
        ((p.factorial : ℝ≥0∞)⁻¹ * (q.factorial : ℝ≥0∞)⁻¹) := by
  rw [signed_orthant_image p q hε, Measure.addHaar_image_linearMap,
    split_simplex_volume]
  congr 1
  simp [signedScale, LinearMap.det_toLin', Matrix.det_diagonal,
    Fintype.prod_sum_type, abs_mul, abs_pow, abs_of_pos hε, pow_add]

private def coordinateChamber {ι : Type*} [Fintype ι] (s : Finset ι) (ε : ℝ) :
    Set (ι → ℝ) :=
  {a | signedBody ε a ∧ (∀ i ∈ s, 0 ≤ a i) ∧ ∀ i ∉ s, a i ≤ 0}

private lemma chamber_measurable {ι : Type*} [Fintype ι] (s : Finset ι) (ε : ℝ) :
    MeasurableSet (coordinateChamber s ε) := by
  have hp : Continuous (fun a : ι → ℝ => ∑ i, max (a i) 0) :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).max continuous_const)
  have hn : Continuous (fun a : ι → ℝ => ∑ i, max (-a i) 0) :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).neg.max continuous_const)
  have hs : MeasurableSet {a : ι → ℝ | ∀ i ∈ s, 0 ≤ a i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (measurable_pi_apply i)
  have ht : MeasurableSet {a : ι → ℝ | ∀ i ∉ s, a i ≤ 0} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_pi_apply i) measurable_const
  exact ((measurableSet_le hp.measurable measurable_const).inter
    (measurableSet_le hn.measurable measurable_const)).inter (hs.inter ht)


private lemma chamber_union {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    {a : ι → ℝ | signedBody ε a} = ⋃ s : Finset ι, coordinateChamber s ε := by
  classical
  ext a
  constructor
  · intro ha
    refine Set.mem_iUnion.mpr ⟨Finset.univ.filter (fun i => 0 ≤ a i), ha, ?_, ?_⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi
      exact le_of_not_ge (by simpa using hi)
  · intro ha
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ha
    exact hs.1

private lemma chamber_aedisjoint {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    Pairwise (fun s t : Finset ι => AEDisjoint volume
      (coordinateChamber s ε) (coordinateChamber t ε)) := by
  intro s t hst
  have hh := Finset.ext_iff.not.mp hst
  push Not at hh
  obtain ⟨i, hi⟩ := hh
  apply measure_mono_null (t := {a : ι → ℝ | a i = 0})
  · intro a ha
    have hs := ha.1
    have ht := ha.2
    by_cases his : i ∈ s
    · have hit : i ∉ t := by tauto
      exact le_antisymm (ht.2.2 i hit) (hs.2.1 i his)
    · have hit : i ∈ t := by tauto
      exact le_antisymm (hs.2.2 i his) (ht.2.1 i hit)
  · exact Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i 0

private lemma chamber_volume_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    volume {a : ι → ℝ | signedBody ε a} =
      ∑ s : Finset ι, volume (coordinateChamber s ε) := by
  rw [chamber_union, measure_iUnion₀ (chamber_aedisjoint ε)
    (fun s => (chamber_measurable s ε).nullMeasurableSet), tsum_fintype]

private def chamberEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) :
    (Fin s.card ⊕ Fin sᶜ.card) ≃ ι :=
  (Equiv.sumCongr s.equivFin.symm sᶜ.equivFin.symm).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun i => Finset.mem_compl))).trans
      (Equiv.sumCompl (fun i => i ∈ s)))

private lemma coordinate_chamber_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) {ε : ℝ} (hε : 0 < ε) :
    volume (coordinateChamber s ε) =
      ENNReal.ofReal (ε ^ Fintype.card ι) *
        ((s.card.factorial : ℝ≥0∞)⁻¹ * (sᶜ.card.factorial : ℝ≥0∞)⁻¹) := by
  let e := chamberEquiv s
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hm := volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  have hE (a : (Fin s.card ⊕ Fin sᶜ.card) → ℝ) (j) : E a (e j) = a j :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e a j
  have hinl (j) : e (.inl j) ∈ s := (s.equivFin.symm j).property
  have hinr (j) : e (.inr j) ∉ s :=
    Finset.mem_compl.mp (sᶜ.equivFin.symm j).property
  have hsum (a : (Fin s.card ⊕ Fin sᶜ.card) → ℝ) (f : ℝ → ℝ) :
      (∑ i, f (E a i)) = ∑ j, f (a j) := by
    exact (e.sum_comp (fun i => f (E a i))).symm.trans
      (Finset.sum_congr rfl (fun j _ => congrArg f (hE a j)))
  have heq : E ⁻¹' coordinateChamber s ε = signedOrthant s.card sᶜ.card ε := by
    ext a
    have hb : signedBody ε (E a) ↔ signedBody ε a := by
      unfold signedBody
      rw [hsum a (fun x => max x 0), hsum a (fun x => max (-x) 0)]
    simp only [Set.mem_preimage, coordinateChamber, signedOrthant, Set.mem_ofPred_eq, hb]
    constructor
    · rintro ⟨ha, hp, hn⟩
      refine ⟨ha, ?_, ?_⟩
      · intro i
        have h := hp (e (.inl i)) (hinl i)
        simpa only [hE] using h
      · intro i
        have h := hn (e (.inr i)) (hinr i)
        simpa only [hE] using h
    · rintro ⟨ha, hp, hn⟩
      refine ⟨ha, ?_, ?_⟩
      · intro i hi
        obtain ⟨j, rfl⟩ := e.surjective i
        cases j with
        | inl j => simpa only [hE] using hp j
        | inr j => exact (hinr j hi).elim
      · intro i hi
        obtain ⟨j, rfl⟩ := e.surjective i
        cases j with
        | inl j => exact (hi (hinl j)).elim
        | inr j => simpa only [hE] using hn j
  rw [← hm.measure_preimage (chamber_measurable s ε).nullMeasurableSet, heq,
    signed_orthant_volume _ _ hε, Finset.card_add_card_compl]

private lemma chamber_coefficient (n : ℕ) :
    (∑ s : Finset (Fin n), (s.card.factorial : ℝ)⁻¹ *
      ((n - s.card).factorial : ℝ)⁻¹) = ((2 * n).choose n : ℝ) / n.factorial := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) ^ 2 / n.factorial := by
      rw [← Finset.powerset_univ, Finset.sum_powerset]
      apply Finset.sum_congr (by simp)
      intro k hk
      have h := Finset.sum_powersetCard k (Finset.univ : Finset (Fin n))
        (fun j => (j.factorial : ℝ)⁻¹ * ((n - j).factorial : ℝ)⁻¹)
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      rw [h, Nat.cast_choose ℝ (by simpa using Finset.mem_range_succ_iff.mp hk)]
      have hf (m : ℕ) : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast Nat.sum_range_choose_sq n

/-- The exact volume of the whole signed error body in every finite dimension. -/
theorem signed_body_volume (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    volume {a : Fin n → ℝ | signedBody ε a} =
      ENNReal.ofReal (((2 * n).choose n : ℝ) * ε ^ n / n.factorial) := by
  classical
  rw [chamber_volume_sum]
  have hc (s : Finset (Fin n)) : volume (coordinateChamber s ε) =
      ENNReal.ofReal (ε ^ n * ((s.card.factorial : ℝ)⁻¹ *
        ((n - s.card).factorial : ℝ)⁻¹)) := by
    rw [coordinate_chamber_volume s hε]
    simp only [Fintype.card_fin, Finset.card_compl, Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
    simp
  simp_rw [hc]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intros; positivity), ← Finset.mul_sum,
    chamber_coefficient]
  congr 1
  ring

/-- A codeword is selected once, before all Boolean queries. -/
def Adequate (n : ℕ) (L ε : ℝ) (C : Finset (Fin n → ℝ)) : Prop :=
  ∀ θ : Fin n → ℝ, ∃ φ ∈ C, booleanError L ε (θ - φ)

private def torusFiber (n : ℕ) (L ε : ℝ) : Set (Fin n → AddCircle L) :=
  {a | ∀ s : Finset (Fin n), ‖∑ i ∈ s, a i‖ ≤ ε}

private lemma torus_fiber_measurable (n : ℕ) (L ε : ℝ) [Fact (0 < L)] :
    MeasurableSet (torusFiber n L ε) := by
  simp only [torusFiber, Set.ofPred_forall]
  exact MeasurableSet.iInter fun s => measurableSet_le
    (continuous_norm.comp (continuous_finsetSum s (fun i _ => continuous_apply i))).measurable
    measurable_const

private lemma torus_fiber_volume_le (n : ℕ) {L ε : ℝ} [Fact (0 < L)]
    (hε : 0 < ε) (hL : 3 * ε < L) :
    volume (torusFiber n L ε) ≤
      ENNReal.ofReal (((2 * n).choose n : ℝ) * ε ^ n / n.factorial) := by
  let B : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Ioc (-(L / 2)) (-(L / 2) + L))
  have hm := measurePreserving_pi
    (fun _ : Fin n => volume.restrict (Ioc (-(L / 2)) (-(L / 2) + L)))
    (fun _ : Fin n => (volume : Measure (AddCircle L)))
    (fun _ => AddCircle.measurePreserving_mk L (-(L / 2)))
  have hm' : MeasurePreserving (fun a : Fin n → ℝ => fun i => (a i : AddCircle L))
      (volume.restrict B) volume := by
    simpa only [B, volume_pi, Measure.restrict_pi_pi] using hm
  rw [← hm'.measure_preimage (torus_fiber_measurable n L ε).nullMeasurableSet,
    Measure.restrict_apply (by exact hm'.measurable (torus_fiber_measurable n L ε))]
  rw [← signed_body_volume n hε]
  apply measure_mono
  rintro a ⟨ha, hb⟩
  apply (exact_error_fiber hε.le hL a ?_).mp
  · intro s
    have hh := ha s
    simpa [circularError, ← QuotientAddGroup.mk_sum] using hh
  · intro i
    have hi := hb i (Set.mem_univ i)
    exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- The exact finite-codebook capacity lower bound, uniformly in the dimension. -/
theorem finite_codebook_lower_bound (n : ℕ) {L ε : ℝ}
    (hε : 0 < ε) (hL : 3 * ε < L) (C : Finset (Fin n → ℝ))
    (hC : Adequate n L ε C) :
    (n.factorial : ℝ) * L ^ n ≤ (C.card : ℝ) * (2 * n).choose n * ε ^ n := by
  classical
  have hLp : 0 < L := by linarith
  letI : Fact (0 < L) := ⟨hLp⟩
  let F := torusFiber n L ε
  let c (φ : Fin n → ℝ) : Fin n → AddCircle L := fun i => (φ i : AddCircle L)
  have hcover : (Set.univ : Set (Fin n → AddCircle L)) ⊆
      ⋃ φ ∈ C, (fun a => a - c φ) ⁻¹' F := by
    intro a _
    have hr : ∀ i, ∃ t : ℝ, (t : AddCircle L) = a i := fun i => QuotientAddGroup.mk_surjective (a i)
    choose θ hθ using hr
    obtain ⟨φ, hφ, hq⟩ := hC θ
    refine Set.mem_iUnion.mpr ⟨φ, Set.mem_iUnion.mpr ⟨hφ, ?_⟩⟩
    intro s
    have hh := hq s
    simpa [circularError, ← QuotientAddGroup.mk_sum, ← hθ, c] using hh
  have hv : ENNReal.ofReal (L ^ n) ≤
      (C.card : ℝ≥0∞) * ENNReal.ofReal (((2 * n).choose n : ℝ) * ε ^ n / n.factorial) := by
    calc
      _ = volume (Set.univ : Set (Fin n → AddCircle L)) := by
        simp [volume_pi, Measure.pi_univ, ← ENNReal.ofReal_pow hLp.le]
      _ ≤ volume (⋃ φ ∈ C, (fun a => a - c φ) ⁻¹' F) := measure_mono hcover
      _ ≤ ∑ φ ∈ C, volume ((fun a => a - c φ) ⁻¹' F) := measure_biUnion_finset_le C _
      _ = ∑ _φ ∈ C, volume F := by
        apply Finset.sum_congr rfl
        intro φ _
        exact (measurePreserving_sub_right volume (c φ)).measure_preimage
          (torus_fiber_measurable n L ε).nullMeasurableSet
      _ ≤ ∑ _φ ∈ C, ENNReal.ofReal (((2 * n).choose n : ℝ) * ε ^ n / n.factorial) :=
        Finset.sum_le_sum fun _ _ => torus_fiber_volume_le n hε hL
      _ = _ := by simp
  have hv' : L ^ n ≤ (C.card : ℝ) * (((2 * n).choose n : ℝ) * ε ^ n / n.factorial) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa [ENNReal.ofReal_mul, ENNReal.ofReal_natCast] using hv
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hh := (le_div_iff₀ hf).mp (show L ^ n ≤
    ((C.card : ℝ) * (2 * n).choose n * ε ^ n) / n.factorial by
      simpa only [mul_div_assoc, mul_assoc] using hv')
  nlinarith [hh]

/-- The literal real planar rotation matrix. -/
def rotation (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α]

/-- The prescribed decoder is fixed by the stored parameter vector. -/
def row0Decoder {n : ℕ} (φ : Fin n → ℝ) (s : Finset (Fin n)) :=
  rotation (∑ i ∈ s, φ i)

private lemma rotation_eq_iff (α β : ℝ) :
    rotation α = rotation β ↔ (α : Real.Angle) = (β : Real.Angle) := by
  constructor
  · intro h
    apply Real.Angle.cos_sin_inj
    · exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
    · exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 0) h
  · intro h
    have hc : Real.cos α = Real.cos β := congrArg Real.Angle.cos h
    have hs : Real.sin α = Real.sin β := congrArg Real.Angle.sin h
    simp [rotation, hc, hs]

private lemma literal_error_iff (α β ε : ℝ) :
    circularError (2 * Real.pi) (α - β) ≤ ε ↔
      ∃ δ : ℝ, |δ| ≤ ε ∧ rotation α = rotation (β + δ) := by
  constructor
  · intro h
    let k : ℤ := round ((2 * Real.pi)⁻¹ * (α - β))
    let δ := α - β - (k : ℝ) * (2 * Real.pi)
    refine ⟨δ, ?_, (rotation_eq_iff _ _).mpr ?_⟩
    · simpa only [circularError, AddCircle.norm_eq] using h
    · have he : β + δ = α - (k : ℝ) * (2 * Real.pi) := by dsimp [δ]; ring
      rw [he, Real.Angle.coe_sub, ← zsmul_eq_mul, Real.Angle.coe_zsmul,
        Real.Angle.coe_two_pi, smul_zero, sub_zero]
  · rintro ⟨δ, hδ, he⟩
    have hangle := (rotation_eq_iff _ _).mp he
    have hd : ((α - β : ℝ) : Real.Angle) = (δ : Real.Angle) := by
      rw [Real.Angle.coe_sub, hangle, Real.Angle.coe_add, add_sub_cancel_left]
    change ‖((α - β : ℝ) : Real.Angle)‖ ≤ ε
    rw [hd]
    exact (show ‖(δ : Real.Angle)‖ ≤ |δ| from QuotientAddGroup.norm_mk_le_norm).trans hδ

/-- Matrix decoder accuracy uses literal equality with a bounded angular residual. -/
def FixedDecoderAdequate (n : ℕ) (ε : ℝ) (C : Finset (Fin n → ℝ)) : Prop :=
  Function.Periodic rotation (2 * Real.pi) ∧
    ∀ θ : Fin n → ℝ, ∃ φ ∈ C, ∀ s : Finset (Fin n),
      ∃ δ : ℝ, |δ| ≤ ε ∧ row0Decoder θ s = rotation ((∑ i ∈ s, φ i) + δ)

private lemma grid_coordinate {L : ℝ} (hL : 0 < L) (m : ℕ) (hm : 0 < m)
    (t : ℝ) : ∃ j : Fin m,
      circularError L (t - (j.val : ℝ) / m * L) ≤ L / (2 * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  letI : Fact (0 < L) := ⟨hL⟩
  let k : ℤ := round (t * m / L)
  let u : AddCircle L := ((k : ℝ) / m * L : ℝ)
  have hu : m • u = 0 := by
    change m • (((k : ℝ) / m * L : ℝ) : AddCircle L) = 0
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    have he : (m : ℝ) * ((k : ℝ) / m * L) = (k : ℝ) * L := by field_simp
    rw [he, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  obtain ⟨j, hj, he⟩ := (AddCircle.nsmul_eq_zero_iff (p := L) hm).mp hu
  refine ⟨⟨j, hj⟩, ?_⟩
  have he' : (((j : ℝ) / m * L : ℝ) : AddCircle L) = u := he
  unfold circularError
  rw [AddCircle.coe_sub, he', ← AddCircle.coe_sub]
  apply (show ‖((t - (k : ℝ) / m * L : ℝ) : AddCircle L)‖ ≤
    |t - (k : ℝ) / m * L| from QuotientAddGroup.norm_mk_le_norm).trans
  have ha := abs_sub_round (t * m / L)
  have hid : t - (k : ℝ) / m * L = (t * m / L - (k : ℝ)) * (L / m) := by
    dsimp [k]; field_simp <;> ring
  rw [hid, abs_mul, abs_of_pos (div_pos hL hmR)]
  calc
    _ ≤ (1 / 2 : ℝ) * (L / m) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by ring

/-- A single finite grid serves all parameter vectors and all subset queries. -/
theorem finite_codebook_upper_bound (n : ℕ) (hn : 0 < n) {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    ∃ C : Finset (Fin n → ℝ), Adequate n L ε C ∧
      C.card ≤ (⌈L * n / (2 * ε)⌉₊) ^ n ∧
      (L = 2 * Real.pi → FixedDecoderAdequate n ε C) := by
  classical
  let m : ℕ := ⌈L * n / (2 * ε)⌉₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let f : (Fin n → Fin m) → (Fin n → ℝ) := fun a i => (a i).val / (m : ℝ) * L
  let C := Finset.univ.image f
  have hadequate : Adequate n L ε C := by
    intro θ
    choose j hj using fun i => grid_coordinate hL m hm (θ i)
    refine ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    intro s
    have hbudget : (n : ℝ) * (L / (2 * m)) ≤ ε := by
      have hc : L * n / (2 * ε) ≤ (m : ℝ) := Nat.le_ceil _
      have hc' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mp hc
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mpr
      nlinarith
    calc
      circularError L (∑ i ∈ s, (θ - f j) i) =
          ‖∑ i ∈ s, (((θ i - f j i : ℝ)) : AddCircle L)‖ := by
            simp [circularError, ← QuotientAddGroup.mk_sum]
      _ ≤ ∑ i ∈ s, ‖(((θ i - f j i : ℝ)) : AddCircle L)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, L / (2 * m) := Finset.sum_le_sum (fun i _ => hj i)
      _ = (s.card : ℝ) * (L / (2 * m)) := by simp
      _ ≤ (n : ℝ) * (L / (2 * m)) := by
        gcongr
        exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_univ s)
      _ ≤ ε := hbudget
  refine ⟨C, hadequate, ?_, ?_⟩
  · calc
      C.card ≤ (Finset.univ : Finset (Fin n → Fin m)).card := Finset.card_image_le
      _ = m ^ n := by simp
  · intro hperiod
    refine ⟨?_, ?_⟩
    · intro α
      apply (rotation_eq_iff _ _).mpr
      simp [Real.Angle.coe_add, Real.Angle.coe_two_pi]
    · intro θ
      obtain ⟨φ, hφ, hq⟩ := hadequate θ
      refine ⟨φ, hφ, fun s => ?_⟩
      apply (literal_error_iff _ _ _).mp
      have hh := hq s
      simpa [hperiod, row0Decoder, Finset.sum_sub_distrib] using hh

end D5.S3.Geometry.BooleanRotationCodebook
