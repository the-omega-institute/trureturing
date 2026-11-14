/- GID: D5/S3/Geometry/BooleanRotationCodebook
   generality: G
   mirror-B: D5/B/S3/Geometry/BooleanRotationCodebook
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle]
   utility: none
   digest: Boolean subset queries determine the exact signed simplex difference below the no-wrap threshold. -/
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
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
  exact ((hp.isClosed_preimage _ isClosed_Iic).inter
    ((hn.isClosed_preimage _ isClosed_Iic).inter
      ((isClosed_biInter fun i _ => isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_biInter fun i _ => isClosed_le (continuous_apply i) continuous_const)))).measurableSet

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
  obtain ⟨i, hi⟩ := Finset.ext_iff.not.mp hst
  apply measure_mono_null (t := {a : ι → ℝ | a i = 0})
  · intro a ha
    have hs := ha.1
    have ht := ha.2
    by_cases his : i ∈ s
    · have hit : i ∉ t := fun h => hi (iff_of_true his h)
      exact le_antisymm (ht.2.2 i hit) (hs.2.1 i his)
    · have hit : i ∈ t := by tauto
      exact le_antisymm (hs.2.2 i his) (ht.2.1 i hit)
  · exact pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i 0

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
  have hsum (a : (Fin s.card ⊕ Fin sᶜ.card) → ℝ) (f : ℝ → ℝ) :
      (∑ i, f (E a i)) = ∑ j, f (a j) := by
    exact (e.sum_comp (fun i => f (E a i))).symm.trans
      (Finset.sum_congr rfl (fun j _ => by simp [E]))
  have heq : E ⁻¹' coordinateChamber s ε = signedOrthant s.card sᶜ.card ε := by
    ext a
    have hb : signedBody ε (E a) ↔ signedBody ε a := by
      simp only [signedBody, hsum]
    simp only [Set.mem_preimage, coordinateChamber, signedOrthant, Set.mem_setOf_eq, hb]
    constructor
    · rintro ⟨ha, hp, hn⟩
      refine ⟨ha, ?_, ?_⟩
      · intro i
        have h := hp (e (.inl i)) (by simp [e, chamberEquiv])
        simpa [E] using h
      · intro i
        have h := hn (e (.inr i)) (by simp [e, chamberEquiv])
        simpa [E] using h
    · rintro ⟨ha, hp, hn⟩
      refine ⟨ha, ?_, ?_⟩
      · intro i hi
        obtain ⟨j, rfl⟩ := s.equivFin.symm.surjective ⟨i, hi⟩
        simpa [E, e, chamberEquiv] using hp j
      · intro i hi
        obtain ⟨j, hj⟩ := sᶜ.equivFin.symm.surjective ⟨i, by simpa using hi⟩
        have h := hn j
        simpa [E, e, chamberEquiv, hj] using h
  rw [← hm.measure_preimage (chamber_measurable s ε).nullMeasurableSet, heq,
    signed_orthant_volume _ _ hε, Finset.card_add_card_compl]

end D5.S3.Geometry.BooleanRotationCodebook
