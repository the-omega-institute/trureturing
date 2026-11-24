/- GID: D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FIBTwoSourceObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two individually sharp event differences share a single capacity. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Two individually attainable differences draw on the same region of a common
containing event. On a five-vertex bipartite graph, these and the endpoint capacities are sufficient. -/

set_option autoImplicit false

open Set MeasureTheory

namespace D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction

/-- Two disjoint parts of `K\setminus S` are reserved by the two differences. -/
theorem shared_capacity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S H K T W : Set Ω} (finiteK : μ K ≠ ⊤)
    (sMeas : MeasurableSet S) (hMeas : MeasurableSet H) (tMeas : MeasurableSet T)
    (sH : S ⊆ H) (sK : S ⊆ K) (tK : T ⊆ K) (wH : W ⊆ H) (wK : W ⊆ K) :
    μ.real (W \ S) + μ.real (T \ H) ≤ μ.real K - μ.real S := by
  have disjointDifferences : Disjoint (W \ S) (T \ H) :=
    disjoint_left.mpr fun _ hw ht => ht.2 (wH hw.1)
  have contained : (W \ S) ∪ (T \ H) ⊆ K \ S :=
    union_subset (sdiff_subset_sdiff_left wK) (sdiff_subset_sdiff tK sH)
  have finite {B : Set Ω} (hB : B ⊆ K) : μ B ≠ ⊤ :=
    measure_ne_top_of_subset hB finiteK
  calc
    _ = μ.real ((W \ S) ∪ (T \ H)) :=
      (measureReal_union disjointDifferences (tMeas.diff hMeas)
        (finite (sdiff_subset.trans wK)) (finite (sdiff_subset.trans tK))).symm
    _ ≤ μ.real (K \ S) := measureReal_mono contained (finite sdiff_subset)
    _ = _ := measureReal_sdiff sK sMeas finiteK

/-- In vertex order `S,H,K,T,W`, the two larger events occupy `H,K`. -/
def Nested {Ω : Type*} (A : Fin 5 → Set Ω) : Prop :=
  A 0 ⊆ A 1 ∧ A 0 ⊆ A 2 ∧ A 3 ⊆ A 2 ∧ A 4 ⊆ A 1 ∧ A 4 ⊆ A 2

private theorem two_intervals_mass {a b c d : ℝ}
    (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d) :
    volume.real (Ico a b ∪ Ico c d) = (b - a) + (d - c) := by
  have h : Disjoint (Ico a b) (Ico c d) :=
    disjoint_left.mpr fun _ hx hy => (not_lt_of_ge (bc.trans hy.1)) hx.2
  rw [measureReal_union h measurableSet_Ico (by simp) (by simp),
    Real.volume_real_Ico_of_le ab, Real.volume_real_Ico_of_le cd]

private theorem finite_unit {U : Set ℝ} (hU : U ⊆ Ico 0 1) : volume U ≠ ⊤ :=
  measure_ne_top_of_subset hU (by simp)

/-- On the five-vertex inclusion graph, the shared region and the endpoint masses
give the exact region of the two oriented differences. -/
theorem five_vertex_range {q c a b : ℝ} :
    (∃ A : Fin 5 → Set ℝ, Nested A ∧
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1) ∧
      volume.real (A 0) = q ∧ volume.real (A 1) = q + c ∧ volume.real (A 2) = q + c ∧
      volume.real (A 3) = q ∧ volume.real (A 4) = q ∧
      volume.real (A 4 \ A 0) = a ∧ volume.real (A 3 \ A 1) = b) ↔
      0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ c ∧ a ≤ q ∧ b ≤ q ∧ b ≤ 1 - (q + c) := by
  constructor
  · rintro ⟨A, nested, law, sMass, hMass, kMass, tMass, wMass, wa, tb⟩
    obtain ⟨sH, sK, tK, wH, wK⟩ := nested
    have cap := shared_capacity volume (finite_unit (law 2).2)
      (law 0).1 (law 1).1 (law 3).1 sH sK tK wH wK
    rw [wa, tb, kMass, sMass, add_sub_cancel_left] at cap
    refine ⟨wa ▸ measureReal_nonneg, tb ▸ measureReal_nonneg, cap, ?_, ?_, ?_⟩
    · rw [← wa, ← wMass]
      exact measureReal_mono sdiff_subset (finite_unit (law 4).2)
    · rw [← tb, ← tMass]
      exact measureReal_mono sdiff_subset (finite_unit (law 3).2)
    · rw [← tb]
      apply (measureReal_mono (sdiff_subset_sdiff_left (law 3).2)
        (finite_unit sdiff_subset)).trans_eq
      rw [measureReal_sdiff (law 1).2 (law 1).1 (by simp), hMass]
      simp [Real.volume_real_Ico]
  · rintro ⟨ha, hb, hab, haq, hbq, hbunit⟩
    have hq : 0 ≤ q := ha.trans haq
    have hc : 0 ≤ c := le_trans (add_nonneg ha hb) hab
    have unit : q + c ≤ 1 := by linarith
    let S := Ico 0 q
    let H := Ico 0 (q + c - b) ∪ Ico (q + c) (q + c + b)
    let K := Ico 0 (q + c)
    let T := Ico 0 (q - b) ∪ Ico (q + c - b) (q + c)
    let W := Ico 0 (q - a) ∪ Ico q (q + a)
    let A : Fin 5 → Set ℝ := ![S, H, K, T, W]
    have sLaw : MeasurableSet S ∧ S ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico, Ico_subset_Ico_right (by linarith)⟩
    have hLaw : MeasurableSet H ∧ H ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico.union measurableSet_Ico,
        union_subset (Ico_subset_Ico_right (by linarith))
          (Ico_subset_Ico (by linarith) (by linarith))⟩
    have kLaw : MeasurableSet K ∧ K ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico, Ico_subset_Ico_right unit⟩
    have tLaw : MeasurableSet T ∧ T ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico.union measurableSet_Ico,
        union_subset (Ico_subset_Ico_right (by linarith))
          (Ico_subset_Ico (by linarith) unit)⟩
    have wLaw : MeasurableSet W ∧ W ⊆ Ico 0 1 :=
      ⟨measurableSet_Ico.union measurableSet_Ico,
        union_subset (Ico_subset_Ico_right (by linarith))
          (Ico_subset_Ico hq (by linarith))⟩
    have sH : S ⊆ H :=
      (Ico_subset_Ico_right (by linarith : q ≤ q + c - b)).trans subset_union_left
    have sK : S ⊆ K := Ico_subset_Ico_right (by linarith)
    have tK : T ⊆ K :=
      union_subset (Ico_subset_Ico_right (by linarith)) (Ico_subset_Ico_left (by linarith))
    have wH : W ⊆ H :=
      (union_subset (Ico_subset_Ico_right (by linarith : q - a ≤ q + c - b))
        (Ico_subset_Ico hq (by linarith : q + a ≤ q + c - b))).trans subset_union_left
    have wK : W ⊆ K :=
      union_subset (Ico_subset_Ico_right (by linarith)) (Ico_subset_Ico hq (by linarith))
    have sMass : volume.real S = q := by
      dsimp only [S]
      rw [Real.volume_real_Ico_of_le hq, sub_zero]
    have hMass : volume.real H = q + c := by
      dsimp only [H]
      rw [two_intervals_mass (by linarith) (by linarith) (by linarith)]
      linarith
    have kMass : volume.real K = q + c := by
      dsimp only [K]
      rw [Real.volume_real_Ico_of_le (by linarith), sub_zero]
    have tMass : volume.real T = q := by
      dsimp only [T]
      rw [two_intervals_mass (by linarith) (by linarith) (by linarith)]
      linarith
    have wMass : volume.real W = q := by
      dsimp only [W]
      rw [two_intervals_mass (by linarith) (by linarith) (by linarith)]
      linarith
    have ws : W \ S = Ico q (q + a) := by
      have ha' : q - a ≤ q := by linarith
      ext x
      simp only [W, S, mem_union, mem_sdiff, mem_Ico]
      grind
    have th : T \ H = Ico (q + c - b) (q + c) := by
      have horder : q - b ≤ q + c - b := by linarith
      have hstart : 0 ≤ q + c - b := by linarith
      ext x
      simp only [T, H, mem_union, mem_sdiff, mem_Ico]
      grind
    have wDiff : volume.real (W \ S) = a := by
      rw [ws, Real.volume_real_Ico_of_le (by linarith)]
      linarith
    have tDiff : volume.real (T \ H) = b := by
      rw [th, Real.volume_real_Ico_of_le (by linarith)]
      linarith
    refine ⟨A, ⟨sH, sK, tK, wH, wK⟩, ?_, sMass, hMass, kMass, tMass, wMass, wDiff, tDiff⟩
    intro v
    fin_cases v
    · exact sLaw
    · exact hLaw
    · exact kLaw
    · exact tLaw
    · exact wLaw

end D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
