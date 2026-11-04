/- GID: D5/S3/Geometry/Rauzy/TribonacciInterior
   generality: I
   mirror-B: D5/B/S3/Geometry/Rauzy/TribonacciInterior
   mirror-E: none(waiver:unbounded-analytic-existence)
   anchors: []
   utility: none
   digest: The exact non-Perron Tribonacci Rauzy closure has nonempty interior. -/

import D5.S3.Geometry.Rauzy.Interior
import D5.S0.Tower.Tribonacci.Separation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
The exact goal and its synchronized limiting-cluster/open-hole witness are
preregistered in `D5.S3.Geometry.Rauzy.Interior`. The only intended endpoint
here is `rauzyFractal_interior_nonempty`, with precisely characteristic-root
membership and inequality to the real Perron root as hypotheses. The set is
the existing closure of finite exponent-zero no-111 sums. The helpers below
are consumed infrastructure for that endpoint and have no standalone
admission claim.
-/

namespace D5.S3.Geometry.Rauzy.TribonacciInterior

open D5.S0.Tower.Tribonacci
open Names Values ModelSet RauzyFractal
open Set Metric Filter MeasureTheory
open scoped Topology Function

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "β" => tribonacciConstant

private theorem name_card_lower (Q : ℕ) :
    β ^ Q ≤ (Fintype.card (TribonacciName Q) : ℝ) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    match Q with
    | 0 =>
      have hcard : Fintype.card (TribonacciName 0) = 1 := by decide
      simp [hcard]
    | 1 =>
      have hcard : Fintype.card (TribonacciName 1) = 2 := by decide
      simpa [hcard] using tribonacciConstant_lt_two.le
    | 2 =>
      have hcard : Fintype.card (TribonacciName 2) = 4 := by decide
      rw [hcard]
      calc
        β ^ 2 ≤ (2 : ℝ) ^ 2 :=
          pow_le_pow_left₀ tribonacciConstant_pos.le tribonacciConstant_lt_two.le 2
        _ = _ := by norm_num
    | n + 3 =>
      rw [tribonacci_name_card_add_three]
      push_cast
      have hpow : β ^ (n + 3) = β ^ (n + 2) + β ^ (n + 1) + β ^ n := by
        calc
          β ^ (n + 3) = β ^ n * β ^ 3 := pow_add _ _ _
          _ = β ^ (n + 2) + β ^ (n + 1) + β ^ n := by
            rw [tribonacciConstant_cubic, pow_add, pow_add]
            ring
      rw [hpow]
      exact add_le_add (add_le_add (ih (n + 2) (by omega)) (ih (n + 1) (by omega)))
        (ih n (by omega))

private def paddedDigit {L : ℕ} (u : TribonacciName L) (i : ℕ) : Bool :=
  if h : i < L then u.1 ⟨i, h⟩ else false

private theorem padded_no_three {L : ℕ} (u : TribonacciName L) (i : ℕ) :
    ¬ (paddedDigit u i ∧ paddedDigit u (i + 1) ∧ paddedDigit u (i + 2)) := by
  by_cases hi : i + 2 < L
  · simpa only [paddedDigit, dif_pos (show i < L by omega),
      dif_pos (show i + 1 < L by omega), dif_pos hi] using
      Representation.admissible_no_three_at L i u.1 u.2 hi
  · simp only [paddedDigit, dif_neg hi, Bool.false_eq_true, and_false, not_false_eq_true]

private theorem admissible_of_no_three (f : ℕ → Bool)
    (hf : ∀ i, ¬ (f i ∧ f (i + 1) ∧ f (i + 2))) (Q start : ℕ) :
    TribonacciAdmissible Q (fun i => f (start + i.1)) := by
  induction Q using Nat.strong_induction_on generalizing start with
  | h Q ih =>
    match Q with
    | 0 => trivial
    | 1 => trivial
    | 2 => trivial
    | n + 3 =>
      rw [admissible_add_three_iff]
      constructor
      · simpa [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] using hf start
      · convert ih (n + 2) (by omega) (start + 1) using 1
        funext i
        congr 1
        simp [Fin.tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private def sliceName {L : ℕ} (u : TribonacciName L) (start Q : ℕ) : TribonacciName Q :=
  ⟨fun i => paddedDigit u (start + i.1),
    admissible_of_no_three (paddedDigit u) (padded_no_three u) Q start⟩

private theorem coordinate_slice {L : ℕ} (u : TribonacciName L) (z : ℂ) (start Q : ℕ) :
    conjugateCoordinate z (sliceName u start Q) =
      ∑ i ∈ Finset.range Q, if paddedDigit u (start + i) then z ^ i else 0 := by
  exact Fin.sum_univ_eq_sum_range
    (fun i => if paddedDigit u (start + i) then z ^ i else 0) Q

private theorem coordinate_split {L : ℕ} (u : TribonacciName L) (z : ℂ) (Q : ℕ) :
    conjugateCoordinate z u =
      conjugateCoordinate z (sliceName u 0 Q) +
        z ^ Q * conjugateCoordinate z (sliceName u Q L) := by
  let f : ℕ → ℂ := fun i => if paddedDigit u i then z ^ i else 0
  have hu : conjugateCoordinate z u = ∑ i ∈ Finset.range L, f i := by
    rw [conjugateCoordinate]
    calc
      _ = ∑ i : Fin L, f i.1 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [f, paddedDigit, dif_pos i.2]
      _ = _ := Fin.sum_univ_eq_sum_range f L
  have hpad : (∑ i ∈ Finset.range L, f i) = ∑ i ∈ Finset.range (Q + L), f i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hin
    have hnot : ¬ i < L := by simpa only [Finset.mem_range] using hin
    simp [f, paddedDigit, hnot]
  rw [hu, hpad, Finset.sum_range_add, coordinate_slice, coordinate_slice]
  congr 1
  · simp only [Nat.zero_add, f]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    split_ifs <;> simp [pow_add]

private def prefixCenters (z : ℂ) (Q : ℕ) : Set ℂ :=
  Set.range (conjugateCoordinate z : TribonacciName Q → ℂ)

private theorem upper_cylinder_cover {z : ℂ}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) (Q : ℕ) :
    ∀ w ∈ rauzyFractal z, ∃ a ∈ prefixCenters z Q,
      ∃ k ∈ rauzyFractal z, w = a + z ^ Q * k := by
  let C : Set ℂ := ⋃ u : TribonacciName Q,
    (fun k => conjugateCoordinate z u + z ^ Q * k) '' rauzyFractal z
  have hC : IsClosed C := (isCompact_iUnion (fun u =>
    (rauzyFractal_isCompact hz hz_ne).image (by fun_prop))).isClosed
  have hsub : rauzyFractal z ⊆ C := by
    apply closure_minimal _ hC
    rintro w ⟨L, u, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨sliceName u 0 Q, conjugateCoordinate z (sliceName u Q L), ?_, ?_⟩
    · exact subset_closure ⟨L, sliceName u Q L, rfl⟩
    · exact (coordinate_split u z Q).symm
  intro w hw
  obtain ⟨u, k, hk, he⟩ := mem_iUnion.mp (hsub hw)
  exact ⟨conjugateCoordinate z u, ⟨u, rfl⟩, k, hk, he.symm⟩

private theorem positive_volume {z : ℂ}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (β : ℂ)) : 0 < volume (rauzyFractal z) := by
  classical
  let K := rauzyFractal z
  let c := Real.sqrt (β - 1)
  let ρ : ℕ → ℝ := fun Q => c * ‖z‖ ^ Q / 2
  have hc : 0 < c := Real.sqrt_pos.mpr (sub_pos.mpr one_lt_tribonacciConstant)
  have hroot := (Binet.tribonacci_secondary_root_relations hz hz_ne).2.2
  have hr : 0 < ‖z‖ := by
    have hn := norm_nonneg z
    by_contra h
    have hzero : ‖z‖ = 0 := le_antisymm (not_lt.mp h) hn
    rw [hzero] at hroot
    norm_num at hroot
  have hr1 := Binet.tribonacci_secondary_root_abs_lt_one hz hz_ne
  have hρ : ∀ Q, 0 < ρ Q := fun Q => div_pos (mul_pos hc (pow_pos hr Q)) (by norm_num)
  have hK := rauzyFractal_isCompact hz hz_ne
  have hlim : Tendsto (fun Q => volume.real (cthickening (ρ Q) K)) atTop
      (𝓝 (volume.real K)) := by
    have hρlim : Tendsto ρ atTop (𝓝 0) := by
      simpa only [mul_zero, zero_div] using
        (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)).div_const 2
    exact (ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp
      ((tendsto_measure_cthickening_of_isCompact hK).comp hρlim)
  have hlower : ∀ Q, c ^ 2 * Real.pi / 4 ≤ volume.real (cthickening (ρ Q) K) := by
    intro Q
    let B : TribonacciName Q → Set ℂ := fun u => ball (conjugateCoordinate z u) (ρ Q)
    have hdisj : Pairwise (Disjoint on B) := by
      intro u v huv
      apply ball_disjoint_ball
      have hs := Separation.conjugateCoordinate_separation hz hz_ne Q u v huv
      dsimp [ρ]
      linarith
    have hU : (⋃ u, B u) ⊆ cthickening (ρ Q) K := by
      intro w hw
      obtain ⟨u, hu⟩ := mem_iUnion.mp hw
      exact mem_cthickening_of_dist_le w (conjugateCoordinate z u) (ρ Q) K
        (subset_closure ⟨Q, u, rfl⟩) (le_of_lt hu)
    have harea : volume.real (⋃ u, B u) =
        (Fintype.card (TribonacciName Q) : ℝ) * ((ρ Q) ^ 2 * Real.pi) := by
      rw [measureReal_iUnion_fintype hdisj (fun _ => measurableSet_ball)]
      simp only [B, measureReal_def, Complex.volume_ball, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (hρ Q).le, ENNReal.coe_toReal,
        NNReal.coe_real_pi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpow : β ^ Q * (‖z‖ ^ Q) ^ 2 = 1 := by
      calc
        _ = (β * ‖z‖ ^ 2) ^ Q := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm Q 2]
        _ = 1 := by rw [hroot, one_pow]
    calc
      c ^ 2 * Real.pi / 4 = β ^ Q * ((ρ Q) ^ 2 * Real.pi) := by
        calc
          _ = (β ^ Q * (‖z‖ ^ Q) ^ 2) * (c ^ 2 * Real.pi / 4) := by rw [hpow, one_mul]
          _ = _ := by dsimp [ρ]; ring
      _ ≤ (Fintype.card (TribonacciName Q) : ℝ) * ((ρ Q) ^ 2 * Real.pi) :=
        mul_le_mul_of_nonneg_right (name_card_lower Q) (by positivity)
      _ = volume.real (⋃ u, B u) := harea.symm
      _ ≤ volume.real (cthickening (ρ Q) K) :=
        measureReal_mono hU (hK.isBounded.cthickening.measure_lt_top.ne)
  have harea : 0 < volume.real K :=
    (by positivity : 0 < c ^ 2 * Real.pi / 4).trans_le (ge_of_tendsto' hlim hlower)
  exact ENNReal.toReal_pos_iff.mp harea |>.1

/-- The separated-cylinder data is constructed for the actual Rauzy closure;
all positivity and covering fields are discharged from the two root hypotheses. -/
noncomputable def tribonacciCylinderSystem {z : Complex}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (Values.tribonacciConstant : Complex)) : Interior.SeparatedCylinderSystem := by
  have hroot := (Binet.tribonacci_secondary_root_relations hz hz_ne).2.2
  have hr : 0 < ‖z‖ := by
    have hn := norm_nonneg z
    by_contra h
    have hzero : ‖z‖ = 0 := le_antisymm (not_lt.mp h) hn
    rw [hzero] at hroot
    norm_num at hroot
  have hr1 := Binet.tribonacci_secondary_root_abs_lt_one hz hz_ne
  exact {
    carrier := rauzyFractal z
    compact := rauzyFractal_isCompact hz hz_ne
    positive_volume := positive_volume hz hz_ne
    radius := (1 - ‖z‖)⁻¹
    separation := Real.sqrt (β - 1)
    radius_nonneg := le_of_lt (inv_pos.mpr (sub_pos.mpr hr1))
    separation_pos := Real.sqrt_pos.mpr (sub_pos.mpr one_lt_tribonacciConstant)
    bounded := rauzyFractal_subset_closedBall hz hz_ne
    contraction := z
    norm_pos := hr
    norm_lt_one := hr1
    centers := prefixCenters z
    separated := by
      rintro Q a ⟨u, rfl⟩ b ⟨v, rfl⟩ huv
      exact Separation.conjugateCoordinate_separation hz hz_ne Q u v
        (fun he => huv (he ▸ rfl))
    upper_cover := upper_cylinder_cover hz hz_ne }

/-- The closure of all finite admissible exponent-zero Tribonacci sums has
nonempty interior at either characteristic root distinct from the Perron root. -/
theorem rauzyFractal_interior_nonempty {z : Complex}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (Values.tribonacciConstant : Complex)) :
    (interior (RauzyFractal.rauzyFractal z)).Nonempty := by
  exact Interior.interior_nonempty_of_separated_cylinders (tribonacciCylinderSystem hz hz_ne)

end D5.S3.Geometry.Rauzy.TribonacciInterior
