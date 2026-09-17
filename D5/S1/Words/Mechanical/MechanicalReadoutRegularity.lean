/- GID: D5/S1/Words/Mechanical/MechanicalReadoutRegularity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalReadoutRegularity
   mirror-E: none(waiver:actual-infinite-readout-continuity-classification)
   anchors: []
   utility: none
   digest: Integer hits classify all fixed-phase continuity points of the completed geometric readout, with a positive jump certificate. -/

import D5.S1.Words.Mechanical.MechanicalReadoutOrder

/-!
# Pointwise regularity of the completed mechanical readout

The L1 isometry of the existing completion does not imply continuity of each
fixed-phase readout. This theorem classifies that continuity using the actual
integer hits x+k*alpha. It also derives a quantitative jump certificate at
every hit from the cumulative-floor Abel identity. No jump size, local
constancy radius, or finite-prefix stability certificate is an assumption.

Continuity is written in its explicit real epsilon-delta form. The phase is
any fixed real number; only the parameter at which continuity is tested lies
in (0,1). The ratio lies in (0,1); at ratio zero only the first bit survives,
so the stated all-integer-hits criterion would be false.

Related classical background: Laurent and Nogueira, Rotation number of
contracted rotations, J. Mod. Dyn. 12 (2018), DOI 10.3934/jmd.2018007,
and Kwon, A devil's staircase from rotations and irrationality measures for
Liouville numbers, arXiv:0709.1642. Their exact maps and one-sided conventions
are not identified with the present arbitrary-phase readout without proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalReadoutRegularity

open Set Finset
open scoped BigOperators
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalReadoutOrder

/-- The completed readout is continuous in slope at a fixed phase exactly
when no positive-time cumulative floor is at an integer. At an integer hit
time k, every smaller admissible slope is separated from its value by at
least (1-r)^2*r^(k-1). Both conclusions are obtained from actual finite
floors and the already proved geometric tail, not an assumed step function. -/
theorem geometric_readout_continuity_and_jump
    (r alpha x : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (ha : alpha ∈ Ioo (0 : ℝ) 1) :
    ((∀ eps : ℝ, 0 < eps → ∃ radius : ℝ, 0 < radius ∧
      ∀ beta : ℝ, |beta - alpha| < radius →
        |geometricReadout r beta x - geometricReadout r alpha x| < eps) ↔
      ∀ k : ℕ, 0 < k → ∀ z : ℤ, x + (k : ℝ) * alpha ≠ (z : ℝ)) ∧
    (∀ k : ℕ, 0 < k → ∀ z : ℤ, x + (k : ℝ) * alpha = (z : ℝ) →
      ∀ beta : ℝ, beta ∈ Ico (0 : ℝ) alpha →
        (1 - r) ^ 2 * r ^ (k - 1) ≤
          geometricReadout r alpha x - geometricReadout r beta x) := by
  classical
  let q : ℕ → ℝ := fun k => (1 - r) * r ^ k
  let G : ℝ → ℝ := fun a => geometricReadout r a x
  let P : ℝ → ℕ → ℝ := fun a N => weightedPrefix q a x N
  have htail (a : ℝ) (ha' : a ∈ Ico (0 : ℝ) 1) (N : ℕ) :
      0 ≤ G a - P a N ∧ G a - P a N ≤ r ^ N :=
    (geometric_readout_isometric_completion r a a hr0.le hr1 ha' ha').2.2.1 x N
  have hq0 (j : ℕ) : 0 ≤ q j :=
    mul_nonneg (sub_nonneg.mpr hr1.le) (pow_nonneg hr0.le j)
  have hdrop (j : ℕ) : q j - q (j + 1) = (1 - r) ^ 2 * r ^ j := by
    dsimp [q]
    rw [pow_succ]
    ring
  have hdrop0 (j : ℕ) : 0 ≤ q j - q (j + 1) := by
    rw [hdrop]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le _)
  -- A cumulative integer hit produces a strictly positive increment in the
  -- Abel sum, even if individual neighboring bits have opposite changes.
  have hjump (k : ℕ) (hk : 0 < k) (z : ℤ)
      (hz : x + (k : ℝ) * alpha = (z : ℝ))
      (beta : ℝ) (hb : beta ∈ Ico (0 : ℝ) alpha) :
      (1 - r) ^ 2 * r ^ (k - 1) ≤ G alpha - G beta := by
    let D : ℕ → ℝ := fun j =>
      (⌊x + (j : ℝ) * alpha⌋ : ℝ) - (⌊x + (j : ℝ) * beta⌋ : ℝ)
    let A : ℝ := (1 - r) ^ 2 * r ^ (k - 1)
    have hD0 : D 0 = 0 := by simp [D]
    have hD (j : ℕ) : 0 ≤ D j := by
      apply sub_nonneg.mpr
      exact_mod_cast (Int.floor_mono (add_le_add_left
        (mul_le_mul_of_nonneg_left hb.2.le (Nat.cast_nonneg (R := ℝ) j)) x))
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hfloor : ⌊x + (k : ℝ) * beta⌋ < z := Int.floor_lt.mpr (by
      have hmul := mul_lt_mul_of_pos_left hb.2 hkR
      linarith)
    have hDk : 1 ≤ D k := by
      dsimp [D]
      rw [hz, Int.floor_intCast]
      exact_mod_cast (show (1 : ℤ) ≤ z - ⌊x + (k : ℝ) * beta⌋ by omega)
    have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le _)
    have hparts : ∀ N : ℕ,
        (∑ j ∈ range N, q j * (D (j + 1) - D j)) =
          q N * D N + ∑ j ∈ range N, (q j - q (j + 1)) * D (j + 1) := by
      intro N
      induction N with
      | zero => simp [hD0]
      | succ N ih => rw [sum_range_succ, ih, sum_range_succ]; ring
    have hdiff (N : ℕ) : P alpha N - P beta N =
        q N * D N + ∑ j ∈ range N, (q j - q (j + 1)) * D (j + 1) := by
      dsimp [P, weightedPrefix]
      rw [← sum_sub_distrib, ← hparts N]
      apply sum_congr rfl
      intro j hj
      dsimp [D, lowerMechanicalLetter]
      push_cast
      ring
    have hfinite (N : ℕ) (hkN : k ≤ N) : A ≤ P alpha N - P beta N := by
      have hindex : k - 1 ∈ range N := mem_range.mpr (by omega)
      have hsingle := single_le_sum
        (fun j (_ : j ∈ range N) => mul_nonneg (hdrop0 j) (hD (j + 1))) hindex
      have hkm : k - 1 + 1 = k := by omega
      rw [hdrop, hkm] at hsingle
      have hprod : A ≤ A * D k := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hDk hA
      rw [hdiff]
      have hterm := mul_nonneg (hq0 N) (hD N)
      change A * D k ≤ _ at hsingle
      linarith
    by_contra hnot
    have hgap : 0 < A - (G alpha - G beta) := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hgap hr1
    have hsmall : r ^ (M + k) < A - (G alpha - G beta) := by
      calc
        r ^ (M + k) = r ^ M * r ^ k := pow_add _ _ _
        _ ≤ r ^ M * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ hr0.le hr1.le) (pow_nonneg hr0.le _)
        _ < A - (G alpha - G beta) := by simpa only [mul_one] using hM
    have hf := hfinite (M + k) (by omega)
    have htA := htail alpha ⟨ha.1.le, ha.2⟩ (M + k)
    have htB := htail beta ⟨hb.1, hb.2.trans ha.2⟩ (M + k)
    linarith
  -- Every nonresonant finite prefix has an actual positive stability radius.
  -- Combining equal prefixes with two one-sided tails costs r^N, not 2*r^N.
  have hlocal (N : ℕ)
      (hreg : ∀ k : ℕ, 0 < k → k ≤ N → ∀ z : ℤ,
        x + (k : ℝ) * alpha ≠ (z : ℝ)) :
      ∃ radius : ℝ, 0 < radius ∧ ∀ beta : ℝ, |beta - alpha| < radius →
        |G beta - G alpha| ≤ r ^ N := by
    let margin : Fin N → ℝ := fun i =>
      let t := x + ((i.val + 1 : ℕ) : ℝ) * alpha
      min (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t) / ((i.val + 1 : ℕ) : ℝ)
    have hmpos (i : Fin N) : 0 < margin i := by
      let t := x + ((i.val + 1 : ℕ) : ℝ) * alpha
      have hne : t ≠ (⌊t⌋ : ℝ) := hreg (i.val + 1) (by omega) (by omega) ⌊t⌋
      have hlo : (⌊t⌋ : ℝ) < t := lt_of_le_of_ne (Int.floor_le t) (Ne.symm hne)
      have hhi : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
      exact div_pos (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)) (by positivity)
    let margins : Finset ℝ := insert alpha (insert (1 - alpha) (univ.image margin))
    have hnonempty : margins.Nonempty := ⟨alpha, mem_insert_self _ _⟩
    have hpos : ∀ t ∈ margins, 0 < t := by
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact ha.1
      · rcases mem_insert.mp ht with rfl | ht
        · exact sub_pos.mpr ha.2
        · obtain ⟨i, _, rfl⟩ := mem_image.mp ht
          exact hmpos i
    let g := margins.min' hnonempty
    have hg : 0 < g := hpos g (min'_mem margins hnonempty)
    have hga : g ≤ alpha := min'_le margins _ (mem_insert_self _ _)
    have hgb : g ≤ 1 - alpha := min'_le margins _
      (mem_insert_of_mem (mem_insert_self _ _))
    have hgm (i : Fin N) : g ≤ margin i := min'_le margins _
      (mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨i, mem_univ _, rfl⟩)))
    refine ⟨g / 2, by positivity, ?_⟩
    intro beta hbeta
    have hsmall : |beta - alpha| < g := lt_trans hbeta (by linarith)
    have habs := abs_lt.mp hsmall
    have hb : beta ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hfloors (k : ℕ) (hk : k ≤ N) :
        ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋ := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · let i : Fin N := ⟨k - 1, by omega⟩
        have hi : i.val + 1 = k := by dsimp [i]; omega
        have hmi := hsmall.trans_le (hgm i)
        dsimp only [margin] at hmi
        rw [hi] at hmi
        let t := x + (k : ℝ) * alpha
        have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hshift : |(k : ℝ) * (beta - alpha)| <
            min (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t) := by
          rw [abs_mul, abs_of_pos hkR, mul_comm]
          exact (lt_div_iff₀ hkR).mp hmi
        have hsl := (abs_lt.mp hshift).1
        have hsr := (abs_lt.mp hshift).2
        have heq : x + (k : ℝ) * beta = t + (k : ℝ) * (beta - alpha) := by
          dsimp [t]
          ring
        apply Int.floor_eq_iff.mpr
        constructor <;> linarith [min_le_left (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t),
          min_le_right (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t)]
    have hprefix : P beta N = P alpha N := by
      dsimp [P, weightedPrefix]
      apply sum_congr rfl
      intro j hj
      have hjN := mem_range.mp hj
      have hletter : lowerMechanicalLetter beta x j = lowerMechanicalLetter alpha x j := by
        unfold lowerMechanicalLetter
        rw [hfloors (j + 1) (by omega), hfloors j (by omega)]
      rw [hletter]
    have htA := htail alpha ⟨ha.1.le, ha.2⟩ N
    have htB := htail beta hb N
    rw [hprefix] at htB
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨⟨?_, ?_⟩, hjump⟩
  · intro hcontinuous k hk z hz
    have h1r : 0 < 1 - r := sub_pos.mpr hr1
    have hA : 0 < (1 - r) ^ 2 * r ^ (k - 1) := by positivity
    obtain ⟨radius, hradius, hbound⟩ := hcontinuous
      ((1 - r) ^ 2 * r ^ (k - 1) / 2) (by positivity)
    let d := min radius alpha / 2
    let beta := alpha - d
    have hd : 0 < d := div_pos (lt_min hradius ha.1) (by norm_num)
    have hdr : d < radius := by dsimp [d]; linarith [min_le_left radius alpha]
    have hda : d < alpha := by dsimp [d]; linarith [min_le_right radius alpha]
    have hb : beta ∈ Ico (0 : ℝ) alpha := by dsimp [beta]; constructor <;> linarith
    have hdist : |beta - alpha| < radius := by
      have heq : beta - alpha = -d := by dsimp [beta]; ring
      rw [heq, abs_neg, abs_of_pos hd]
      exact hdr
    have hclose := hbound beta hdist
    have hlower := hjump k hk z hz beta hb
    have hleft := (abs_lt.mp hclose).1
    change -( (1 - r) ^ 2 * r ^ (k - 1) / 2) < G beta - G alpha at hleft
    linarith
  · intro hregular eps heps
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one heps hr1
    obtain ⟨radius, hradius, hbound⟩ := hlocal N (fun k hk _ z => hregular k hk z)
    exact ⟨radius, hradius, fun beta hb => (hbound beta hb).trans_lt hN⟩

#print axioms geometric_readout_continuity_and_jump

end D5.S1.Words.Mechanical.MechanicalReadoutRegularity
