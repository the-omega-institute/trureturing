/- GID: D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Irrational slopes encode integer pairs; the golden slope has a finite pairwise gap. -/

import D5.S1.Depth.GoldenHurwitzBound

namespace D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness

-- The real encoding of an integer pair at slope `alpha`.
def slopeEncoding (alpha : Real) (label : Int × Int) : Real :=
  alpha * label.1 + label.2

-- The effective separation visible within horizontal displacement budget `precision`.
noncomputable def finitePrecisionGap (precision : Nat) : Real :=
  1 / (Real.sqrt 5 * precision + 1)

-- Finite-precision stability requires distinct labels within the horizontal precision budget to
-- remain pairwise distinguishable by an effective output gap.
def FinitePrecisionStable (encoding : Int × Int → Real) : Prop :=
  ∀ precision : Nat, 0 < precision → ∀ left right : Int × Int,
    Int.natAbs (left.1 - right.1) ≤ precision → left ≠ right →
      finitePrecisionGap precision < |encoding left - encoding right|

private theorem slope_encoding_injective_of_irrational {alpha : Real}
    (halpha : Irrational alpha) : Function.Injective (slopeEncoding alpha) := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ hencoding
  simp only [slopeEncoding] at hencoding
  have hrelation : alpha * ((m - m' : Int) : Real) = ((n' - n : Int) : Real) := by
    norm_num only [Int.cast_sub]
    linarith
  have hm : m = m' := by
    by_contra hne
    have hdiff : m - m' ≠ 0 := sub_ne_zero.mpr hne
    exact (halpha.mul_intCast hdiff).ne_int (n' - n) hrelation
  subst m'
  have hncast : (n : Real) = (n' : Real) := by
    simpa using hencoding
  have hn : n = n' := by
    exact_mod_cast hncast
  exact Prod.ext rfl hn

private theorem golden_finite_precision_stable :
    FinitePrecisionStable (slopeEncoding Real.goldenRatio) := by
  rintro precision hprecision ⟨m, n⟩ ⟨m', n'⟩ hhorizontal hlabels
  set k : Int := m - m'
  set l : Int := n - n'
  have houtput :
      slopeEncoding Real.goldenRatio (m, n) - slopeEncoding Real.goldenRatio (m', n') =
        Real.goldenRatio * (k : Real) + (l : Real) := by
    change Real.goldenRatio * (m : Real) + (n : Real) -
        (Real.goldenRatio * (m' : Real) + (n' : Real)) =
      Real.goldenRatio * ((m - m' : Int) : Real) + ((n - n' : Int) : Real)
    norm_num only [Int.cast_sub]
    ring
  by_cases hk : k = 0
  · have hm : m = m' := sub_eq_zero.mp (by simpa [k] using hk)
    have hl : l ≠ 0 := by
      intro hl
      apply hlabels
      apply Prod.ext
      · exact hm
      · exact sub_eq_zero.mp (by simpa [l] using hl)
    have hgap_one : finitePrecisionGap precision < 1 := by
      have hprecision_real : (0 : Real) < precision := by exact_mod_cast hprecision
      have hsqrt : (0 : Real) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      have hdenominator :
          (1 : Real) < Real.sqrt 5 * (precision : Real) + 1 := by
        nlinarith [mul_pos hsqrt hprecision_real]
      simpa [finitePrecisionGap] using
        (one_div_lt_one_div_of_lt (show (0 : Real) < 1 by norm_num) hdenominator)
    have hone : (1 : Real) ≤ |(l : Real)| := by
      exact_mod_cast Int.one_le_abs hl
    rw [houtput, hk]
    simpa using hgap_one.trans_le hone
  · let q : Rat := Rat.divInt (-l) k
    have hk_real : (k : Real) ≠ 0 := by exact_mod_cast hk
    have hden_le_k : q.den ≤ k.natAbs := by
      have hdiv : ((q.den : Int) ∣ k) := by
        simpa [q] using Rat.den_dvd (-l) k
      simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hk
    have hden_le_precision : q.den ≤ precision :=
      hden_le_k.trans (by simpa [k] using hhorizontal)
    have hden : (0 : Real) < q.den := by exact_mod_cast q.pos
    have hden_real : (q.den : Real) ≤ precision := by exact_mod_cast hden_le_precision
    have hdenominator :
        Real.sqrt 5 * (q.den : Real) + 1 ≤
          Real.sqrt 5 * (precision : Real) + 1 := by
      gcongr
    have hscale :
        (q.den : Real) *
            (1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den)) =
          1 / (Real.sqrt 5 * (q.den : Real) + 1) := by
      field_simp
    have hqcast : (q : Real) = (-l : Int) / (k : Int) := by
      simpa [q] using Rat.cast_divInt_of_ne_zero (-l) hk_real
    have hscaled :
        (k : Real) * (Real.goldenRatio - (q : Real)) =
          Real.goldenRatio * (k : Real) + (l : Real) := by
      rw [hqcast]
      rw [Int.cast_neg]
      field_simp
      ring
    have hden_le_abs_k : (q.den : Real) ≤ |(k : Real)| := by
      have hcast : (q.den : Real) ≤ (k.natAbs : Real) := by exact_mod_cast hden_le_k
      simpa [Nat.cast_natAbs, Int.cast_abs] using hcast
    calc
      finitePrecisionGap precision ≤
          1 / (Real.sqrt 5 * (q.den : Real) + 1) :=
        one_div_le_one_div_of_le (by positivity) hdenominator
      _ = (q.den : Real) *
          (1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den)) := hscale.symm
      _ < (q.den : Real) * |Real.goldenRatio - (q : Real)| :=
        mul_lt_mul_of_pos_left (D5.S1.Depth.golden_hurwitz_bound q) hden
      _ ≤ |(k : Real)| * |Real.goldenRatio - (q : Real)| := by gcongr
      _ = |(k : Real) * (Real.goldenRatio - (q : Real))| := (abs_mul _ _).symm
      _ = |slopeEncoding Real.goldenRatio (m, n) -
          slopeEncoding Real.goldenRatio (m', n')| := by rw [hscaled, houtput]

-- Irrational slopes faithfully encode integer pairs at infinite precision. Every irrational
-- slope works, the golden ratio is not the only such slope, and its additional finite-precision
-- feature is pairwise finite-precision stability, proved using the golden Hurwitz bound.
theorem irrational_slope_faithfulness (alpha : Real) (halpha : Irrational alpha) :
    Function.Injective (slopeEncoding alpha) ∧
      (∀ beta : Real, Irrational beta → Function.Injective (slopeEncoding beta)) ∧
      (∃ beta : Real,
        beta ≠ Real.goldenRatio ∧ Irrational beta ∧ Function.Injective (slopeEncoding beta)) ∧
      FinitePrecisionStable (slopeEncoding Real.goldenRatio) := by
  have hall : ∀ beta : Real, Irrational beta → Function.Injective (slopeEncoding beta) :=
    fun _ hbeta => slope_encoding_injective_of_irrational hbeta
  refine ⟨hall alpha halpha, hall, ?_, ?_⟩
  · refine ⟨Real.goldenConj, ?_, Real.goldenConj_irrational,
      hall _ Real.goldenConj_irrational⟩
    have hpositive : 0 < Real.goldenRatio - Real.goldenConj := by
      rw [Real.goldenRatio_sub_goldenConj]
      positivity
    exact (sub_pos.mp hpositive).ne
  · exact golden_finite_precision_stable

-- Reverse probe: the public proposition separates two concrete integer labels.
example (alpha : Real) (halpha : Irrational alpha) :
    slopeEncoding alpha (1, 0) ≠ slopeEncoding alpha (0, 0) := by
  intro hequal
  have hpairs := (irrational_slope_faithfulness alpha halpha).1 hequal
  norm_num at hpairs

-- Trivialization probe: zero slope collapses labels that differ in their first coordinate.
example : ¬Function.Injective (slopeEncoding 0) := by
  intro hinjective
  have hpairs := hinjective (show slopeEncoding 0 (1, 0) = slopeEncoding 0 (0, 0) by
    norm_num [slopeEncoding])
  norm_num at hpairs

-- Reverse probe for CAS-A4: the public fourth clause separates two distinct labels.
example : finitePrecisionGap 1 <
    |slopeEncoding Real.goldenRatio (0, 0) - slopeEncoding Real.goldenRatio (0, 1)| := by
  exact (irrational_slope_faithfulness Real.goldenRatio Real.goldenRatio_irrational).2.2.2
    1 (by norm_num) (0, 0) (0, 1) (by norm_num) (by norm_num)

-- Pairwise-constant probe: even a nonzero constant encoding must fail finite-precision stability.
example : ¬FinitePrecisionStable (fun _ => (1 : Real)) := by
  intro hstable
  have hgap := hstable 1 (by norm_num) (0, 0) (0, 1) (by norm_num) (by norm_num)
  have hpositive : 0 < finitePrecisionGap 1 := by
    unfold finitePrecisionGap
    positivity
  norm_num at hgap
  linarith

#print axioms irrational_slope_faithfulness

end D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness
