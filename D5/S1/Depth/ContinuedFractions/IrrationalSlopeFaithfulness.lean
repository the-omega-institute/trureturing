/- GID: D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Irrational slopes faithfully encode integer pairs; the golden slope has a Hurwitz gap. -/

import D5.S1.Depth.GoldenHurwitzBound

namespace D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness

-- The real encoding of an integer pair at slope `alpha`.
def slopeEncoding (alpha : Real) (label : Int × Int) : Real :=
  alpha * label.1 + label.2

-- The primitive integer label whose encoded separation from zero measures approximation by `q`.
def rationalApproximationLabel (q : Rat) : Int × Int :=
  ((q.den : Int), -q.num)

-- The effective separation visible when rational denominators are bounded by `precision`.
noncomputable def finitePrecisionGap (precision : Nat) : Real :=
  1 / (Real.sqrt 5 * precision + 1)

-- An encoding is stable at finite precision when every primitive label of denominator at most
-- `precision` remains separated from zero by the effective precision-dependent gap.
def FinitePrecisionStable (encoding : Int × Int → Real) : Prop :=
  ∀ precision : Nat, 0 < precision → ∀ q : Rat, q.den ≤ precision →
    finitePrecisionGap precision < |encoding (rationalApproximationLabel q)|

-- The old Hurwitz certificate and its required interpretation as finite-precision stability of
-- the actual golden slope encoding are kept together as the fourth semantic clause.
def GoldenFinitePrecisionStability : Prop :=
  (∀ q : Rat,
    1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den) < |Real.goldenRatio - q|) ∧
  FinitePrecisionStable (slopeEncoding Real.goldenRatio)

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

private theorem golden_encoding_separation (q : Rat) :
    1 / (Real.sqrt 5 * (q.den : Real) + 1) <
      |slopeEncoding Real.goldenRatio (rationalApproximationLabel q)| := by
  have hd : (0 : Real) < q.den := by exact_mod_cast q.pos
  have hbound := D5.S1.Depth.golden_hurwitz_bound q
  have hscale :
      (q.den : Real) * (1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den)) =
        1 / (Real.sqrt 5 * (q.den : Real) + 1) := by
    field_simp
  have hencoding :
      slopeEncoding Real.goldenRatio (rationalApproximationLabel q) =
        (q.den : Real) * (Real.goldenRatio - (q : Real)) := by
    rw [Rat.cast_def]
    field_simp
    simp [slopeEncoding, rationalApproximationLabel]
    ring
  calc
    1 / (Real.sqrt 5 * (q.den : Real) + 1) =
        (q.den : Real) *
          (1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den)) := hscale.symm
    _ < (q.den : Real) * |Real.goldenRatio - (q : Real)| :=
      mul_lt_mul_of_pos_left hbound hd
    _ = |slopeEncoding Real.goldenRatio (rationalApproximationLabel q)| := by
      rw [hencoding, abs_mul, abs_of_pos hd]

private theorem golden_finite_precision_stable :
    FinitePrecisionStable (slopeEncoding Real.goldenRatio) := by
  intro precision hprecision q hden
  have hd : (0 : Real) < q.den := by exact_mod_cast q.pos
  have hsqrt : (0 : Real) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hden_real : (q.den : Real) ≤ precision := by exact_mod_cast hden
  have hdenominator :
      Real.sqrt 5 * (q.den : Real) + 1 ≤ Real.sqrt 5 * (precision : Real) + 1 := by
    gcongr
  exact (one_div_le_one_div_of_le (by positivity) hdenominator).trans_lt
    (golden_encoding_separation q)

-- Irrational slopes faithfully encode integer pairs at infinite precision. Every irrational
-- slope works, the golden ratio is not the only such slope, and its additional finite-precision
-- feature is witnessed by the effective golden Hurwitz separation bound.
theorem irrational_slope_faithfulness (alpha : Real) (halpha : Irrational alpha) :
    Function.Injective (slopeEncoding alpha) ∧
      (∀ beta : Real, Irrational beta → Function.Injective (slopeEncoding beta)) ∧
      (∃ beta : Real,
        beta ≠ Real.goldenRatio ∧ Irrational beta ∧ Function.Injective (slopeEncoding beta)) ∧
      GoldenFinitePrecisionStability := by
  have hall : ∀ beta : Real, Irrational beta → Function.Injective (slopeEncoding beta) :=
    fun _ hbeta => slope_encoding_injective_of_irrational hbeta
  refine ⟨hall alpha halpha, hall, ?_, ?_⟩
  · refine ⟨Real.goldenConj, ?_, Real.goldenConj_irrational,
      hall _ Real.goldenConj_irrational⟩
    have hpositive : 0 < Real.goldenRatio - Real.goldenConj := by
      rw [Real.goldenRatio_sub_goldenConj]
      positivity
    exact (sub_pos.mp hpositive).ne
  · exact ⟨D5.S1.Depth.golden_hurwitz_bound, golden_finite_precision_stable⟩

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

-- Reverse probe for the repaired fourth clause: precision one separates the label for `q = 0`.
example : finitePrecisionGap 1 <
    |slopeEncoding Real.goldenRatio (rationalApproximationLabel 0)| := by
  exact (irrational_slope_faithfulness Real.goldenRatio Real.goldenRatio_irrational).2.2.2.2
    1 (by norm_num) 0 (by norm_num)

-- Weak-carrier probe: a constant encoding fails finite-precision stability already at `q = 0`.
example : ¬FinitePrecisionStable (fun _ => 0) := by
  intro hstable
  have hgap := hstable 1 (by norm_num) 0 (by norm_num)
  norm_num [finitePrecisionGap, rationalApproximationLabel] at hgap
  have hpositive : 0 < Real.sqrt 5 + 1 := by positivity
  linarith

-- Nyxid counterexample: the old fourth clause can be proved without observing the encoding.
example : ∀ q : Rat,
    1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den) < |Real.goldenRatio - q| := by
  exact D5.S1.Depth.golden_hurwitz_bound

#print axioms irrational_slope_faithfulness

end D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness
