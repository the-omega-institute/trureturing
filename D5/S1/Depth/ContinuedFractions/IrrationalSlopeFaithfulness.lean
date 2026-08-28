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

-- Irrational slopes faithfully encode integer pairs at infinite precision. Every irrational
-- slope works, the golden ratio is not the only such slope, and its additional finite-precision
-- feature is witnessed by the effective golden Hurwitz separation bound.
theorem irrational_slope_faithfulness (alpha : Real) (halpha : Irrational alpha) :
    Function.Injective (slopeEncoding alpha) ∧
      (∀ beta : Real, Irrational beta → Function.Injective (slopeEncoding beta)) ∧
      (∃ beta : Real,
        beta ≠ Real.goldenRatio ∧ Irrational beta ∧ Function.Injective (slopeEncoding beta)) ∧
      (∀ q : Rat,
        1 / (Real.sqrt 5 * (q.den : Real) ^ 2 + q.den) < |Real.goldenRatio - q|) := by
  have hall : ∀ beta : Real, Irrational beta → Function.Injective (slopeEncoding beta) :=
    fun _ hbeta => slope_encoding_injective_of_irrational hbeta
  refine ⟨hall alpha halpha, hall, ?_, D5.S1.Depth.golden_hurwitz_bound⟩
  refine ⟨Real.goldenConj, ?_, Real.goldenConj_irrational, hall _ Real.goldenConj_irrational⟩
  have hpositive : 0 < Real.goldenRatio - Real.goldenConj := by
    rw [Real.goldenRatio_sub_goldenConj]
    positivity
  exact (sub_pos.mp hpositive).ne

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

#print axioms irrational_slope_faithfulness

end D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness
