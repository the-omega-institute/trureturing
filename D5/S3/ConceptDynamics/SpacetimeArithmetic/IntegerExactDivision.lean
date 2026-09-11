/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision.division_domains_equal_claim; result=D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision.division_domains_equal_refuted; claim=D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision.division_domains_equal_claim
   digest: Exact integer division selects its unique representative; half separates its domain. -/

import D5.S3.ConceptDynamics.SpacetimeArithmetic.RationalQuotient

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeArithmetic.IntegerExactDivision

open Spacetime.ComplementCharge Spacetime.ComplementFibers
open Spacetime.IntegerRepresentatives Spacetime.GeneratedProduct
open RichRational RationalQuotient

noncomputable section
variable {d : Nat}

def ExactGuard (x y : BalancedRich d) : Prop := balancedQ y ≠ 0 ∧ balancedQ y ∣ balancedQ x

theorem exact_guard_congr {x x' y y' : BalancedRich d}
    (hx : balancedQ x = balancedQ x') (hy : balancedQ y = balancedQ y') :
    ExactGuard x y ↔ ExactGuard x' y' := by
  simp only [ExactGuard, hx, hy]

theorem exact_quotient_exists_unique (x y : BalancedRich d) (h : ExactGuard x y) :
    ∃! k : Int, balancedQ x = k * balancedQ y := by
  obtain ⟨k, hk⟩ := h.2
  refine ⟨k, by simpa [mul_comm] using hk, ?_⟩
  intro l hl
  exact mul_right_cancel₀ h.1 (hl.symm.trans (by simpa [mul_comm] using hk))

/-- Selection is from the divisibility witness, and has no value outside the exact guard. -/
def exactQuotient (x y : BalancedRich d) (h : ExactGuard x y) : Int :=
  Classical.choose (exact_quotient_exists_unique x y h)

theorem exactQuotient_spec (x y : BalancedRich d) (h : ExactGuard x y) :
    balancedQ x = exactQuotient x y h * balancedQ y :=
  (Classical.choose_spec (exact_quotient_exists_unique x y h)).1

theorem exactQuotient_unique (x y : BalancedRich d) (h : ExactGuard x y)
    (k : Int) (hk : balancedQ x = k * balancedQ y) : exactQuotient x y h = k :=
  ((Classical.choose_spec (exact_quotient_exists_unique x y h)).2 k hk).symm

def exactDivide (x y : BalancedRich d) (h : ExactGuard x y) : BalancedRich d :=
  balancedSection d (exactQuotient x y h)

theorem exactDivide_literal (x y : BalancedRich d) (h : ExactGuard x y)
    (k : Int) (hk : balancedQ x = k * balancedQ y) :
    (exactDivide x y h).val = representative d k := by
  rw [exactDivide, exactQuotient_unique x y h k hk]
  rfl

theorem exactDivide_readout (x y : BalancedRich d) (h : ExactGuard x y) :
    balancedQ (exactDivide x y h) = exactQuotient x y h :=
  balancedSection_rightInverse d _

theorem exactDivide_congr {x x' y y' : BalancedRich d}
    (hx : balancedQ x = balancedQ x') (hy : balancedQ y = balancedQ y')
    (h : ExactGuard x y) (h' : ExactGuard x' y') :
    exactDivide x y h = exactDivide x' y' h' := by
  unfold exactDivide
  congr 1
  apply exactQuotient_unique x y h
  rw [hx, hy]
  exact exactQuotient_spec x' y' h'

theorem fraction_eq_integer_iff (r : Fraction d) (k : Int) :
    readout r = (k : Rat) ↔ balancedQ r.numerator = k * balancedQ r.denominator := by
  rw [RichRational.readout, div_eq_iff (denominator_cast_ne_zero r)]
  exact_mod_cast (Iff.rfl :
    balancedQ r.numerator = k * balancedQ r.denominator ↔
      balancedQ r.numerator = k * balancedQ r.denominator)

theorem exact_guard_iff_integer_value (r : Fraction d) :
    ExactGuard r.numerator r.denominator ↔ ∃ k : Int, readout r = (k : Rat) := by
  constructor
  · intro h
    exact ⟨exactQuotient _ _ h, (fraction_eq_integer_iff r _).mpr (exactQuotient_spec _ _ h)⟩
  · rintro ⟨k, hk⟩
    exact ⟨r.denominator_ne_zero, k, by
      simpa [mul_comm] using (fraction_eq_integer_iff r k).mp hk⟩

theorem exact_guard_fraction_congr {r s : Fraction d} (h : CrossEquivalent r s) :
    ExactGuard r.numerator r.denominator ↔ ExactGuard s.numerator s.denominator := by
  rw [exact_guard_iff_integer_value, exact_guard_iff_integer_value,
    (cross_iff_readout r s).mp h]

theorem fraction_exactDivide (r : Fraction d) (h : ExactGuard r.numerator r.denominator) :
    readout r = (balancedQ (exactDivide r.numerator r.denominator h) : Rat) := by
  rw [exactDivide_readout]
  exact (fraction_eq_integer_iff r _).mpr (exactQuotient_spec _ _ h)

theorem quotient_exactDivide (r : Fraction d) (h : ExactGuard r.numerator r.denominator) :
    classOf r = classOf (integerEmbedding (exactDivide r.numerator r.denominator h)) := by
  apply (rational_quotient_equiv d).injective
  rw [quotient_readout, quotient_readout, integerEmbedding_readout]
  exact fraction_exactDivide r h

/-- For every integer and every dimension, the generated product has more archived events
than the canonical representative of its unchanged readout. -/
theorem section_loses_product_history (d : Nat) (n : Int) :
    balancedSection d (balancedQ (productBalanced (balancedSection d n) (balancedSection d 1))) ≠
      productBalanced (balancedSection d n) (balancedSection d 1) := by
  have hq : balancedQ (productBalanced (balancedSection d n) (balancedSection d 1)) = n := by
    change q (product (representative d n) (representative d 1)) = n
    rw [q_product, representative_readout, representative_readout, mul_one]
  rw [hq]
  intro h
  have hc := congrArg (fun x : BalancedRich d => x.val.1.archive.events.card) h
  change (representativeArchive d n).events.card =
    (archive (representativeContext d n) (representativeContext d 1)).events.card at hc
  rw [archive_card] at hc
  change (representativeArchive d n).events.card =
    (representativeArchive d n).events.card + (representativeArchive d 1).events.card +
      (representativeContext d n).current.card * (representativeContext d 1).current.card at hc
  rw [representative_archive_card, representative_archive_card,
    representative_current_card, representative_current_card] at hc
  simp only [Int.natAbs_one, mul_one] at hc
  omega

theorem exactDivide_by_one (x : BalancedRich d) :
    ExactGuard x (balancedSection d 1) := by
  unfold ExactGuard
  rw [balancedSection_rightInverse d]
  simp

theorem exactDivide_loses_product_history (d : Nat) (n : Int) :
    let x := productBalanced (balancedSection d n) (balancedSection d 1)
    exactDivide x (balancedSection d 1) (exactDivide_by_one x) ≠ x := by
  dsimp only
  have hk := exactQuotient_unique _ _
    (exactDivide_by_one (productBalanced (balancedSection d n) (balancedSection d 1)))
    (balancedQ (productBalanced (balancedSection d n) (balancedSection d 1)))
    (by rw [balancedSection_rightInverse d, mul_one])
  rw [exactDivide, hk]
  exact section_loses_product_history d n

/-- The independently specified stronger claim denied by the source's half example. -/
def division_domains_equal_claim : Prop :=
  ∀ x y : BalancedRich 3, ExactGuard x y ↔ DivisionGuard (integerEmbedding y)

/-- The source's actual legal half pair supplies the domain counterexample. -/
def half : Fraction 3 where
  numerator := balancedSection 3 1
  denominator := balancedSection 3 2
  denominator_ne_zero := by rw [balancedSection_rightInverse 3]; decide

theorem division_domains_equal_refuted : ¬ division_domains_equal_claim := by
  intro h
  have hy : DivisionGuard (integerEmbedding half.denominator) := half.denominator_ne_zero
  have hexact := (h half.numerator half.denominator).mpr hy
  have hdvd := hexact.2
  change balancedQ (balancedSection 3 2) ∣ balancedQ (balancedSection 3 1) at hdvd
  rw [balancedSection_rightInverse 3, balancedSection_rightInverse 3] at hdvd
  norm_num at hdvd

end
end D5.S3.ConceptDynamics.SpacetimeArithmetic.IntegerExactDivision
