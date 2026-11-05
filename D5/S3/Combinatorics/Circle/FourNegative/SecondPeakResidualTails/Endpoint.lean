import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Endpoint

/- UNCOMPILED SOURCE PREPARATION. Every original residual cone is covered;
   the final result assumes OriginalDomain alone. Actual physical gates are
   discharged here, then the common native remaining-charge proof constructs
   the original certificate and the SAME physical sigma at literal cut0.
   Full Circle J remains OPEN. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open PacketNormalForm SourceWidth PeriodicShortening RunFirstEarTransport
open private charge from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-- Both sides are ACTUAL physical gates, over the unchanged full domain. -/
private theorem residual_physical_gates (a b c d : ℕ)
    (hdom : OriginalDomain a b c d) : ActualPhysicalGateSides a b c d := by
  obtain ⟨hb,hshape⟩ := hdom
  rcases hshape with h2 | hdiag | h3
  · obtain ⟨rfl,rfl,hd⟩ := h2
    exact c2_physical_gates b d hd hb
  · exact c3_diagonal_physical_gates a b c d hb (Or.inr hdiag)
  · exact c3_diagonal_physical_gates a b c d hb (Or.inl h3)

/-- Entire residual OriginalDomain: one actual physical permutation, both
    complete original orders at literal cut0, matched-new -A and fresh A
    separately, every natural repeated prefix, and both repeated zero totals.
    Complete candidate proof body only; UNCOMPILED. -/
theorem actualSource_residual_joint_lift (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    ∃ sigma : List (Fin (a+b+c+d)),
      sigma.map Fin.val =
        physicalWord a b c d (residualBanks a b c d) (residualOrder c d) ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut0) ∧
      ((sigma.map Fin.castSucc).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum =
        -(1+2^a+2^(a+b)+2^(a+b+c) : ℤ) ∧
      actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (Fin.last (a+b+c+d)) = (1+2^a+2^(a+b)+2^(a+b+c) : ℤ) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
          Set.Icc (0 : ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma cut0)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
          Set.Icc (0 : ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum = 0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma cut0)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum = 0) := by
  exact residual_joint_lift_of_physical_gates a b c d hdom
    (residual_physical_gates a b c d hdom)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
