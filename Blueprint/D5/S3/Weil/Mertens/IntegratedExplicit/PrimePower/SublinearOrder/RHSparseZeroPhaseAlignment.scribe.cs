using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHSparseZeroPhaseAlignmentDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSparseZeroPhaseAlignment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse omitted zeta zeros and the signed-window coefficient",
        H("Sparse counts and weighted phase alignment"),
        Blocks(
            Paragraph(Text(
                "Assume the Riemann hypothesis. For a set S of real ordinates, use exactly "
                + "the positive zeta zeros with ordinates γ ≤ T for the inclusive cutoff at T. "
                + "Write B(T) for the sum of analytic multiplicities over the zeros with γ outside S, "
                + "and Wout(T) for their mass with weights mγ γ/(1/4 + γ²), where mγ is the analytic "
                + "multiplicity. The full harmonic mass W(T) uses the same weights. At W(T) > 0, "
                + "the deficit D(T) is one minus the real-time supremum of the full weighted sine sum "
                + "divided by W(T). "),
                Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup")),
            Describe.Lean(
                DescribeId.Create("omitted-mass-tendsto-zero"),
                DeclarationHandle.Create(Owner + ".omittedMass_tendsto_zero"),
                H("Omitted harmonic mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every S, if B(T)/(T log T) tends to zero as T tends to positive infinity, "
                    + "then Wout(T)/(log T)² tends to zero there. Give each retained zero multiplicity "
                    + "zero inside the sums for B and Wout, and apply the sparse ordinate estimate "
                    + "to this common multiplicity function. "),
                    Ref("D5/S3/Analytic/Oscillation/SparseOrdinateMass"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-phase-defect-le-omitted-mass"),
                DeclarationHandle.Create(Owner + ".weightedPhaseDefect_le_omittedMass"),
                H("Finite cutoff deficit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the inclusion of S into the reals is linearly independent over the rationals, "
                    + "then every real cutoff with W(T) > 0 satisfies D(T) ≤ 2 Wout(T)/W(T). "
                    + "The Riemann hypothesis makes the ordinate injective on the positive zeros. "
                    + "Restrict independence to the retained zeros at the cutoff. Their only integer "
                    + "relation is zero, so their common real-time phase orbit has the quarter-phase "
                    + "point in its closure. The retained score at this point is the retained mass. "
                    + "At every real time the omitted sine sum is at least minus its mass. "
                    + "Continuity carries the resulting bound on the retained score to the quarter-phase "
                    + "point, including when the retained set is empty. "),
                    Ref("D5/S3/Fourier/WeightedPhaseRelationLattice"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-phase-defect-tendsto-zero-of-sparse-count"),
                DeclarationHandle.Create(Owner + ".weightedPhaseDefect_tendsto_zero_of_sparse_count"),
                H("Vanishing phase deficit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If S is rationally linearly independent and B(T)/(T log T) tends to zero "
                    + "at positive infinity, then D(T) tends to zero. The normalized full mass "
                    + "W(T)/(log T)² tends to 1/(4π), so W(T) is eventually positive. "
                    + "The quotient of the normalized omitted mass by the normalized full mass "
                    + "tends to zero. The finite cutoff bound then squeezes the nonnegative deficit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-window-even-cutoff-full-coefficient-of-sparse-count"),
                DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_full_coefficient_of_sparse_count"),
                H("Full signed left-endpoint coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose S is rationally linearly independent and B(T)/(T log T) tends to zero "
                        + "at positive infinity. For natural m and r with m ≥ 2, m + 1 = 2r and "
                        + "μ(r) nonzero, put s = orderRate(m) = 1/2 − 1/(2r) and "
                        + "cₘ = μ(m+1)(m+1)/(m s). At endpoints exp(u) and exp(u+L), divide "
                        + "signedWindowResidual by powerGap at rate s, add cₘ and μ(r) times the "
                        + "root signal at u, and take the absolute value. This is bounded above on "
                        + "a late tail in u for all sufficiently small positive L. The late limsup "
                        + "as u tends to positive infinity, divided by L log²(1/L), tends to "
                        + "|μ(r)|/(4πs) as L tends to zero from above.")),
                    Paragraph(Text(
                        "The weighted-phase equivalence applies to exactly these endpoints, "
                        + "the same signed residual and the same power gap. Its deficit condition is "
                        + "supplied by the omitted-count estimate. Existence of an independent set "
                        + "of actual ordinates satisfying the count condition is open."))),
                DescribeRole.Theorem))));
}
