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
                    "The retained cutoff is quarter-phase compatible if every integer relation "
                    + "on its ordinates has value one under the character at the common quarter "
                    + "phase. At a compatible cutoff with W(T) > 0, "
                    + "0 ≤ D(T) ≤ min(1, 2 Wout(T)/W(T)). The phase orbit closure contains the "
                    + "quarter phase by the annihilator equation. At this point the retained score "
                    + "equals the retained mass. At every real time the omitted sine sum is at least "
                    + "minus its mass. Continuity carries the resulting bound on the retained score "
                    + "to the quarter phase, including when the retained set is empty. The full "
                    + "weighted sine supremum lies between zero and W(T). "),
                    Ref("D5/S3/Fourier/WeightedPhaseRelationLattice"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-phase-defect-tendsto-zero"),
                DeclarationHandle.Create(Owner + ".weightedPhaseDefect_tendsto_zero"),
                H("Vanishing phase deficit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the retained cutoff is eventually quarter-phase compatible and "
                    + "Wout(T)/(log T)² tends to zero, then D(T) tends to zero. "
                    + "The normalized full mass W(T)/(log T)² tends to 1/(4π), so W(T) is "
                    + "eventually positive. The finite bound squeezes the deficit as the quotient "
                    + "of the two normalized masses tends to zero. Rational independence of S "
                    + "implies compatibility at every cutoff, because the ordinate is injective "
                    + "on the positive zeros under RH. A sparse omitted count makes the normalized "
                    + "omitted mass tend to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-window-even-cutoff-full-coefficient-of-sparse-count"),
                DeclarationHandle.Create(Owner + ".signed_window_even_cutoff_full_coefficient_of_sparse_count"),
                H("Full signed left-endpoint coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural m and r with m ≥ 2 and m + 1 = 2r, put "
                        + "s = orderRate(m) = 1/2 − 1/(2r) and "
                        + "cₘ = μ(m+1)(m+1)/(m s). At endpoints exp(u) and exp(u+L), divide "
                        + "signedWindowResidual by powerGap at rate s, add cₘ and μ(r) times the "
                        + "root signal at u, and take the absolute value. This is bounded above on "
                        + "a late tail in u for all sufficiently small positive L. The late limsup "
                        + "as u tends to positive infinity, divided by L log²(1/L), tends to "
                        + "|μ(r)|/(4πs) as L tends to zero from above.")),
                    Paragraph(Text(
                        "When μ(r) is nonzero, assume S is rationally linearly independent "
                        + "and B(T)/(T log T) tends to zero. The original weighted-phase "
                        + "equivalence then uses the vanishing phase deficit supplied by the "
                        + "independent sparse-count specialization. When μ(r) is zero, the exact "
                        + "RH weighted-phase formula gives coefficient zero directly. "
                        + "Existence of an independent set of "
                        + "actual ordinates satisfying the count condition is open."))),
                DescribeRole.Theorem))));
}
