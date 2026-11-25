using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SparseOrdinateMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Oscillation/SparseOrdinateMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic transfer from sparse real cutoffs to harmonic mass.",
        H("Sparse ordinate mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cutoff-mass-tendsto-zero"),
                DeclarationHandle.Create(Prefix + "cutoffMass_tendsto_zero"),
                H("Sparse counts bound the weighted mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let gamma be a real ordinate family with finite inclusive lower cutoffs. "
                    + "Let m and w be nonnegative weights, with w(j) at most m(j)/gamma(j) "
                    + "whenever gamma(j) is positive. If the cutoff sum B of m satisfies "
                    + "B(T)/(T log T) tending to zero, the cutoff sum W of w satisfies "
                    + "W(T)/(log T)^2 tending to zero. For positive T, the shell with "
                    + "T/2 < gamma <= T adds at most 2 B(T)/T. Above a fixed cutoff, "
                    + "successive halving bounds the shell contributions by an arbitrarily "
                    + "small multiple of (log T)^2, because each difference of squared "
                    + "logarithms dominates log(2) log(T). The fixed initial mass vanishes "
                    + "after normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("harmonic-mass-tendsto-zero"),
                DeclarationHandle.Create(Prefix + "harmonicMass_tendsto_zero"),
                H("Harmonic mass with nonnegative real multiplicities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative ordinates and nonnegative real multiplicities m(j), "
                    + "take the weight m(j) gamma(j)/(1/4 + gamma(j)^2). At a positive ordinate "
                    + "the weight is at most m(j)/gamma(j). At ordinate zero the weight is zero. "
                    + "The same sparse inclusive cutoff count implies that the harmonic mass "
                    + "divided by (log T)^2 tends to zero."))),
                DescribeRole.Theorem))));
}
