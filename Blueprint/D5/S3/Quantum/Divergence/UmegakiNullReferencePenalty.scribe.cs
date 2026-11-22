using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiNullReferencePenaltyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.";
    private static readonly LibraryNoteRef Skew =
        LibraryNoteRef.Create("D5/L/Divergence/audenaert2014skew");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp spectral lower bound on the cost of adding a zero-likelihood class to a reference state.",
        H("The relative entropy cost of a reference increment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-increment-lower-bound"),
                DeclarationHandle.Create(Prefix + "log_increment_ge"),
                H("Lower bound from the smallest reference eigenvalue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Skew),
                Blocks(Paragraph(Text(
                    "The comparison dominates u times the positive reference C, and C has spectral floor "
                    + "lambda. Adding a trace-one positive density with weight e to the reference decreases "
                    + "the trace-log relative entropy of the fixed comparison by at least "
                    + "u times lambda times log(1 + e/lambda). The proof differentiates the logarithm along "
                    + "the affine reference path, compares the comparison to a positive multiple of the "
                    + "current reference, and uses the trace identity for the resolvent derivative. "
                    + "Audenaert's logarithm calculation supplies the analytic prerequisite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-increment-attainment"),
                DeclarationHandle.Create(Prefix + "log_increment_eq_of_eigenvector"),
                H("Attainment at a lowest eigenvector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the comparison is proportional to C, placing the added density on a "
                    + "lambda eigenvector attains the lower bound. The spectral calculation follows "
                    + "the shared eigenvector along the affine reference path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-floor-obstruction"),
                DeclarationHandle.Create(Prefix + "not_floor_of_log_increment_le"),
                H("A small loss restricts the positive reference floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function lambda times log(1 + e/lambda) increases strictly for positive e. "
                    + "An observed loss at or below the bound for a given floor excludes every larger "
                    + "floor. This gives the spectral estimate used to compare compression of the "
                    + "positive-likelihood classes against the loss incurred by the zero class."))),
                DescribeRole.Theorem))));
}
