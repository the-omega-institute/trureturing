using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiNullReferencePenaltyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/UmegakiNullReferencePenalty.";
    private static readonly LibraryNoteRef Skew =
        LibraryNoteRef.Create("D5/L/Divergence/audenaert2014skew");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp spectral lower bound for the trace-log pairing of a positive reference increment.",
        H("The trace-log cost of a reference increment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-increment-lower-bound"),
                DeclarationHandle.Create(Prefix + "log_increment_ge"),
                H("Lower bound from a positive reference floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Skew),
                Blocks(Paragraph(Text(
                    "Assume u > 0, λ > 0, e ≥ 0, A ≥ uC, and C ≥ λI in the Löwner order. "
                    + "Let ρ be positive semidefinite with trace one. The unnormalized real trace pairing "
                    + "Re Tr[A(log(C + eρ) − log C)] is at least uλ log(1 + e/λ). The reference C "
                    + "can have arbitrary trace subject to these hypotheses, and C + eρ has trace Tr C + e. "
                    + "The decrease in relative entropy with the unequal-trace correction equals this pairing "
                    + "minus e. The proof uses Audenaert's derivative along the affine reference path "
                    + "and operator monotonicity of the matrix logarithm after pairing with a positive weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-increment-attainment"),
                DeclarationHandle.Create(Prefix + "log_increment_eq_of_eigenvector"),
                H("Attainment at a unit eigenvector at the floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume λ > 0, C ≥ λI and e ≥ 0. If v†v = 1 and Cv = λv, then ρ = vv† "
                    + "is positive semidefinite with trace one. For A = uC, the pairing equals "
                    + "uλ log(1 + e/λ) for every real u, attaining the lower bound when u > 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-floor-obstruction"),
                DeclarationHandle.Create(Prefix + "not_floor_of_log_increment_le"),
                H("A small loss restricts the positive reference floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume u > 0, e > 0, A ≥ uC, and that ρ is positive semidefinite with trace one. "
                    + "For a threshold θ > 0, a pairing at most uθ log(1 + e/θ) rules out C ≥ λI "
                    + "for every λ > θ, since λ log(1 + e/λ) increases strictly on λ > 0. "
                    + "In an application with likelihood classes, eρ can represent reference mass added "
                    + "for a zero-likelihood class. The estimate controls the trace-log cost of that addition "
                    + "when comparing it with compression of the positive-likelihood classes."))),
                DescribeRole.Theorem))));
}
