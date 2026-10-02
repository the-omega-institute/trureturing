using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SimplexCoverageHessianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected nonnegative normalized finite matrix is nonpositive transverse to its positive fixed vector.",
        H("Connected Hessian Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simplex-coverage-connected-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Resource/SimplexCoverageHessian.quadratic_nonpos_of_connected_normalization"),
                H("Transverse nonpositivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is finite and nonempty. The real matrix is symmetric and entrywise "
                        + "nonnegative, its fixed vector is strictly positive, every nonempty proper cut "
                        + "has a positive crossing entry, and every vector satisfies z^T S z <= z^T S^2 z. "
                        + "Every vector perpendicular to the fixed vector then has nonpositive quadratic form.")),
                    Paragraph(Text(
                        "The proof combines a maximum-ratio bound with a Hermitian eigenbasis. "
                        + "The singleton cut condition is vacuous; an empty carrier cannot invoke this theorem. "
                        + "This is a dependency of the full simplex coverage optimizer development in #11799, "
                        + "not an independent open-problem settlement. The represented higher-degree normalized "
                        + "Hessian consumer, concavity and actual expected-time optimizer remain unproved."))),
                DescribeRole.Theorem)),
        []));
}
