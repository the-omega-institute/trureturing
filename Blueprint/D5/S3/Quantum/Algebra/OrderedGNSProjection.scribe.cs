using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OrderedGNSProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful matrix states detect positivity through internal compressions of a star-subalgebra.",
        H("Ordered GNS Projections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("internal-compressions-detect-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrderedGNSProjection.positive_of_internal_compressions"),
                H("Internal compressions detect positivity"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an arbitrary positive definite complex matrix rho and a unital star-subalgebra A. "
                        + "A Hermitian matrix y in A is positive semidefinite if every compression q-star y q, "
                        + "with q in A, has nonnegative real rho-weighted trace.")),
                    Paragraph(Text(
                        "Continuous functional calculus keeps the square root of the negative part of y in A. "
                        + "Its compression is the negative of the square of that negative part. "
                        + "Faithfulness of the weighted matrix inner product forces the negative part to vanish."))),
                DescribeRole.Theorem))));
}
