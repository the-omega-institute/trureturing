using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibCoherentExtensionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common-state criterion for two adjacent Fibonacci marginals with arbitrary coherences.",
        H("Coherent Fibonacci marginal extensions"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-coherent-extension"),
                DeclarationHandle.Create(Result), H("The residual endpoint marginals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The five legal Fibonacci words split into the middle singleton and the "
                    + "four occupation patterns of the two endpoints. Let b be the weight of "
                    + "the singleton and let L and R be the two observed endpoint blocks, obtained "
                    + "by restricting each edge matrix to the empty-middle subspace. Both edges "
                    + "supply the same middle-to-vacuum entry. Each edge supplies one additional "
                    + "middle-to-endpoint entry. The middle-to-double-occupation entry is free.")),
                    Paragraph(Text(
                    "A common positive semidefinite trace-one state exists exactly when b is "
                    + "nonnegative, the two endpoint block traces both equal 1 - b, and there "
                    + "is a choice of the free entry for which the two residual blocks are "
                    + "positive semidefinite. For positive b the residuals subtract the "
                    + "respective endpoint marginals of the outer product of the conjugated "
                    + "middle row divided by b. At b = 0 the entire row coupling must vanish "
                    + "and the endpoint blocks themselves are the residuals.")),
                    Paragraph(Text(
                    "The scalar Schur complement gives the necessity of the residual conditions. "
                    + "Their traces agree by trace preservation. If their trace is positive, "
                    + "their tensor product divided by that trace gives a joint positive "
                    + "residual on the endpoints. At trace zero the residual blocks are zero. "
                    + "Restoring the outer product contribution and the middle singleton "
                    + "gives the required common state."))),
                DescribeRole.Theorem))));
}
