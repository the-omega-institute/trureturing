using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FiniteModuleProductCancellationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/FiniteModuleProductCancellation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cancelling a common finite module.",
        H("Finite Module Product Cancellation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prod-cancel"),
                DeclarationHandle.Create(Module + ".finite_prod_cancel"),
                H("Cancelling a common finite module"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count the linear maps from each finite source to the two products. The common factor cancels in the cardinal counts. Decompose maps by their kernels, then induct on the source size to recover the counts of injective maps. An injection between the remaining factors is bijective because they have the same finite cardinality."))),
                DescribeRole.Theorem))));
}
