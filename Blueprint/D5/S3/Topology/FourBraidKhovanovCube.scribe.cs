using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovCubeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral resolution cube of the four-braid",
        H("The integral resolution cube of the four-braid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-signed-differential"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovCube.differential"),
                H("Signed merge and split maps"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each zero-smoothing, the cube edge changes that crossing to the "
                    + "one-smoothing. The exponent of its sign counts the earlier one-smoothings. "
                    + "The signed saddle coefficients use multiplication at a merge and "
                    + "comultiplication at a split in the integral Frobenius algebra with "
                    + "basis 1 and X and relation X squared equal to zero."))),
                DescribeRole.Definition))));
}
