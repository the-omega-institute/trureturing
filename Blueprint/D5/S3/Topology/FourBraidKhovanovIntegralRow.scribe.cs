using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovIntegralRowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Checked integral cohomology of the signed row", H("Checked integral cohomology of the signed row"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-contraction-sound"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovIntegralRow.sound"),
                H("Checked integral cohomology of the signed row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The boolean checks verify that all signed matrices are defined and that the "
                    + "differential squares to zero. They verify each contraction identity and yield "
                    + "the integral cohomology groups as free modules on the residual generators."))),
                DescribeRole.Theorem))));
}
