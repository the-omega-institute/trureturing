using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SpanSumOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four affine-independent points in a common sum-one hyperplane span that hyperplane.",
        H("Affine span of a four-point sum-one family"),
        Blocks(
            Paragraph(Text("Work in the four-coordinate real space and let sumOne be the affine hyperplane whose coordinates sum to one. "
                + "If four points are affine independent and each lies in sumOne, their affine span is all of sumOne.")),
            Describe.Lean(
                DescribeId.Create("span-sum-one"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/SpanSumOne.span_sumOne"),
                H("Four independent points span the sum-one hyperplane"),
                StatementSource.FromAuthor(F.Disp(F.Id("spanSumOne"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Affine independence gives a linear basis for the four-dimensional coordinate space. "
                        + "Every point of sumOne has a unique expansion in that basis, and its coefficients sum to one because each basis point does."))),
                DescribeRole.Theorem))));
}
