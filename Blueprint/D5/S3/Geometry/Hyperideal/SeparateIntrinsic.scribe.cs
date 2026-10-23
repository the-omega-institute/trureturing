using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SeparateIntrinsicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite linear support signs separate the intrinsic interiors of two convex sets.",
        H("Intrinsic interiors separated by opposite supports"),
        Blocks(
            Paragraph(Text("Let s and t be sets in the four-coordinate real space and let L be a real linear functional. "
                + "If L is nonpositive on s, nonnegative on t, and is strictly negative somewhere in s, "
                + "then the intrinsic interiors of s and t are disjoint.")),
            Describe.Lean(
                DescribeId.Create("separate-intrinsic"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/SeparateIntrinsic.separate_intrinsic"),
                H("Opposite support signs exclude a common intrinsic-interior point"),
                StatementSource.FromAuthor(F.Disp(F.Id("separateIntrinsic"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a hypothetical common interior point, linearity forces the support value to be zero. "
                        + "Intrinsic interior permits a positive extension away from any chosen point of s while staying in s. "
                        + "The strict negative witness then makes the extended support value positive, contradicting the nonpositive bound."))),
                DescribeRole.Theorem))));
}
