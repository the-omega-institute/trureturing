using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphUnionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A marked edge-labeling avoiding every incident additive triple makes the cubic graph additively rigid.",
        H("Avoiding all local collisions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubicargraphunion-argraph_of_bad_sum_lt"),
                DeclarationHandle.Create(Prefix + "arGraph_of_bad_sum_lt"),
                H("A finite union bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the total cardinality of the bad vertex events is smaller than the marked sample space, one labeling avoids them all."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubicargraphunion-sum_bad_card_lt"),
                DeclarationHandle.Create(Prefix + "sum_bad_card_lt"),
                H("Strict factorial margin"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For at least twelve edges, the common marked endpoint, the two other marked endpoints, and the remaining vertices together have total bad-event bound below the sample-space factorial."))),
                DescribeRole.Theorem))));
}
