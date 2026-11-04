using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class BanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak SecondPeakHighD: Banks", H("Banks"),
        Blocks(Paragraph(Text("The four banks use actual natural label offsets and retain equal-valued occurrences as different labels. Their inventory is a permutation of the complete original range. Nested masks split the same physical stock and exact dyadic masses determine both source rows."))), []));
}
