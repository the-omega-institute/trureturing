using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail;
internal sealed class SelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer selection for the dyadic regimes", H("Paired source arithmetic"),
        Blocks(
            Paragraph(Text("The low ratios q=4 and q=8 use exact signed dyadic residues. For large a the residue representative determines v and m; exponent orthant inequalities justify the polynomial residual bounds. For the remaining a values, classes modulo 2a express z as a fixed dyadic power plus (2^a+1)T with T a nonnegative integer.")),
            Paragraph(Text("Every periodic expression is an exact polynomial identity on the unbounded nonnegative parameter T. The fixed values of a partition the original domain together with the large-a branches. The three explicit exceptional words are excluded only from this internal selector and are supplied separately at the physical endpoint."))), []));
}
