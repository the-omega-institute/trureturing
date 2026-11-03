using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class TableDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact paired row bounds and finite row type", H("Exact paired row bounds and finite row type"),
        Blocks(
            Paragraph(Text("FixedRow stores natural x,p,q,h,v,m,M and the actual Bool before. rowBounds is an integer proposition. For each of the first three endpoints it requires the old endpoint in [0,old head-1] and the enlarged endpoint in [0,new head-1]. It also requires 1<=v, 2v<=t, 0<=M and 2M<=y-2.")),
            Paragraph(Text("This module contains only the shared row type and predicate. The small-p tables are defined in SmallTables. The selector therefore returns original simultaneous old and new constraints with their stocks."))), []));
}
