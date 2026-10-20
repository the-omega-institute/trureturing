using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DeformedJucysMurphySurgeryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native surgery supplies the exact internal and ordered external occurrence counts.",
        H("Native Matching Surgery and Ordered Joins"),
        Blocks(Paragraph(Text("This source owns the actual conjugation surgery used by the canonical "
            + "native row. An opposite-charge internal choice preserves the complete partition. "
            + "A choice in distinct components joins their actual identity-edge sets, preserving all "
            + "untouched components. Counting uses the finite component partition before mapping "
            + "component cardinalities into the part multiset. Thus components with equal sizes "
            + "remain distinct occurrences, and every ordered join erases two actual occurrences. "
            + "The internal count is the sum of choose(r,2); the external coefficient is (1+b)/2 "
            + "times the ordered r*s sum. These results are live inputs to the Row and Cuts owners. "
            + "The public native-row statement and its complete occurrence formula are described "
            + "in the canonical Row document.")))));
}
