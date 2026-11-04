using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class ActualBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical block inventories and reserve bounds",
        H("Occurrences, masses and every prefix"),
        Blocks(Paragraph(Text("The nested binary masks partition each of the four original physical chains. masked_inventory proves a permutation of the complete natural label range, including its four negative endpoints. No quotient identifies occurrences carrying the same numerical source value. masked_weighted_masses sums the selected physical occurrences using the decoder and split permutations. The effective reserves are S1=A*u1-2*e1*v0, S2=A*u2+2*e1*v2 and S3=A*u3+2*e1*v3+2*e2*w. The four shadow block sums are B+e1-A-S1, B+e2-2*e1+S1-S2, B+e3-2*e2+S2-S3 and B-2*e3+S3.")),
            Paragraph(Text("actual_word_totals identifies the actual centered old total as zero and the total charge as A for every complete physical inventory. actual_chain_masses derives the four complete shadow masses from Source.source_shadow_charge. For generic source functions f and q, four_reserve_strong combines nonnegative positive-step values, nonnegative charge and shadow, the four negative shadow values, the selected shadow masses and exact final totals. At the first three negative endpoints the remaining charges are retained exactly in the upper reserve conditions. This proves 0<=h<=B-1 and 0<=h+Q<=B at every prefix, including the empty and complete prefixes."))), []));
}
