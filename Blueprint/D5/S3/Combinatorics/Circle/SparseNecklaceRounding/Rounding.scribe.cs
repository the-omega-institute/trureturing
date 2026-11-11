using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.SparseNecklaceRounding;

internal sealed class SparseNecklaceRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous rounding of local corners",
        H("Simultaneous rounding of local corners"),
        Blocks(
            Describe.Lean(DescribeId.Create("sparse-necklace-simultaneous-rounding"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Rounding.simultaneous_rounding"),
                H("Whole-label words with bounded possible corners"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let alpha be any type with decidable equality, f,g:alpha->Q, and H,N,x,y rational. A block is either one label i or a cut (i,j,t). A cut has f(i),g(i)>0, f(j),g(j)<0 and 0<t<1. Its four fractional vertices are A, A+t v, A+t v+w and A+v+w, where v=(f(i),g(i)) and w=(f(j),g(j)). Assume FractionalFits: every one-label boundary and all four cut vertices lie in the same rectangle [0,H] times [0,N], starting from (x,y). Assume the plus word has no repeated labels.")),
                    Paragraph(Text("Expand each cut as i,j for the plus word and as j,i for the minus word, leaving every one-label block unchanged. These words are permutations of each other and have exactly the same f-total and g-total. The flattened list of cut-pair labels has no repetition. Applying the literal swaps of these pairs in list order to the plus word gives exactly the minus word.")),
                    Paragraph(Text("The corner-position list has no repetition, has length equal to the number of cut pairs, and every entry is at least one and strictly less than the plus-word length. Every pair has a positive first label and a negative second label in both coordinates. Every natural plus prefix has both coordinates nonnegative; every natural minus prefix has coordinates at most H,N. At a prefix outside the corner list, the plus prefix also satisfies both upper bounds, the minus prefix also satisfies both lower bounds, and the two words have identical prefix sums in each coordinate.")),
                    Paragraph(Text("Every corner n has a specified pair (i,j): the plus word is u++[i,j]++v, the minus word is u'++[j,i]++v', and length(u)+1=n=length(u')+1. Every cut pair occurs in such adjacent positions with equal preceding lengths. For every natural m, among q:Fin(m) the number of plus prefixes exceeding H or N and the number of minus prefixes below zero are each at most the number of pairs. Actual failures may be fewer than possible corners.")),
                    Paragraph(Text("At a cut the only new plus state is A+v=(A+t v)+(1-t)v, which preserves lower bounds. The only new minus state is A+w=(A+t v+w)-t v, which preserves upper bounds. The block displacement v+w is identical in both expansions. Induction over the list therefore preserves every later boundary without accumulating errors. Distinct positions give the finite-cardinality bound. This geometric theorem retains FractionalFits as an internal hypothesis; it does not assert that a particular physical necklace supplies that hypothesis."))),
                DescribeRole.Theorem)), []));
}
