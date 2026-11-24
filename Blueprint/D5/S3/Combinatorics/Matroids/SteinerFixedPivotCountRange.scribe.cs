using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerFixedPivotCountRangeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full range of binary switch counts at a fixed pair of Steiner pivots.",
        H("Fixed-Pair Steiner Switch Counts"),
        Blocks(Describe.Lean(
            DescribeId.Create("steiner-fixed-pivot-count-range"),
            DeclarationHandle.Create(Module + ".labelledFixedPivotCountRange"),
            H("Each selected four-point component contributes four full fibres"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Extensions),
            Blocks(
                Paragraph(Text("Take a finite Steiner loop with trivial centre, two distinct nonidentity pivots, the graph of their left translations, and a finite binary vector space A. Let b count quotient vertices failing to return after two rounds of the pivot composite. Let s count four-point components other than the component containing the identity.")),
                Paragraph(Text("Among normalized binary extensions and their compatible labelled complete triple systems, the attainable counts are exactly |A|(b+4k), for 0≤k≤s. When A is trivial, only k=0 is available. The deletion and retained pivot have labels (p,0) and (q,0), and the matching is the actual matching of uncovered pairs.")),
                Paragraph(Text("A four-point component closes in two rounds of the composite. Its lift contributes either no starts or the full fibre at each of the four vertices. The identity component always returns with zero shift. A nonzero fibre element can be assigned to any selected set of the remaining square components using the single-pair return theorem. For any given labelling, the return is constant on a component. Counting the disjoint full fibres gives the converse."))),
            DescribeRole.Theorem))));
}
