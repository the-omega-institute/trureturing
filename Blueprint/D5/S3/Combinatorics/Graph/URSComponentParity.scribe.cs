using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class URSComponentParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/URSComponentParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/iurlano2026pairwise");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fix one indexed array of 2n permutation rows on n columns and n symbols. Fibres and joint counts refer to this same array and its original row indices. For odd n at least three, fibre size two and equality of reflected joint counts force its fibre graph to be connected. The conclusion also applies to arrays whose first row is the identity and whose rows are sorted on their original labels.",
        H("Component parity of uniform reflection arrays"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibre"),
                DeclarationHandle.Create(Prefix + "fibre"),
                H("Actual column-symbol fibres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a column x and symbol p, the fibre F(x,p) consists of precisely the row indices i for which the permutation in row i sends x to p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pair-count"),
                DeclarationHandle.Create(Prefix + "pairCount"),
                H("Actual joint counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The count f(x,y;p,q) is the number of actual row indices i sending x to p and y to q simultaneously, as in Definition 3 of the source. All counts use the same row family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibre-graph"),
                DeclarationHandle.Create(Prefix + "fibreGraph"),
                H("The graph on original row indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Distinct row indices i and j are adjacent precisely when some column has the same symbol in both rows. Under the fibre-size-two hypothesis these are exactly the pairs making up the actual fibres."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibre-graph-connected"),
                DeclarationHandle.Create(Prefix + "fibre_graph_connected"),
                H("Odd order forces connectivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The source domain is URS(n,2,1), abbreviated URS(n,2), in Definition 4, with reflection symmetry from Definition 3. Definition 2 restricts to reduced arrays by requiring an identity first row and lexicographic row order. The repository-derived connectivity theorem applies to the full domain without these reduction conditions.")),
                    Paragraph(Text("For every odd n at least three and every indexed family of 2n permutations on Fin n, assume each column-symbol fibre has exactly two row indices and f(x,y;p,q)=f(x,y;q,p) whenever x and y are distinct columns and p and q are distinct symbols. Then the actual fibre graph is connected. Identity-first and lexicographic sorting conditions are unnecessary for this conclusion.")),
                    Paragraph(Text("A proper set S closed under fibre edges has size 2s, with exactly s occupied symbols in every column. An actual row i outside S defines a graph on the columns: x is adjacent to y when the symbol in row i at y is occupied by S at x. Reflection supplies an actual row with the two outside-row symbols exchanged, which proves symmetry of this graph. Its diagonal is empty and every degree is s. The handshaking lemma on the odd column set forces s even, so four divides the size of S. If the fibre graph were disconnected, one component and its complement would both have size divisible by four, contradicting the oddness of n."))),
                DescribeRole.Theorem)),
        []));
}
