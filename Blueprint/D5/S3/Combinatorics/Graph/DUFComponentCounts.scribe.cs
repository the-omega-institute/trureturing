using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFComponentCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFComponentCounts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of subsets of an n-element vertex type, m=card(H), and P=binom(n,2). The side predicate is defined for every H. Under DUF and the cap of at most four neighbors per ground pair, each four-edge fiber F(S) with card(S)=4 determines one center/support component, and each counted component has exactly two sides.",
        H("The component correction identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blockside"),
                DeclarationHandle.Create(Prefix + "blockSide"),
                H("One side of a block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S is a side of (c,U) when some opposite four-set A forms a complete block (c,A,S) in H and U=A union S. The underlying block identity is (c,U); under the cap, it identifies a link component."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reciprocal-count"),
                DeclarationHandle.Create(Prefix + "reciprocal_count"),
                H("Two fibers per component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For DUF H with the cap, b=2B. The proof counts actual side-component incidences in both directions. Exact neighborhoods show that any two bipartitions of one support have the same two sides up to interchange."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("component-counting"),
                DeclarationHandle.Create(Prefix + "component_counting"),
                H("The full counting identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a three-uniform DUF family of maximum pair codegree at most four, q4+a=h4+4B and 8B<=h4. Moreover 6m+a+q2+2q1+3q0+h1+3h0=6P+4B, while 21m+10h0+3h1+h3<=22P. If m>P, integrality forces B>=2 and h4>=16. No global charging inequality or unrestricted-codegree conclusion is asserted."))),
                DescribeRole.Theorem)),
        []));
}
