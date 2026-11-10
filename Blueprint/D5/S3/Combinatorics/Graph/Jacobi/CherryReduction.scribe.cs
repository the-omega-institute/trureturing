using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class CherryReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/CherryReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local ordinary cherry in the true graph quotient", H("The local ordinary cherry in the true graph quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-cherry"),
                DeclarationHandle.Create(Prefix + "Cherry"), H("An actual terminal cherry socket"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Cherry G is a literal six-flag X socket in G whose two selected ports are paired to two distinct ordinary leaf flags. The stem joins the other selected trivalent vertex. The leaf colors may differ, and all exterior pairings, loops and parallel edges remain unrestricted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cherry-zero"),
                DeclarationHandle.Create(Prefix + "cherry_zero"), H("A terminal ordinary cherry is zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite flag type and every actual Cherry G, the class of G in the actual AS, IHX and ordinary CL quotient is zero. In the corresponding I branch the two ordinary legs are consecutive. CL exchanges their colors. A concrete flag permutation swaps the two central flags, the two leaf ports and their leaf mates; it identifies the exchanged I graph with the H graph after reversal of both local trivalent rotors. The two AS signs multiply to plus one, so I equals H, and the literal I minus H plus X relation kills X. No assumption of compatibility with an abstract normalization map is used."))), DescribeRole.Theorem))));
}
