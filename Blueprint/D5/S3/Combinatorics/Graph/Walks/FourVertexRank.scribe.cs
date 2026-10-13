using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class FourVertexRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/FourVertexRank.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual perfect matchings on four vertices admit three pairings. Their supported pairs give the exact number of perfect-matching subgraphs.",
        H("Actual Perfect Matchings on Four Vertices"),
        Blocks(
            Paragraph(Text("Vertices are indexed by Fin 4, with indices 0, 1, 2, 3. The three partner maps exchange respectively the pairs 01 and 23, 02 and 13, and 03 and 12. A perfect matching is an actual SimpleGraph.Subgraph satisfying IsPerfectMatching; it includes every vertex and gives each vertex exactly one adjacent partner.")),
            Describe.Lean(DescribeId.Create("partner-maps"), DeclarationHandle.Create(Prefix + "mate"), H("Three Partner Maps"),
                StatementSource.FromAuthor(Disp(All("j", Call("Fin", D(3)), All("i", Call("Fin", D(4)),
                    Eq(Call("mate", F.Id("j"), F.Id("i")), Call("Entry", Call("PartnerTable"), F.Id("j"), F.Id("i"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("PartnerTable has rows (1,0,3,2), (2,3,0,1), and (3,2,1,0). Every row is an involution without a fixed vertex."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("perfect-matching-count"), DeclarationHandle.Create(Prefix + "pmCount"), H("Actual Perfect-Matching Count"),
                StatementSource.FromAuthor(Disp(All("H", Call("SimpleGraph", Call("Fin", D(4))),
                    Eq(Call("pmCount", F.Id("H")), Call("card", Call("PerfectMatchingSubgraphs", F.Id("H"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("PerfectMatchingSubgraphs(H) is the subtype of all subgraphs M of H with M.IsPerfectMatching. Its cardinality is Nat.card of this finite type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-matching-count"), DeclarationHandle.Create(Prefix + "actual_matching_count"), H("Exact Matching Count"),
                StatementSource.FromAuthor(MatchingStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the unique partner of vertex 0. It is 1, 2, or 3. Symmetry fixes its partner as 0. The two remaining vertices must be paired with each other, because the already paired vertices cannot acquire a second partner. Conversely, each of the three pairings gives a perfect-matching subgraph exactly when both of its edges occur in H. These constructions form a bijection, so their supported indicators sum to the actual cardinality. Each indicator is 1 when its two edges occur and 0 otherwise."))), DescribeRole.Theorem),
            Paragraph(Text("The counting formula holds for every simple graph on these four vertices. The weighted and binary adjacency rank tables, the classification up to graph isomorphism, and the signed rank difference require further arguments.")))));
    private static Formula MatchingStatement()
    {
        Formula g = F.Id("H");
        return Disp(All("H", Call("SimpleGraph", Call("Fin", D(4))), Eq(Call("pmCount", g),
            Seq(Indicator(And(Call("Adj", g, D(0), D(1)), Call("Adj", g, D(2), D(3)))), Plus,
                Indicator(And(Call("Adj", g, D(0), D(2)), Call("Adj", g, D(1), D(3)))), Plus,
                Indicator(And(Call("Adj", g, D(0), D(3)), Call("Adj", g, D(1), D(2))))))));
    }
    private static Formula Indicator(Formula p) => Call("indicator", p);
    private static Formula Call(string n, params Formula[] a) => a.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(n)) : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
}
