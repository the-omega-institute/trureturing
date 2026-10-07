using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HyperedgeCutDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HyperedgeCutDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hereditary cut bounds charge three distinct representatives more strongly than two, through a multigraph of parallel edges and triangles.",
        H("Density from Pairs and Triangles"),
        Blocks(
            Paragraph(Text(
                "Let V be a finite vertex set and E a finite set of indexed edges, with two distinct "
                + "endpoints l(e) and r(e) for every edge. Parallel edges retain their different indices. "
                + "TwoCutCap means that for every S contained in V and every L contained in S, the "
                + "number of edges with one endpoint in L and the other in S minus L is at most 2|S|. "
                + "The bound is required on every induced vertex set, not only on cuts of V.")),
            Describe.Lean(DescribeId.Create("scaled-cut-density"),
                DeclarationHandle.Create(Prefix + "two_cut_density"),
                H("A Multigraph Bound with Cut Capacity Two"),
                StatementSource.FromAuthor(GraphFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every endpoint lies in V and TwoCutCap holds, then 2|E| is at most 7|V|. "
                    + "Averaging cuts gives fewer than 4|S| internal edges on every nonempty S. "
                    + "The degree sum therefore yields a vertex of degree at most seven. Deleting "
                    + "and restoring such vertices constructs an eight-coloring. Regard its colors "
                    + "as three-bit vectors and take the seven cuts given by nonzero binary linear "
                    + "forms. Each edge crosses exactly four cuts, while each cut contains at most "
                    + "2|V| edges. Summing gives 4|E| at most 14|V|."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the owner bound, let I be a finite set of indexed owners, let large assign a "
                + "Boolean flag to each owner, and choose representatives a(i), b(i), c(i) in V. "
                + "Always require a(i) different from b(i). A flagged owner must have all three "
                + "representatives distinct. For an unflagged owner, c(i) need not be distinct and "
                + "may equal a(i). Let T be the flagged owners. A representative set hits a cut "
                + "when its intersection with S meets both L and S minus L. The hereditary owner "
                + "condition bounds the number of hitting owners by |S| for every S contained in V "
                + "and every L contained in S. Owners count once, regardless of how many of their "
                + "representatives cross the cut.")),
            Describe.Lean(DescribeId.Create("mixed-owner-density"),
                DeclarationHandle.Create(Prefix + "mixed_owner_density"),
                H("The Additional Cost of a Third Representative"),
                StatementSource.FromAuthor(OwnerFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the stated distinctness, containment and hereditary owner conditions, "
                    + "4|I| plus 2|T| is at most 7|V|. Give each unflagged owner two indexed parallel "
                    + "edges joining a(i) and b(i), and each flagged owner the triangle on its three "
                    + "representatives. An owner contributes at most two crossing edges to any "
                    + "induced cut, and contributes none unless its representative set hits the cut. "
                    + "The resulting graph therefore satisfies TwoCutCap and has exactly 2|I|+|T| "
                    + "edges. Apply the preceding graph bound. Empty owner and vertex sets are "
                    + "included. If representatives are selected from larger supports, the owner "
                    + "condition follows from the corresponding cut bound on those supports; this "
                    + "requires containment of each representative in its own support."))),
                DescribeRole.Theorem))));

    private static Formula GraphFormula() => Disp(All("V", Call("Finset", F.Id("Vertex")),
        All("E", Call("Finset", F.Id("Edge")), All("l", Call("Function", F.Id("Edge"), F.Id("Vertex")),
        All("r", Call("Function", F.Id("Edge"), F.Id("Vertex")),
            Implies(And(Call("DistinctEndpoints", F.Id("E"), F.Id("l"), F.Id("r")),
                And(Call("EndpointsIn", F.Id("V"), F.Id("E"), F.Id("l"), F.Id("r")),
                    Call("TwoCutCap", F.Id("V"), F.Id("E"), F.Id("l"), F.Id("r")))),
                Le(Mul(D(2), Call("card", F.Id("E"))), Mul(D(7), Call("card", F.Id("V"))))))))));

    private static Formula OwnerFormula() => Disp(All("V", Call("Finset", F.Id("Vertex")),
        All("I", Call("Finset", F.Id("Owner")),
        All("large", Call("Function", F.Id("Owner"), F.Id("Bool")),
        All("a", Call("Function", F.Id("Owner"), F.Id("Vertex")),
        All("b", Call("Function", F.Id("Owner"), F.Id("Vertex")),
        All("c", Call("Function", F.Id("Owner"), F.Id("Vertex")),
            Implies(And(Call("DistinctPairs", F.Id("I"), F.Id("a"), F.Id("b")),
                And(Call("DistinctThirdWhenFlagged", F.Id("I"), F.Id("large"), F.Id("a"), F.Id("b"), F.Id("c")),
                And(Call("RepresentativesIn", F.Id("V"), F.Id("I"), F.Id("a"), F.Id("b"), F.Id("c")),
                    Call("HereditaryOwnerCutBound", F.Id("V"), F.Id("I"), F.Id("a"), F.Id("b"), F.Id("c"))))),
                Le(Add(Mul(D(4), Call("card", F.Id("I"))),
                    Mul(D(2), Call("card", Call("FlaggedOwners", F.Id("I"), F.Id("large"))))),
                    Mul(D(7), Call("card", F.Id("V"))))))))))));

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula l, Formula r) =>
        new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
}
