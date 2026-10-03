using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class TianDokyeesunKlavzarOuterGeneralPositionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/TianDokyeesunKlavzarOuterGeneralPositionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/tiandokyeesunklavzar2025removal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induced vertex deletion can raise the outer general position number by more than the deleted degree.",
        H("The outer general position vertex-removal bound is false"),
        Blocks(
            Node("vertex-deletion", "Actual induced vertex deletion", "vertexDelete", DeleteFormula(),
                "The vertex carrier consists of precisely the vertices other than x. "
                    + "Adjacency is inherited from Q, so this is the actual graph Q-x.",
                DescribeRole.Definition),
            Node("non-cut", "Non-cut by component count", "NonCut", NonCutFormula(),
                "A vertex is non-cut when its deletion does not increase the number of connected "
                    + "components. The empty graph has zero components. Hence the sole vertex "
                    + "of K1 is non-cut under this convention.", DescribeRole.Definition, fromRepo: true),
            Node("outer-position", "All shortest paths avoid selected internal vertices", "OuterPosition",
                OuterFormula(),
                "For a selected first endpoint and any other endpoint, every shortest path excludes "
                    + "each selected vertex distinct from both endpoints. A shortest path is a native graph walk "
                    + "satisfying IsPath and having length equal to the distance. Reversal accounts for either "
                    + "endpoint being selected. This includes pairs within S and pairs from S to its "
                    + "complement, as in the source definition.", DescribeRole.Definition),
            Node("outer-number", "Maximum outer general position cardinality", "outerNumber",
                NumberFormula(),
                "The finite supremum ranges over every finite subset of the vertex carrier satisfying "
                    + "OuterPosition. It is the largest such cardinality; the empty set is included. "
                    + "The empty graph therefore has outer number zero, and K1 has outer number one.",
                DescribeRole.Definition),
            Node("source-conjecture", "The full finite Conjecture 3.4", "claim", ClaimFormula(),
                "Conjecture 3.4 in section 3.2 of arXiv:2510.01294v2 states: "
                    + "If x is not a cut vertex of a graph G, then gp_o(G-x) <= gp_o(G) + deg_G(x). "
                    + "The formal statement uses Q for the source's G. For every finite vertex type, "
                    + "every simple connected graph Q, and every non-cut "
                    + "vertex x, Conjecture 3.4 proposes the displayed inequality. The degree is the "
                    + "native graph degree, counting the neighbors of x. No restriction to a graph "
                    + "family or to a particular selected set is imposed.", DescribeRole.Definition),
            Node("refutation", "A 19-vertex counterexample", "result", Disp(new Formula.Not(F.Id("claim"))),
                "Start from a twelve-cycle and replace opposite vertices by independent sets A and B "
                    + "of four vertices each, retaining their cycle neighbors. The resulting H has "
                    + "18 vertices. Add x adjacent to one cycle neighbor of A and the corresponding "
                    + "cycle neighbor of B, so G has 19 vertices. Both G and the actual deletion G-x "
                    + "are connected, and x has degree two. The set A union B has size eight and is "
                    + "outer general position in G-x. A five-color assignment in G gives a shortest-path "
                    + "obstruction for every distinct pair of equal color. Every outer general position "
                    + "set is therefore injectively colored and has size at most five. Exact edge "
                    + "certificates construct descending walks and bound the length of every walk, "
                    + "establishing the native distances. A graph isomorphism transfers the eight-vertex "
                    + "set to the actual induced deletion. Thus the proposed inequality would imply "
                    + "8 <= 5+2, a contradiction. The simplicial-vertex bound and conditional lower "
                    + "bound stated separately in the source are not settled by this result.",
                DescribeRole.Theorem, fromRepo: true,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tian-dokyeesun-klavzar-conjecture34-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, bool fromRepo = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            fromRepo ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DeleteFormula()
    {
        var v = F.Id("V"); var q = F.Id("Q"); var x = F.Id("x");
        return Disp(All("V", Type(), All("Q", Call("SimpleGraph", v), All("x", v,
            Eq(Call("vertexDelete", q, x),
                Call("induce", q, Call("compl", Call("singleton", x))))))));
    }

    private static Formula NonCutFormula()
    {
        var v = F.Id("V"); var q = F.Id("Q"); var x = F.Id("x");
        return Disp(All("V", Type(), All("Q", Call("SimpleGraph", v), All("x", v,
            IffFormula(Call("NonCut", q, x), LeFormula(
                NatCard(Call("ConnectedComponent", Call("vertexDelete", q, x))),
                NatCard(Call("ConnectedComponent", q))))))));
    }

    private static Formula OuterFormula()
    {
        var vtype = F.Id("V"); var q = F.Id("Q"); var s = F.Id("S");
        var u = F.Id("u"); var v = F.Id("v"); var p = F.Id("p"); var w = F.Id("w");
        var neq = AndFormula(new Formula.Relation(w, FormulaRelationOperator.NotEqual, u),
            new Formula.Relation(w, FormulaRelationOperator.NotEqual, v));
        var free = All("w", vtype, ImpliesFormula(AndFormula(Member(w, s), neq),
            new Formula.Not(Member(w, Call("support", p)))));
        var shortest = AndFormula(Call("IsPath", p),
            Eq(Call("length", p), Call("dist", q, u, v)));
        var paths = All("u", vtype, ImpliesFormula(Member(u, s), All("v", vtype,
            All("p", Call("Walk", q, u, v), ImpliesFormula(shortest, free)))));
        return Disp(All("V", Type(), All("Q", Call("SimpleGraph", vtype),
            All("S", Call("Finset", vtype), IffFormula(Call("OuterPosition", q, s), paths)))));
    }

    private static Formula NumberFormula()
    {
        var v = F.Id("V"); var q = F.Id("Q");
        var subsets = Call("filter", Call("OuterPosition", q), Call("univ", Call("Finset", v)));
        var card = Seq(Operatorname, Grp(F.Id("Finset"),
            new Formula.LatexSymbol(FormulaLatexSymbol.Period), F.Id("card")));
        var maximum = Eq(Call("outerNumber", q), Call("sup", subsets, card));
        return Disp(All("V", Type(), Seq(
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("Q", Call("SimpleGraph", v), maximum))));
    }

    private static Formula ClaimFormula()
    {
        var v = F.Id("V"); var q = F.Id("Q"); var x = F.Id("x");
        return Disp(IffFormula(F.Id("claim"), All("V", Type(), Seq(
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
                All("Q", Call("SimpleGraph", v), ImpliesFormula(Call("Connected", q),
                    All("x", v, ImpliesFormula(Call("NonCut", q, x), LeFormula(
                        Call("outerNumber", Call("vertexDelete", q, x)),
                        Seq(Call("outerNumber", q), Sp, Plus, Sp, Call("degree", q, x)))))))))));
    }

    private static Formula NatCard(Formula type) => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id("Nat"), new Formula.LatexSymbol(FormulaLatexSymbol.Period), F.Id("card"))), [type]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeFormula(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula IffFormula(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Iff, Paren(b));
    private static Formula ImpliesFormula(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Implies, Paren(b));
    private static Formula AndFormula(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.And, Paren(b));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
}
