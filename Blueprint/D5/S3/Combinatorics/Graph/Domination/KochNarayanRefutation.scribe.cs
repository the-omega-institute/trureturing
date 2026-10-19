using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class KochNarayanRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kochnarayan2025uniquedomination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A graph with fourteen vertices, twenty-eight edges and a unique minimum dominating set of size four exceeds the printed bound twenty-six.",
        H("The Koch-Narayan bipartite edge bound is false"),
        Blocks(
            Node("halfCeil", "Exact ceiling", DescribeRole.Definition,
                "halfCeil(k) is the integer ceiling of the rational number k/2. Division is exact before rounding."),
            Node("halfFloor", "Exact floor", DescribeRole.Definition,
                "halfFloor(k) is the integer floor of the rational number k/2."),
            Node("phi", "The printed positive part", DescribeRole.Definition,
                "With a=ceil(gamma/2) and b=floor(gamma/2), Phi=max(0,n-3gamma-2a-b+1). Every subtraction is in the integers. In particular Phi(14,4)=0; left-associated truncated natural subtraction would change the formula."),
            Node("bound", "The exact printed edge bound", DescribeRole.Definition,
                "The bound is 2gamma+2ab+min(n-3gamma,2a-b+1)(2a+1), plus the sum of (2a+1)+ceil(i/2) over the inclusive integer interval 1 through Phi. An empty interval contributes zero. Both the minimum and the signed arithmetic are exactly those printed in Conjecture 1."),
            Node("claim", "Conjecture 1 on its whole domain", DescribeRole.Definition,
                "Koch and Narayan, arXiv:2511.01719v1, Conjecture 1, assert this bound for every finite simple bipartite graph without isolated vertices, with a unique minimum dominating set, gamma at least two and n at least three gamma. The vertex type is arbitrary; n is its Fintype cardinality. The graph is an actual SimpleGraph and its size is edgeFinset.card, counting unordered edges once. IsDominating, IsNDominatingSet and dominationNumber are the existing native definitions. Uniqueness quantifies over every Set V attaining dominationNumber. On a finite type, the proof identifies attainment with minimum cardinality among all dominating sets using native minimum attainment, the native domination upper bound and the Set/Finset membership and cardinality equalities. There is no connectedness, minimum-degree-two, balanced-center or constructed-family assumption."),
            Node("forward", "The oriented edges", DescribeRole.Definition,
                "The parts are {0,...,6} and {7,...,13}. Join 0 to 10,11,12,13; join 7 to 1,2, join 8 to 3,4 and join 9 to 5,6; join each of 1,...,6 to each of 10,12,13. These disjoint families have four, six and eighteen edges. forward orients each edge from the first part to the second."),
            Node("graph", "The fourteen-vertex graph", DescribeRole.Definition,
                "Adjacency is forward in either direction. The disjoint parts exclude loops and reversal gives symmetry. Every edge crosses the parts, every vertex has a neighbor, and the actual edgeFinset has cardinality twenty-eight."),
            Node("centers", "The unique minimum dominating set", DescribeRole.Definition,
                "The centers are {0,7,8,9}. Their closed neighborhoods are {0,10,11,12,13}, {7,1,2}, {8,3,4} and {9,5,6}. They partition the graph. Any dominating set meets every block to dominate its center, so the image under the block map has cardinality four and the set has at least four members. The centers themselves dominate, and native attainment therefore gives dominationNumber=4."),
            Node("result", "The whole conjecture is false", DescribeRole.Theorem,
                "A dominating set of size four has exactly one member in each block: equality of the block-image cardinality makes the block map injective on the set. Leaf 11 forces the first choice into {0,11}, so hubs 10,12,13 are absent. If a noncenter is chosen in any other block, its partner has no selected neighbor; hence 7,8,9 must all be chosen and 1,...,6 are absent. The choice 11 would leave 10 undominated, forcing 0 as well. Thus every minimum set equals the centers. Finite Set/Finset conversion preserves domination, membership, cardinality and equality, giving uniqueness over all sets. Substituting n=14, gamma=4 gives a=b=2, Phi=0 and bound 8+8+min(2,3)*5=26, contradicting 28 edges. The printed Phi differs from the residual count suggested by construction Case 3, max(0,n-3gamma-2a+b-1); both are zero here, and Case 2 also gives 26. This proves no true extremal formula and settles neither an unspecified corrected conjecture nor the unrestricted predecessor problem. The elementary private-neighbor mechanism is also used in the source; the imported domination port retains its formal-conjectures Apache-2.0 attribution.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("koch-narayan-2025-bipartite-unique-domination-edge-bound"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string selector, string title, DescribeRole role,
        string prose, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("kochnarayan-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(Presentation(selector)),
            selector is "halfCeil" or "halfFloor" or "phi" or "bound" or "claim"
                ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eqf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leqf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Ifff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Some(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static Formula Mem(Formula x, params Formula[] values) =>
        new Formula.Relation(x, FormulaRelationOperator.MemberOf, new Formula.SetLiteral([.. values]));

    private static Formula Presentation(string selector)
    {
        Formula k = F.Id("k"), n = F.Id("n"), gamma = F.Id("gamma");
        Formula u = F.Id("u"), v = F.Id("v"), i = F.Id("i");
        Formula a = Call("halfCeil", gamma), b = Call("halfFloor", gamma);
        Formula factor = Add(Mul(D(2), a), D(1));
        Formula signed = Add(Sub(Sub(Sub(n, Mul(D(3), gamma)), Mul(D(2), a)), b), D(1));
        Formula forward = Or(And(Eqf(u, D(0)), Mem(v, D(1, 0), D(1, 1), D(1, 2), D(1, 3))),
            Or(And(Mem(u, D(1), D(2)), Eqf(v, D(7))),
            Or(And(Mem(u, D(3), D(4)), Eqf(v, D(8))),
            Or(And(Mem(u, D(5), D(6)), Eqf(v, D(9))),
                And(And(Leqf(D(1), u), Leqf(u, D(6))), Mem(v, D(1, 0), D(1, 2), D(1, 3)))))));
        return Disp(selector switch
        {
            "halfCeil" => Eqf(Call("halfCeil", k), Call("ceil", new Formula.Fraction(k, D(2)))),
            "halfFloor" => Eqf(Call("halfFloor", k), new Formula.Floor(new Formula.Fraction(k, D(2)))),
            "phi" => Eqf(Call("phi", n, gamma), Call("max", D(0), signed)),
            "bound" => Eqf(Call("bound", n, gamma), Add(Add(Add(Mul(D(2), gamma), Mul(Mul(D(2), a), b)),
                Mul(Call("min", Sub(n, Mul(D(3), gamma)), Add(Sub(Mul(D(2), a), b), D(1))), factor)),
                Seq(Sum, Underscore, Grp(Eqf(i, D(1))), Caret, Grp(Call("phi", n, gamma)),
                    Grp(Add(factor, Call("ceil", new Formula.Fraction(i, D(2)))))))),
            "claim" => ClaimPresentation(),
            "forward" => Ifff(Call("forward", u, v), forward),
            "graph" => Ifff(Call("Adj", F.Id("graph"), u, v),
                Or(Call("forward", u, v), Call("forward", v, u))),
            "centers" => Eqf(F.Id("centers"), new Formula.SetLiteral([D(0), D(7), D(8), D(9)])),
            "result" => new Formula.Not(F.Id("claim")),
            _ => throw new System.ArgumentOutOfRangeException(nameof(selector))
        });
    }

    private static Formula ClaimPresentation()
    {
        Formula v = F.Id("V"), g = F.Id("G"), d = F.Id("D"), s = F.Id("S");
        Formula gamma = Call("dominationNumber", g), order = Call("card", v);
        Formula Attains(Formula x) => And(Call("IsDominating", g, x), Eqf(Call("ncard", x), gamma));
        Formula unique = Some("D", Call("Set", v), And(Attains(d),
            All("S", Call("Set", v), Imp(Attains(s), Eqf(s, d)))));
        Formula hypotheses = And(Call("IsBipartite", g),
            And(All("v", v, new Formula.Not(Call("IsIsolated", g, F.Id("v")))),
            And(unique, And(Leqf(D(2), gamma), Leqf(Mul(D(3), gamma), order)))));
        return Ifff(F.Id("claim"), All("V", F.Id("Type"),
            All("finite", Call("Fintype", v), All("G", Call("SimpleGraph", v),
                Imp(hypotheses, Leqf(Call("card", Call("edgeFinset", g)), Call("bound", order, gamma)))))));
    }
}
