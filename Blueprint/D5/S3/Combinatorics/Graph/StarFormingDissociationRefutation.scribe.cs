using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class StarFormingDissociationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bipartite graph on ten vertices has a minimal two-star-forming set of size six, "
            + "but every two-independent set has size at most five.",
        H("Two-independence and upper two-star formation differ"),
        Blocks(
            Paragraph(Text("Let G be a finite simple graph on V, with decidable adjacency. "
                + "Write d(G,S,v) for the number of neighbours of v in S. All sets below "
                + "are finite vertex sets. The definitions are those of Rafik Sahbi, "
                + "Upper k-Star-Forming Sets, k-Independence, and Upper Domination, "
                + "arXiv:2610.03785v2, Definition 2.1 and Conjecture 4.2.")),
            Node("IsKIndependent", "Selected induced degree is less than k",
                Disp(Iff(Call("IsKIndependent", G, K, I),
                    All("v", V, Imp(Member(v, I), Lt(Degree(I, v), K))))),
                "Each selected vertex has fewer than k selected neighbours. For k equal "
                    + "to two, the induced graph is a disjoint union of edges and isolated vertices.",
                DescribeRole.Definition),
            Node("beta", "Maximum k-independent cardinality",
                Disp(Eq(Call("beta", G, K), Maximum("I", Independent(I)))),
                "Take the maximum cardinality over the k-independent subsets of V. "
                    + "The finite supremum has value zero if the family is empty.",
                DescribeRole.Definition),
            Node("IsStarForming", "A star containing each outside vertex",
                StarFormula(),
                "For every vertex outside S, the graph on S together with that vertex "
                    + "contains a star with k leaves containing the vertex. The centre is "
                    + "distinct from all leaves. Extra edges between leaves are allowed: "
                    + "the star is a subgraph, with no induced-subgraph requirement.",
                DescribeRole.Definition),
            Node("IsMinimalStarForming", "Inclusion-minimal star formation",
                Disp(Iff(Call("IsMinimalStarForming", G, K, S), And(Star(S),
                    All("T", Sets, Imp(Call("ProperSubset", T, S), new Formula.Not(Star(T))))))),
                "The set is star-forming and no proper subset is star-forming. "
                    + "This is inclusion-minimality rather than minimum cardinality.",
                DescribeRole.Definition),
            Node("SF", "Upper k-star-forming number",
                Disp(Eq(Call("SF", G, K), Maximum("S", Call("IsMinimalStarForming", G, K, S)))),
                "Take the maximum cardinality among all inclusion-minimal k-star-forming "
                    + "sets. The finite supremum has value zero if the family is empty.",
                DescribeRole.Definition),
            Node("LocalTwo", "Two local alternatives",
                Disp(Iff(Call("LocalTwo", G, S), LocalFormula())),
                "Every outside vertex either has two neighbours in S, or has a neighbour "
                    + "in S that itself has a neighbour in S. In the second alternative "
                    + "this further neighbour cannot be the outside vertex.",
                DescribeRole.Definition),
            Node("starForming_two_iff", "The local criterion equals the star definition",
                Disp(All("V", F.Id("Type"), All("G", Call("SimpleGraph", V),
                    All("S", Sets, Iff(Call("IsStarForming", G, D(2), S), Call("LocalTwo", G, S)))))),
                "In a two-leaf star, the outside vertex is either the centre, giving "
                    + "two neighbours in S, or a leaf, giving a centre and another leaf "
                    + "in S. Conversely, two selected neighbours give a star centred at "
                    + "the outside vertex; a selected neighbour with its own selected "
                    + "neighbour gives a star centred at that selected neighbour. The "
                    + "argument works on any vertex type with decidable equality and adjacency.",
                DescribeRole.Theorem),
            Node("claim", "Equality on all bipartite finite graphs", ClaimFormula(),
                "Conjecture 4.2 asserts equality for every bipartite finite graph. "
                    + "Graphs on Fin n cover every finite simple graph up to isomorphism. "
                    + "Bipartiteness is expressed by a proper colouring with two colours.",
                DescribeRole.Definition),
            Node("result", "The equality is false", Disp(new Formula.Not(F.Id("claim"))),
                "Use vertices 0 through 9, with sides 0 through 4 and 5 through 9. "
                    + "The neighbourhoods on the first side are {5,6,9}, {5,6,8}, "
                    + "{8,9}, {6,7,8,9}, and {5,7,8,9}, respectively. Colour by side. "
                    + "The set {0,1,2,5,6,7} satisfies the local criterion, while each "
                    + "of its 63 proper subsets fails it. It is therefore minimal "
                    + "two-star-forming, so SF is at least six. Each of the 210 "
                    + "six-element vertex sets contains a vertex with at least two "
                    + "selected neighbours. Any larger two-independent set would "
                    + "contain a two-independent six-element subset, since deletion "
                    + "cannot increase selected degrees. Thus beta is at most five "
                    + "and the asserted equality fails.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sahbi-2026-star-forming-bipartite-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula G => F.Id("G");
    private static Formula V => F.Id("V");
    private static Formula K => F.Id("k");
    private static Formula S => F.Id("S");
    private static Formula T => F.Id("T");
    private static Formula I => F.Id("I");
    private static Formula v => F.Id("v");
    private static Formula Sets => Call("Finset", V);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula Degree(Formula s, Formula x) => Call("d", G, s, x);
    private static Formula Star(Formula s) => Call("IsStarForming", G, K, s);
    private static Formula Independent(Formula s) => Call("IsKIndependent", G, K, s);
    private static Formula Maximum(string name, Formula condition) => Call("supCard",
        Seq(OpenBrace, F.Id(name), Sp, InMacro, Sp,
            Call("powerset", Call("univ", V)), Sp, Mid, Sp, condition, CloseBrace));

    private static Formula StarFormula()
    {
        var c = F.Id("c"); var l = F.Id("L"); var leaf = F.Id("ell");
        var copy = And(Eq(Call("card", l), K),
            And(new Formula.Not(Member(c, l)),
            And(Call("Subset", Call("insert", c, l), Call("insert", v, S)),
            And(All("ell", V, Imp(Member(leaf, l), Call("Adj", G, c, leaf))),
                Member(v, Call("insert", c, l))))));
        return Disp(Iff(Star(S), All("v", V, Imp(new Formula.Not(Member(v, S)),
            Ex("c", V, Ex("L", Sets, copy))))));
    }

    private static Formula LocalFormula()
    {
        var u = F.Id("u");
        return All("v", V, Imp(new Formula.Not(Member(v, S)),
            Or(Le(D(2), Degree(S, v)), Ex("u", V,
                And(Member(u, S), And(Call("Adj", G, v, u), Le(D(1), Degree(S, u))))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var graph = F.Id("G");
        return Disp(Iff(F.Id("claim"), All("n", F.Id("Nat"),
            All("G", Call("SimpleGraph", Call("Fin", n)),
                Imp(Call("Colorable", graph, D(2)),
                    Eq(Call("beta", graph, D(2)), Call("SF", graph, D(2))))))));
    }

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(selector == "starForming_two_iff"
                ? "sf2-star-forming-two-iff" : "sf2-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
