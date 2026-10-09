using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SupportForestMoments;

internal sealed class ShapiroQuarticInversionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/shapiro2026spectrum");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two trees have equal Laplacian characteristic polynomials, lower support counts and moments through degree four, but different four-edge path counts.",
        H("The unweighted fourth moment does not determine four-edge forest counts"), Blocks(
            Def("claim", "Shapiro's inversion question", ClaimFormula(), "Section 12, page 13, Outlook item 1: \"Compute an explicit closed formula for the unweighted fourth moment and invert it, modulo Laplacian and cubic data, on the finite list of four-edge support forests. The degree-three inversion is complete by the cubic inversion theorem above.\" The inversion implication quantifies over n ≥ 4, all trees on Fin n, every forest without isolated vertices with at most three edges, and every such forest with exactly four edges. Laplacian data is the characteristic polynomial over ℤ. The moments use the right side of (6.2); the integer r ranges over {2,3,4}. A refutation answers the inversion part; it makes no claim that a closed fourth-moment formula does not exist.", true),
            Def("EA", "Edges of the first tree", Equal(F.Id("EA"), EdgeLiteral(true)), "These eleven unordered pairs lie in Sym2 (Fin 12). Labels are 0 through 11."),
            Def("A", "First tree", Equal(F.Id("A"), App(Q("SimpleGraph", "fromEdgeSet"), Cast(F.Id("EA"), Call("Set", Call("Sym2", Fin(Num(12))))))), "The graph has exactly the displayed edges. Its paths from vertex zero establish connectedness; eleven edges on twelve vertices give the tree property."),
            Def("EB", "Edges of the second tree", Equal(F.Id("EB"), EdgeLiteral(false)), "These eleven unordered pairs lie in Sym2 (Fin 12)."),
            Def("B", "Second tree", Equal(F.Id("B"), App(Q("SimpleGraph", "fromEdgeSet"), Cast(F.Id("EB"), Call("Set", Call("Sym2", Fin(Num(12))))))), "The graph has exactly the displayed edges and is also a tree."),
            Def("P5", "Four-edge path", Equal(Name("P5"), App(Q("SimpleGraph", "fromEdgeSet"), Cast(Cast(Set(PairEdge(0,1), PairEdge(1,2), PairEdge(2,3), PairEdge(3,4)), Call("Finset", Call("Sym2", Fin(D(5))))), Call("Set", Call("Sym2", Fin(D(5))))))), "The source's path model has five vertices and four edges. It has no isolated vertex and is acyclic."),
            Describe.Lean(DescribeId.Create("shapiro-quartic-a-m4"), DeclarationHandle.Create(Prefix + "A_M4"), H("Fourth moment of the first tree"),
                StatementSource.FromAuthor(Disp(Equal(C("Mr2", F.Id("A"), D(4)), Num(234836)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The recursive evaluator splits the first two choices, evaluates all remaining ordered edge pairs, and sums the resulting eleven-by-eleven integer table. Its soundness theorem identifies this value with the literal edge-word moment. This equality is used in comparing the two trees' moments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shapiro-quartic-result"), DeclarationHandle.Create(Prefix + "result"), H("Failure of quartic inversion"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The twelve-vertex pair A, B has the same Laplacian characteristic polynomial, as certified by a rational invertible intertwiner. Explicit bijections between their edge subsets match every support of size at most three. The edge-word sums give M₂ = 3164, M₃ = 26730 and M₄ = 234836 for both trees. Their P5 support counts are respectively 12 and 10, contradicting the inversion implication. This is a statement about the base pair. It does not establish an infinite family or equality of the full (n−2,2)-spectrum, and it does not refute either conjecture using all moments."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shapiro-2026-unweighted-fourth-moment-inversion"),
                    ResolutionKind.Refuted))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection"))]));
    private static DocumentBlock Def(string name, string title, Formula formula, string prose, bool literature = false) => Describe.Lean(
        DescribeId.Create("shapiro-quartic-" + (name == "P5" ? "path" : name.ToLowerInvariant())), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula PairEdge(int a, int b) => C("s", Num(a), Num(b));
    private static Formula EdgeLiteral(bool first) => first
        ? Set(PairEdge(0,5), PairEdge(0,10), PairEdge(0,11), PairEdge(0,1), PairEdge(1,2), PairEdge(2,3), PairEdge(3,4), PairEdge(5,6), PairEdge(5,9), PairEdge(6,7), PairEdge(6,8))
        : Set(PairEdge(0,8), PairEdge(0,1), PairEdge(1,2), PairEdge(1,5), PairEdge(1,7), PairEdge(2,3), PairEdge(2,4), PairEdge(5,6), PairEdge(8,9), PairEdge(9,10), PairEdge(9,11));
    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), t = F.Id("T"), tp = F.Id("Tprime"), h = F.Id("h"), f = F.Id("F"), r = F.Id("r");
        Formula SupportClause(bool four) => All("h", Nat(), All("F", Graph(h), Implies(C("noIsolated", f), Implies(Field(f, "IsAcyclic"), Implies(
            four ? Equal(FinsetCard(EdgeSet(f)), D(4)) : Leq(FinsetCard(EdgeSet(f)), D(3)), Equal(C("NH", t, f), C("NH", tp, f)))))));
        Formula moments = All("r", Nat(), Implies(Member(r, Cast(Set(D(2),D(3),D(4)), Call("Finset", Nat()))), Equal(C("Mr2", t, r), C("Mr2", tp, r))));
        Formula lap(Formula graph) => App(Q("Matrix", "charpoly"), App(Q("SimpleGraph", "lapMatrix"), graph, Ints()));
        Formula implication = All("n", Nat(), Implies(Leq(D(4),n), All("T", Graph(n), All("Tprime", Graph(n), Implies(Field(t,"IsTree"), Implies(Field(tp,"IsTree"), Implies(Equal(lap(t),lap(tp)), Implies(SupportClause(false), Implies(moments, SupportClause(true))))))))));
        return IffFormula(F.Id("claim"), implication);
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);




    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(Lex(owner), Dot, Lex(name))));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Field(Formula value, string name) => App(Q("SimpleGraph", name), value);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => new Formula.Integers();
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula n) => Call("SimpleGraph", Fin(n));



    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);


    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Set(params Formula[] items) =>
        Seq(OpenBrace, Seq(items.SelectMany((item, index) => index == 0 ? new[] { item } : new[] { Comma, Sp, item }).ToArray()), CloseBrace);
    private static Formula Name(string name) => name switch
    {
        "c1" => F.Id("c1"),
        "c2" => F.Id("c2"),
        "chi" => Seq(F.Id("x")),
        "NH" => Seq(F.Id("N"), Underscore, Grp(F.Id("H"))),
        "Mr2" => Seq(F.Id("M"), Underscore, Grp(F.Id("r2"))),
        "P5" => F.Id("P5"),
        _ => Lex(name),
    };
    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Name(name) : App(Name(name), args);

    private static Formula FinsetCard(Formula s) => App(Q("Finset", "card"), s);
    private static Formula EdgeSet(Formula g) => Field(g, "edgeFinset");





    private static Formula Lex(string name) => name switch
    {
        "natChi" => Seq(F.Id("nat"), Seq(Mathrm, Grp(F.Id("x")))),
        "Equiv.Perm" => Seq(F.Id("Equiv"), Dot, F.Id("Perm")),
        "endpointIso_image" => Seq(F.Id("endpointIso"), Underscore, Grp(F.Id("image"))),
        "swap_comm" => Seq(F.Id("swap"), Underscore, Grp(F.Id("comm"))),
        _ => F.Id(name),
    };
}
