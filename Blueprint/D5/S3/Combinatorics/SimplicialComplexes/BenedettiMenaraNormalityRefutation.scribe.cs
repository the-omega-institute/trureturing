using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SimplicialComplexes;

internal sealed class BenedettiMenaraNormalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/benedettimenara2026diameter");
    private const string Question = "Page 21, Question 9.1: In Main Theorem A with k ≥ 2, does normality of Δ̂ follow from normality of Δ together with (Gₖ) and purity of Δ̂? (For k ≤ 1 it does, by Proposition 3.5.) The vertex carrier is Fin n, d is facet cardinality and k satisfies 2 <= k and k + 2 <= d. C is the complex whose nonempty faces are the cliques of skeleton K. Every vertex occurs, and AugmentedFace includes the empty face.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ten-vertex complex refutes normality preservation under flag completion.",
        H("Flag completion can destroy normality without changing pure dimension"),
        Blocks(
            Node("Pure", "Pure rank", PureFormula(),
                "Page 7: Throughout, Δ is a (finite) pure simplicial complex of dimension d − 1 on a vertex set V with |V| = n. A facet is a nonempty face maximal under inclusion. Pure K d requires a facet to exist and every facet to have exactly d vertices, so the dimension is d - 1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("dualGraph", "The dual graph", DualFormula(),
                "Page 7: The dual graph 𝒢(Δ) has the facets of Δ as nodes, and its edges join facets that are adjacent, i.e. that share exactly d − 1 vertices; diam(Δ) is its diameter. SimpleGraph.fromRel excludes equality of its vertices and symmetrizes the displayed intersection condition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Normal", "Normality of all face-stars", NormalFormula(),
                "Page 1: The question is typically asked for normal complexes, i.e. complexes Δ where for every face σ, including the empty one, the facets containing σ induce a connected subgraph of 𝒢(Δ). The graph is induced on its own subtype of facets containing sigma. Connected includes nonemptiness.",
                AssessedProvenance.FromLiterature(Source)),
            Node("skeleton", "The one-skeleton", SkeletonFormula(),
                "The vertices are all of Fin n. Distinct u and v are adjacent exactly when their two-element set is a face. Singletons are present in every AbstractSimplicialComplex.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Gap", "The gap in minimal nonfaces", GapFormula(),
                "Page 2: Δ has no minimal nonfaces of size 3, 4, …, d − k. A minimal nonface is not an augmented face and all of its proper subsets are augmented faces. Under k + 2 <= d, the forbidden upper bound is expressed without subtraction as M.card + k <= d. At d = 4 and k = 2 the forbidden interval is empty.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Question 9.1", Disp(Equal(Named("claim"), ClaimBody())),
                Question + " Page 2: Let now Δ̂ be the flag completion of Δ, that is, the clique complex of its 1-skeleton. In the displayed record the fields proving downward closure and singleton membership are determined by the clique condition.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("bmnormal-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of Question 9.1"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take n = 10, d = 4 and k = 2, with a = 6, z = 7, w = 8 and b = 9. The original facets, in order, are zw01, zw12, zw23, zw34, zw45, zw50, az01, az12, az23, az34, wb01, wb50, wb45, wb34 and ab01. Each has four vertices and every vertex occurs. For any two facets at distinct positions, their intersection is contained in an earlier facet meeting the later one in three vertices. Strong induction on the sum of the positions constructs a path between every two facets containing a given face, including the empty face. Thus the original complex is normal. The completion has precisely these facets and ab34, and remains pure of rank four. Its ab-star consists of ab01 and ab34, whose intersection has two vertices; its induced dual graph has two vertices and no edges. Consequently the completion is not normal.")),
                    Paragraph(Text("The gap condition here is vacuous, as the source allows at k = d - 2. Proposition 3.5 for k <= 1 and Main Theorem A, which assumes completion normality, retain their stated hypotheses. This example leaves preservation under nonvacuous G_k with 2 <= k < d - 2 and the uniform arbitrary-N family as separate questions."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-bm2611q91"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("bmnormal-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula SubsetOf(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Sets(Formula n) => Call("Finset", Fin(n));
    private static Formula Complex(Formula n) => Call("AbstractSimplicialComplex", Fin(n));
    private static Formula Fun(string variable, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(variable), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula Face(Formula k, Formula s) => App(
        Seq(Named("D5"), Dot, Named("S3"), Dot, Named("Geometry"), Dot,
            Named("FiniteRelativeSimplicialCollapse"), Dot, Named("AugmentedFace")),
        App(Qualified("AbstractSimplicialComplex", "toPreAbstractSimplicialComplex"), k), s);
    private static Formula Facet(Formula n, Formula k, Formula f) =>
        And(Member(f, k), All("T", Sets(n), Implies(Member(F.Id("T"), k),
            Implies(SubsetOf(f, F.Id("T")), Equal(F.Id("T"), f)))));
    private static Formula Facets(Formula n, Formula k) => Call("Subtype",
        Parenthesized(Fun("F", Sets(n), Facet(n, k, F.Id("F")))));

    private static Formula PureFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), d = F.Id("d"), f = F.Id("F");
        Formula body = And(Ex("F", Sets(n), Facet(n, k, f)),
            All("F", Sets(n), Implies(Facet(n, k, f), Equal(App(Qualified("Finset", "card"), f), d))));
        return Disp(All("n", Nat(), All("K", Complex(n), All("d", Nat(), Equal(Call("Pure", k, d), body)))));
    }
    private static Formula DualFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), d = F.Id("d"), f = F.Id("F"), h = F.Id("H");
        Formula inter = App(Qualified("Finset", "inter"), Call("val", f), Call("val", h));
        Formula relation = Equal(Add(App(Qualified("Finset", "card"), Parenthesized(inter)), D(1)), d);
        Formula graph = App(Qualified("SimpleGraph", "fromRel"),
            Parenthesized(Fun("F", Facets(n, k), Fun("H", Facets(n, k), relation))));
        return Disp(All("n", Nat(), All("K", Complex(n), All("d", Nat(), Equal(Call("dualGraph", k, d), graph)))));
    }
    private static Formula NormalFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), d = F.Id("d"), sigma = F.Id("sigma"), f = F.Id("F");
        Formula star = Seq(OpenBrace, f, Colon, Facets(n, k), Sp, Bar, Sp,
            SubsetOf(sigma, Call("val", f)), CloseBrace);
        Formula graph = App(Qualified("SimpleGraph", "induce"), star, Call("dualGraph", k, d));
        Formula body = All("sigma", Sets(n), Implies(Face(k, sigma), App(Qualified("SimpleGraph", "Connected"), graph)));
        return Disp(All("n", Nat(), All("K", Complex(n), All("d", Nat(), Equal(Call("Normal", k, d), body)))));
    }
    private static Formula SkeletonFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), u = F.Id("u"), v = F.Id("v");
        Formula pair = Parenthesized(Seq(OpenBrace, u, Comma, v, CloseBrace, Colon, Sets(n)));
        Formula graph = App(Qualified("SimpleGraph", "fromRel"),
            Parenthesized(Fun("u", Fin(n), Fun("v", Fin(n), Member(pair, k)))));
        return Disp(All("n", Nat(), All("K", Complex(n), Equal(Call("skeleton", k), graph))));
    }
    private static Formula GapFormula()
    {
        Formula n = F.Id("n"), k = F.Id("K"), d = F.Id("d"), j = F.Id("k"), m = F.Id("M"), t = F.Id("T");
        Formula minimal = And(new Formula.Not(Face(k, m)), All("T", Sets(n),
            Implies(Seq(t, Sp, Subset, Sp, m), Face(k, t))));
        Formula forbidden = And(AtMost(D(3), App(Qualified("Finset", "card"), m)), AtMost(Add(App(Qualified("Finset", "card"), m), j), d));
        Formula body = All("M", Sets(n), Implies(minimal, new Formula.Not(Parenthesized(forbidden))));
        return Disp(All("n", Nat(), All("K", Complex(n), All("d", Nat(), All("k", Nat(), Equal(Call("Gap", k, d, j), body))))));
    }
    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), d = F.Id("d"), j = F.Id("k"), k = F.Id("K"), c = F.Id("C"), s = F.Id("s");
        Formula faces = Seq(OpenBrace, s, Sp, Bar, Sp,
            And(App(Qualified("Finset", "Nonempty"), s), App(Qualified("SimpleGraph", "IsClique"), Call("skeleton", k),
                Parenthesized(Seq(s, Colon, Call("Set", Fin(n)))))), CloseBrace);
        Formula completion = Parenthesized(Seq(OpenBrace, Named("faces"), Colon, Eq, faces, CloseBrace, Colon, Complex(n)));
        Formula body = Implies(AtMost(D(2), j), Implies(AtMost(Add(j, D(2)), d),
            Implies(Call("Pure", k, d), Implies(Call("Normal", k, d), Implies(Call("Gap", k, d, j),
                Implies(Call("Pure", c, d), Call("Normal", c, d)))))));
        Formula let = Seq(Named("let"), Sp, c, Colon, Eq, completion, Semi, Sp, body);
        return All("n", Nat(), All("d", Nat(), All("k", Nat(), All("K", Complex(n), let))));
    }
}
