using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class WangQinXiaLooplessStabilityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/wangqinxia2025unexpectedautomorphisms");

    public DocumentDefinition Create()
    {
        var g = X("G"); var h = X("H");
        return DocumentDefinition.Create(ScribeNode.Create(
            "A stable loopless family has nontrivially unstable pairs with the four-vertex path.",
            H("A loopless counterexample to Wang–Qin–Xia Conjecture 1.3"),
            Blocks(
                Node("twin-free", "Distinct open neighborhoods", "TwinFree", DescribeRole.Definition,
                    OneGraph(Eq(Call("TwinFree", g),
                        App(Q("Function", "Injective"), App(Q("SimpleGraph", "neighborSet"), g)))),
                    AssessedProvenance.FromLiterature(Source),
                    "Page 1: “A graph is called twin-free if no two vertices have the same neighborhood in the graph.” The variable G is a loopless graph on V; injectivity refers to its full open-neighborhood map."),
                Node("coprime", "No nontrivial common direct factor", "Coprime", DescribeRole.Definition,
                    TwoGraphs(Eq(Call("Coprime", g, h), CoprimeBody())),
                    AssessedProvenance.FromLiterature(Source),
                    "Page 1: “We say that graphs Γ and Σ are coprime (with respect to the direct product) if there exists no graph Δ of order greater than 1 such that Γ ≅ Γ′×Δ and Σ ≅ Σ′×Δ for some graphs Γ′ and Σ′.” The graphs G and H represent Γ and Σ. The common factor F and the cofactors G′ and H′ are arbitrary finite symmetric relations, including diagonal edges. Their carriers Fin d, Fin a and Fin b cover every finite isomorphism class. RelIso preserves and reflects adjacency."),
                Node("stable-pair", "Componentwise automorphisms", "StablePair", DescribeRole.Definition,
                    TwoGraphs(Eq(Call("StablePair", g, h), Parenthesized(StablePairBody()))),
                    AssessedProvenance.FromLiterature(Source),
                    "Page 1: “In other words, (Γ,Σ) is stable if and only if (1) is an equality.” Equation (1) is Aut(Γ)×Aut(Σ) ≤ Aut(Γ×Σ), with componentwise action. The formula says that every automorphism f of dirProd G H is induced by graph automorphisms α of G and β of H. It quantifies over all vertices of the product."),
                Node("stable-graph", "Stability of a single graph", "StableGraph", DescribeRole.Definition,
                    OneGraph(Eq(Call("StableGraph", g),
                        Call("StablePair", g, Typed(Q("Top", "top"), Call("SimpleGraph", Call("Fin", D(2))))))),
                    AssessedProvenance.FromLiterature(Source),
                    "Page 1: “Indeed, a graph Γ is stable in the sense of [7] if and only if the pair (Γ,K₂) is stable.” The complete loopless graph on Fin 2 represents K₂."),
                Node("nontrivial", "The hypotheses on a graph pair", "Nontrivial", DescribeRole.Definition,
                    TwoGraphs(Eq(Call("Nontrivial", g, h), NontrivialBody(g, h))),
                    AssessedProvenance.FromLiterature(Source),
                    "Definition 1.1, page 1: “A graph pair (Γ,Σ) is nontrivial if Γ and Σ are coprime connected twin-free graphs and exactly one of them is bipartite.” Connectedness, injectivity of the open-neighborhood maps, and both alternatives for the bipartite factor are retained."),
                Node("claim", "Conjecture 1.3", "claim", DescribeRole.Definition,
                    Eq(Typed(X("claim"), X("Prop")), Parenthesized(ClaimBody())),
                    AssessedProvenance.FromLiterature(Source),
                    "Conjecture 1.3, page 2: “Let (Γ,Σ) be a nontrivial graph pair without loops, where Σ is bipartite. Then (Γ,Σ) is stable if and only if Γ is stable.” V and W are finite vertex types, Gamma and Sigma are SimpleGraph values, and Sigma.IsBipartite is a separate hypothesis. The SimpleGraph carriers enforce looplessness. The implication retains the whole predicate Nontrivial, even though one of its bipartiteness alternatives follows from the separate hypothesis."),
                Node("result", "The loopless conjecture is false", "result", DescribeRole.Theorem,
                    new Formula.Not(Parenthesized(ClaimBody())),
                    AssessedProvenance.FromRepo(Source),
                    "For every m ≥ 3, take vertices (t,a,b) in Fin m × Bool × Bool and put R(a,b) precisely when a=true or b=true. Two vertices (t,a,b) and (u,c,d) are adjacent precisely when t≠u, R(a,d), and R(c,b). This is loopless. The second graph has vertices (s,i) in Bool × Bool and adjacency s≠r together with R(i,j); it is the four-vertex path. Neighborhood inclusion gives one four-element diamond at each index. Preservation of these diamonds under a two-fold automorphism, and a third index, force its two permutations to agree. This makes the first graph stable. Every independent set in it has at most m+2 vertices, excluding a half-size independent slice from a two-vertex common factor; a four-vertex common factor would force bipartiteness. The graph pair is connected, twin-free, coprime even when factors have loops, and has exactly one bipartite factor. In the product, the involution sends ((t,a,b),(false,i)) to ((t,a,i),(false,b)) and ((t,a,b),(true,j)) to ((t,j,b),(true,a)). It preserves adjacency and acts noncomponentwise. The case m=3 contradicts the universal equivalence."))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, DescribeRole role,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            declaration == "result"
                ? new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wqx-loopless-stability-refutation"), ResolutionKind.Refuted)
                : null);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot,
        Operatorname, Grp(X(name)));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, body);
    private static Formula SomeSymbol(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Inst(string name, Formula arg, Formula body) =>
        Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Product(Formula left, Formula right) => Call("Prod", left, right);
    private static Formula Fst(Formula value) => App(Q("Prod", "fst"), value);
    private static Formula Snd(Formula value) => App(Q("Prod", "snd"), value);
    private static Formula GraphIso(Formula g, Formula h) => App(Q("SimpleGraph", "Iso"), g, h);
    private static Formula Adj(Formula g) => App(Q("SimpleGraph", "Adj"), g);
    private static Formula Edge(Formula g, Formula x, Formula y) =>
        App(Q("LoopGraph", "edge"), g, x, y);
    private static Formula OneGraph(Formula body) =>
        All("V", X("Type"), All("G", Call("SimpleGraph", X("V")), body));
    private static Formula TwoGraphs(Formula body) => All("V", X("Type"), All("W", X("Type"),
        All("G", Call("SimpleGraph", X("V")), All("H", Call("SimpleGraph", X("W")), body))));

    private static Formula FactorRelation(Formula cofactor, string order)
    {
        var x = X("x"); var y = X("y");
        var carrier = Product(Call("Fin", X(order)), Call("Fin", X("d")));
        var body = And(Edge(cofactor, Fst(x), Fst(y)), Edge(X("F"), Snd(x), Snd(y)));
        return Seq(X("fun"), Sp, Typed(x, carrier), Sp, Mapsto, Sp,
            X("fun"), Sp, Typed(y, carrier), Sp, Mapsto, Sp, Parenthesized(body));
    }

    private static Formula CoprimeBody()
    {
        var factors = And(Lt(D(1), X("d")), And(
            Call("Nonempty", Call("RelIso", Adj(X("G")), Parenthesized(FactorRelation(Seq(X("G"), Apos), "a")))),
            Call("Nonempty", Call("RelIso", Adj(X("H")), Parenthesized(FactorRelation(Seq(X("H"), Apos), "b"))))));
        return new Formula.Not(Parenthesized(Some("d", X("Nat"), Some("a", X("Nat"), Some("b", X("Nat"),
            Some("F", Call("LoopGraph", X("d")), SomeSymbol(Seq(X("G"), Apos), Call("LoopGraph", X("a")),
                SomeSymbol(Seq(X("H"), Apos), Call("LoopGraph", X("b")), factors))))))));
    }

    private static Formula StablePairBody()
    {
        var g = X("G"); var h = X("H"); var p = X("p");
        var product = Call("dirProd", g, h);
        var image = Parenthesized(Seq(App(Alpha, Fst(p)), Comma, Sp, App(Beta, Snd(p))));
        return All("f", GraphIso(product, product), SomeSymbol(Alpha, GraphIso(g, g),
            SomeSymbol(Beta, GraphIso(h, h), All("p", Product(X("V"), X("W")), Eq(Call("f", p), image)))));
    }

    private static Formula NontrivialBody(Formula g, Formula h) =>
        And(Call("Coprime", g, h), And(App(Q("SimpleGraph", "Connected"), g),
            And(App(Q("SimpleGraph", "Connected"), h), And(Call("TwinFree", g), And(Call("TwinFree", h),
                Or(And(App(Q("SimpleGraph", "IsBipartite"), g), new Formula.Not(App(Q("SimpleGraph", "IsBipartite"), h))),
                    And(new Formula.Not(App(Q("SimpleGraph", "IsBipartite"), g)), App(Q("SimpleGraph", "IsBipartite"), h))))))));

    private static Formula ClaimBody()
    {
        var gamma = X("Gamma"); var sigma = X("Sigma");
        return All("V", X("Type"), All("W", X("Type"), Inst("Fintype", X("V"), Inst("Fintype", X("W"),
            All("Gamma", Call("SimpleGraph", X("V")), All("Sigma", Call("SimpleGraph", X("W")),
                Imp(Call("Nontrivial", gamma, sigma), Imp(App(Q("SimpleGraph", "IsBipartite"), sigma),
                    Iff(Call("StablePair", gamma, sigma), Call("StableGraph", gamma))))))))));
    }
}
