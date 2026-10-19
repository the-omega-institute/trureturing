using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class PolettiniPinnedTreeSpanRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/polettini2024coplanarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangle of pinned reversible edges in unit-rate K4 makes the rooted spanning-tree vectors linearly dependent.",
        H("Triangle pins refute the proposed spanning-tree dimension"), Blocks(
            Paragraph(Text("Vertices are Fin N. The real rate r(a,b) is positive exactly on directed edges a → b. "
                + "Each pinned edge has three statuses: none excludes both orientations, some true includes the forward orientation "
                + "and excludes the backward orientation, and some false does the reverse. Thus functions Fin n → Option Bool "
                + "index all 3ⁿ coordinates. A parent map fixes its root; its root loop contributes no rate factor.")),
            Node("Irreducible", "Irreducibility", IrreducibleFormula(),
                "Page 6, §2.1: “We assume the graph to be irreducible, that is, there exists a path x ⇝ y of nonzero weight between any two vertices.” "
                + "Relation.ReflTransGen allows a path of length zero. The edge relation tests strict positivity of r.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsRootedTree", "Rooted spanning trees", TreeFormula(),
                "Page 6, §2.1: “In a directed graph, a rooted spanning tree Tₓ with root x is a spanning tree such that each edge is directed along the unique path that leads to the root.” "
                + "The parent p(v) is the endpoint of the outgoing edge at each non-root vertex v. The root is fixed, "
                + "all other parent edges have positive rate, and every vertex reaches the root after finitely many iterations.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Contains", "An oriented tree edge", ContainsFormula(),
                "For a parent map rooted at x, the arc u → v belongs to the tree precisely when u is not the root and p(u) = v. "
                + "The auxiliary root loop is excluded.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("HasStatus", "The three statuses of a reversible edge", StatusFormula(),
                "The ordered pair e chooses the forward orientation. These three cases specify the two inclusion tests "
                + "separately, so no coordinate permits both orientations of a pinned edge.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tau", "Conditioned rooted spanning-tree vectors", TauFormula(),
                "Page 6, Definition 1: “The conditioned rooted spanning tree polynomial is defined as” "
                + "τₓ^{∖A ∖∖B} = ∑_{Tₓ : A ∩ Tₓ = ∅, B ⊆ Tₓ} r(Tₓ). "
                + "For a status s, A contains both arcs of an absent pin and the excluded reverse arc of an oriented pin; "
                + "B contains the chosen arcs. The displayed sum is over all parent maps satisfying these conditions, "
                + "and its product ranges over all vertices except the root. The empty product is one. "
                + "Every rooted tree is counted once, with weight equal to the product of its directed edge rates.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("deletePins", "Deleting the pinned edges", DeleteFormula(),
                "Both orientations of every pinned pair receive rate zero. All other rates retain their original values.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The conjectured dimension", Eq(Q("claim"), Parenthesized(ClaimBody())),
                "Page 2, Introduction: “Finally, we conjecture that the 3ⁿ-vectors representing the deletion-constriction through n reversible edges span a n+1 dimensional space.” "
                + "N is the number of vertices and n is the number of distinct unordered pinned edges. "
                + "The statement requires nonnegative rates, irreducibility, positive rates in both directions of every pin, "
                + "distinct endpoints, injectivity as Sym2 edges, and irreducibility after deleting all pins. "
                + "The finrank is over ℝ of the span of the N vectors tau(r,pins,x).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A pinned triangle disproves the dimension formula", Not(ClaimBody()),
                "Use N = 4, n = 3, rates zero on the diagonal and one elsewhere, and pins (0,1), (1,2), (2,0). "
                + "Deleting these pins leaves the bidirected star centred at 3, so irreducibility holds before and after deletion. "
                + "There are sixteen rooted trees for each root. Counting their twenty-seven statuses gives "
                + "tau(r,pins,0) + tau(r,pins,1) + tau(r,pins,2) = 3 • tau(r,pins,3). "
                + "The four vectors are therefore linearly dependent, and their span has dimension at most three, "
                + "whereas n + 1 is four. The argument establishes the failure of the universal dimension formula; "
                + "it does not assert a general replacement formula for arbitrary pinned graphs.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("phdl-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(string name, Formula type) => Parenthesized(Seq(V(name), Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Q("fun"), Sp, Typed(name, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Vertex() => Call("Fin", V("N"));
    private static Formula PinIndex() => Call("Fin", V("n"));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Rates() => Arrow(Vertex(), Arrow(Vertex(), Real()));
    private static Formula Parents() => Arrow(Vertex(), Vertex());
    private static Formula PairType() => Seq(Vertex(), Sp, Times, Sp, Vertex());
    private static Formula Status() => Call("Option", Q("Bool"));
    private static Formula Pins() => Arrow(PinIndex(), Parenthesized(PairType()));
    private static Formula Statuses() => Arrow(PinIndex(), Status());
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Size(Formula body) => All("N", Nat(), body);
    private static Formula WithRates(Formula body) => Size(All("r", Rates(), body));
    private static Formula WithParents(Formula body) => Size(All("x", Vertex(), All("p", Parents(), body)));
    private static Formula WithPins(Formula body) => Size(All("n", Nat(), All("r", Rates(), All("pins", Pins(), body))));
    private static Formula R(Formula a, Formula b) => At(V("r"), a, b);
    private static Formula P(Formula a) => At(V("p"), a);
    private static Formula First(Formula e) => Seq(Parenthesized(e), Dot, D(1));
    private static Formula Second(Formula e) => Seq(Parenthesized(e), Dot, D(2));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Iterate(Formula f, Formula k, Formula v) =>
        At(new Formula.Power(f, Seq(OpenBracket, k, CloseBracket)), v);
    private static Formula Contains(Formula u, Formula v) => Call("Contains", V("x"), V("p"), u, v);
    private static Formula IrreducibleFormula() => WithRates(Eq(Call("Irreducible", V("r")), Parenthesized(
        All("x", Vertex(), All("y", Vertex(), Call("Relation.ReflTransGen",
            Lambda("a", Vertex(), Lambda("b", Vertex(), Lt(D(0), R(V("a"), V("b"))))), V("x"), V("y")))))));
    private static Formula TreeFormula() => WithRates(All("x", Vertex(), All("p", Parents(),
        Eq(Call("IsRootedTree", V("r"), V("x"), V("p")), Parenthesized(
            And(Eq(P(V("x")), V("x")), And(
                All("v", Vertex(), Imp(Ne(V("v"), V("x")), Lt(D(0), R(V("v"), P(V("v")))))),
                All("v", Vertex(), Some("k", Nat(), Eq(Iterate(V("p"), V("k"), V("v")), V("x")))))))))));
    private static Formula ContainsFormula() => WithParents(All("u", Vertex(), All("v", Vertex(),
        Eq(Contains(V("u"), V("v")), Parenthesized(And(Ne(V("u"), V("x")), Eq(P(V("u")), V("v"))))))));
    private static Formula StatusFormula()
    {
        Formula forward = Contains(First(V("e")), Second(V("e")));
        Formula backward = Contains(Second(V("e")), First(V("e")));
        Formula StatusAt(Formula s) => Call("HasStatus", V("x"), V("p"), V("e"), s);
        return WithParents(All("e", PairType(), And(
            Eq(StatusAt(Q("none")), Parenthesized(And(Not(forward), Not(backward)))), And(
            Eq(StatusAt(Call("some", Q("true"))), Parenthesized(And(forward, Not(backward)))),
            Eq(StatusAt(Call("some", Q("false"))), Parenthesized(And(backward, Not(forward))))))));
    }
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula ProdIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula TauFormula()
    {
        Formula condition = And(Call("IsRootedTree", V("r"), V("x"), V("p")),
            All("i", PinIndex(), Call("HasStatus", V("x"), V("p"), At(V("pins"), V("i")), At(V("s"), V("i")))));
        Formula selected = Call("Finset.filter", Lambda("p", Parents(), condition), Q("Finset.univ"));
        Formula product = ProdIn("v", Call("Finset.erase", Q("Finset.univ"), V("x")), R(V("v"), P(V("v"))));
        return WithPins(All("x", Vertex(), Eq(Call("tau", V("r"), V("pins"), V("x")),
            Lambda("s", Statuses(), SumIn("p", selected, product)))));
    }
    private static Formula DeleteFormula()
    {
        Formula hit = Some("i", PinIndex(), Or(Eq(At(V("pins"), V("i")), Pair(V("a"), V("b"))),
            Eq(At(V("pins"), V("i")), Pair(V("b"), V("a")))));
        Formula conditional = Seq(Q("if"), Sp, Parenthesized(hit), Sp, Q("then"), Sp, D(0), Sp,
            Q("else"), Sp, R(V("a"), V("b")));
        return WithPins(Eq(Call("deletePins", V("r"), V("pins")),
            Lambda("a", Vertex(), Lambda("b", Vertex(), conditional))));
    }
    private static Formula ClaimBody()
    {
        Formula edge = At(V("pins"), V("i"));
        Formula positivePins = All("i", PinIndex(), And(Ne(First(edge), Second(edge)),
            And(Lt(D(0), R(First(edge), Second(edge))), Lt(D(0), R(Second(edge), First(edge))))));
        Formula nonnegative = All("a", Vertex(), All("b", Vertex(), Le(D(0), R(V("a"), V("b")))));
        Formula distinct = Call("Function.Injective", Lambda("i", PinIndex(), Call("Sym2.mk", edge)));
        Formula rank = Call("Module.finrank", Real(), Call("Submodule.span", Real(),
            Call("Set.range", Call("tau", V("r"), V("pins")))));
        Formula conclusion = Eq(rank, new Formula.Binary(V("n"), FormulaBinaryOperator.Add, D(1)));
        return Size(All("n", Nat(), All("r", Rates(), All("pins", Pins(),
            Imp(nonnegative, Imp(Call("Irreducible", V("r")), Imp(positivePins, Imp(distinct,
                Imp(Call("Irreducible", Call("deletePins", V("r"), V("pins"))), conclusion)))))))));
    }
}
