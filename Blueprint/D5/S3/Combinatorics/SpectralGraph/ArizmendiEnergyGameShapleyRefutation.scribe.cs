using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class ArizmendiEnergyGameShapleyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/arizmendi2020energygame");

    public DocumentDefinition Create()
    {
        Formula v = V("V"), g = V("G"), s = V("S"), w = V("w"), x = V("x"), i = V("i");
        Formula worth = Carrier(true, All("G", Call("SimpleGraph", v), All("S", Call("Finset", v),
            Eqn(Call("worth", g, s), App(Qualified("D5", "S3", "Combinatorics", "Graph",
                "SubgroupGenerating", "CyclicExtensionRefutation", "graphEnergy"),
                App(Qualified("SimpleGraph", "induce"), g,
                    Parenthesized(Seq(s, Colon, Sp, Call("Set", v)))),
                Qualified("D5", "S3", "Combinatorics", "Graph", "SubgroupGenerating",
                    "CyclicExtensionRefutation", "MatrixKind", "adjacency"))))));
        Formula core = Carrier(false, All("w", Fn(Call("Finset", v), C("Real")),
            Eqn(Call("core", w), Seq(OpenBrace, x, Colon, Sp, Fn(v, C("Real")), Sp, Mid, Sp,
                Parenthesized(new Formula.Logic(
                    All("S", Call("Finset", v),
                        new Formula.Relation(Total(x, s), FormulaRelationOperator.GreaterThanOrEqual, App(w, s))),
                    FormulaLogicOperator.And,
                    Eqn(Total(x, Qualified("Finset", "univ")), App(w, Qualified("Finset", "univ"))))),
                CloseBrace))));
        Formula card = App(Qualified("Fintype", "card"), v);
        Formula size = App(Qualified("Finset", "card"), s);
        Formula coefficient = new Formula.Fraction(
            Mul(Cast(Factorial(size)), Cast(Factorial(Sub(Sub(card, size), D(1))))),
            Cast(Factorial(card)));
        Formula shapley = Carrier(true, All("w", Fn(Call("Finset", v), C("Real")), All("i", v,
            Eqn(Call("shapley", w, i), SumOver("S",
                App(Qualified("Finset", "powerset"),
                    App(Qualified("Finset", "erase"), Qualified("Finset", "univ"), i)),
                Mul(coefficient, Parenthesized(Sub(
                    App(w, App(Qualified("Finset", "insert"), i, s)), App(w, s)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete bipartite graphs refute Shapley core membership for graph energy games.",
            H("The graph energy game and an unbalanced bipartite obstruction"), Blocks(
                Node("worth", "Energy of an induced coalition", "worth", worth,
                    "Definition 3.1, page 5: “Let G = (V, E) be a simple undirected graph. For each subset S ⊂ V let w(S) := 𝓔(I(S)) where I(S) is the graph induced by S. We denote (V, w), the energy game on G.” Here the coalition is a Finset and its induced vertex type is (S : Set V). The existing graphEnergy with MatrixKind.adjacency sums the absolute real adjacency eigenvalues with multiplicity and center zero. This includes the empty coalition.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("core", "Coalition rationality and efficiency", "core", core,
                    "Definition 2.7, page 4: “The core of a game (N, w), denoted by C(w) is the set of imputations that are group rational. That is,” followed by “C(w) = {x| x(S) ≥ w(S) for each S ⊂ N and x(N) = w(N)}”. The same page states: “For a payoff distribution x and a coalition S, we use the notation x(S) = ∑_{i∈S} xᵢ.” The finite sums range over all coalitions, including the empty set and the full set. The variable x has type V → Real.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("shapley", "Factorial formula for the Shapley allocation", "shapley", shapley,
                    "Section 2.4, page 4: “The Shapley value is the only value that satisfies the axioms of efficiency, symmetry, additivity and null player, it is well known that actually the Shapley value is given by” followed by “φᵢ(w) = ∑_{S⊂N∖{i}} |S|!(n − |S| − 1)!(w(S ∪ {i}) − w(S))/n!” The index S ranges over the powerset of all vertices except i. The three factorials are computed in Nat and then coerced to Real; the displayed division is real division. Natural subtraction is truncated subtraction, agreeing with ordinary subtraction on this powerset because S.card ≤ Fintype.card V − 1.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("claim", "Conjecture 3.10", "claim", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                    "Conjecture 3.10, page 8: “For the energy game, the Shapley value is in the core.” The universal size n includes zero, and SimpleGraph (Fin n) supplies a finite simple undirected graph without a connectedness or degree restriction. Core membership includes every coalition inequality and efficiency.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("result", "Refutation by K₂,₅₀", "result", Seq(Neg, Sp, Parenthesized(ClaimBody())),
                    "For every m ≥ 50, the graph with two scarce-side vertices a and b and m other vertices, with exactly the cross edges, has coalition energy 2√(rk) when the coalition contains r scarce-side vertices and k other vertices. Its scarce-side Shapley payoff is 2((m + √2)∑ₖ₌₀ᵐ√k + (√2 − 2)∑ₖ₌₀ᵐk√k)/((m + 1)(m + 2)). Summing the one-step inequalities gives ∑ₖ₌₀ᵐ√k ≥ (2/3)m√m and ∑ₖ₌₀ᵐk√k ≤ (2/5)m²√m + m√m. With the negative coefficient √2 − 2 treated in its correct direction, these bounds put the payoff above 2(√2 − 1)√m. If the allocation were in the core, its efficiency equality would make the coalition excluding a violate its lower payoff bound 2√m. Taking m = 50 and vertices 0 and 1 in Fin 52 disproves the universal proposition. No optimal threshold, asymptotic limit, or classification of trees or regular graphs is asserted.",
                    DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    }

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("arizmendi-energy-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula ClaimBody() => All("n", C("Nat"), All("G", Call("SimpleGraph", Call("Fin", V("n"))),
        new Formula.Relation(Call("shapley", Call("worth", V("G"))), FormulaRelationOperator.MemberOf,
            Call("core", Call("worth", V("G"))))));
    private static Formula Carrier(bool decidable, Formula body) => All("V", C("Type"), Seq(
        OpenBracket, Call("Fintype", V("V")), CloseBracket, Sp,
        decidable ? Seq(OpenBracket, Call("DecidableEq", V("V")), CloseBracket, Sp, body) : body));
    private static Formula Total(Formula x, Formula s) => SumOver("i", s, App(x, V("i")));
    private static Formula SumOver(string name, Formula set, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Factorial(Formula n) => App(Qualified("Nat", "factorial"), n);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, C("Real")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(params string[] names) => Seq(names.Select(C)
        .SelectMany((name, index) => index == 0 ? new[] { name } : new[] { Dot, name }).ToArray());
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? C(name) : App(C(name), args);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Fn(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
