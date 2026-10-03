using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class SierpinskiLimitedDominationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/SierpinskiLimitedDomination.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/bozovic2026limiteddomination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The k-limited domination number of the Sierpiński graph S(n,m) is proved exactly for n ≥ 1, 2 ≤ m, and 1 ≤ k ≤ m − 1.",
        H("Božović Conjecture 12: limited domination in Sierpiński graphs"),
        Blocks(
            Node("adjacency", "Sierpiński adjacency", "sierAdj", AdjacencyFormula(),
                "For words u and v, adjacency is witnessed by an index h: the coordinates before h agree, the h-coordinates differ, and every later coordinate of each word is the other's h-coordinate. This is the adjacency rule of Section 2.", DescribeRole.Definition),
            Node("graph", "Sierpiński graph", "sierGraph", GraphFormula(),
                "sierGraph r m is the loopless undirected SimpleGraph on functions from Fin (r + 1) to Fin m whose adjacency relation is sierAdj r m.", DescribeRole.Definition),
            Node("limited", "k-limited dominating set", "isKLimited", LimitedFormula(),
                "A set is k-limited dominating when it is dominating and every selected vertex has at most k neighbors outside the set.", DescribeRole.Definition),
            Node("gamma", "Limited domination number", "gamma", GammaFormula(),
                "gamma r m k is the infimum of the cardinalities of k-limited dominating subsets of the functions from Fin (r + 1) to Fin m.", DescribeRole.Definition),
            Node("claim", "Conjecture 12", "claim", ClaimFormula(),
                "Section 6, Conjecture 12 (p. 9) states verbatim: \"Let n, m, and k be integers such that n ≥ 1 and 1 ≤ k ≤ m − 1. Then γ_k^L(S(n, m)) = (m−k)·m^(n−1).\" The formal encoding uses n,m,k : ℕ, the graph rank n−1, and gamma for γ_k^L.", DescribeRole.Definition),
            Node("result", "Conjecture 12 proved", "result", ResultFormula(),
                "The theorem result has type claim. Its proof gives a recursive coloring constant on linking edges and bijective on every base clique for the upper bound; the lower bound charges every empty base clique an additional k−1 vertices. The result also specializes the source's Theorems 10 and 11 at k = 1 and m = 3.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("sierpinski-limited-domination-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula AdjacencyFormula()
    {
        var r = F.Id("r");
        var m = F.Id("m");
        var u = F.Id("u");
        var v = F.Id("v");
        var h = F.Id("h");
        var t = F.Id("t");
        var uAt = new Formula.Apply(u, [t]);
        var vAt = new Formula.Apply(v, [t]);
        var uAtH = new Formula.Apply(u, [h]);
        var vAtH = new Formula.Apply(v, [h]);
        var before = Universal("t", Call("Fin", Add(r, D(1))),
            Implies(Rel(t, FormulaRelationOperator.LessThan, h),
                Eqn(uAt, vAt)));
        var different = Neq(uAtH, vAtH);
        var after = Universal("t", Call("Fin", Add(r, D(1))),
            Implies(Rel(h, FormulaRelationOperator.LessThan, t),
                And(Eqn(new Formula.Apply(u, [t]), vAtH),
                    Eqn(new Formula.Apply(v, [t]), uAtH))));
        var witness = Exists("h", Call("Fin", Add(r, D(1))),
            And(before, And(different, after)));
        var body = Universal("u", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m)), Universal("v", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m)),
            Iff(Call("sierAdj", r, m, u, v), witness)));
        return Disp(Universal("r", Nat(), Universal("m", Nat(), body)));
    }

    private static Formula GraphFormula()
    {
        var r = F.Id("r");
        var m = F.Id("m");
        var u = F.Id("u");
        var v = F.Id("v");
        var body = Universal("u", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m)), Universal("v", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m)),
            Iff(Call("Adj", Call("sierGraph", r, m), u, v), Call("sierAdj", r, m, u, v))));
        return Disp(Universal("r", Nat(), Universal("m", Nat(), body)));
    }

    private static Formula LimitedFormula()
    {
        var r = F.Id("r");
        var m = F.Id("m");
        var k = F.Id("k");
        var d = F.Id("D");
        var u = F.Id("u");
        var body = And(Call("IsDominating", Call("sierGraph", r, m),
            Seq(Open, d, Colon, Sp, Call("Set", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m))), Close)), Universal("u", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m)),
            Implies(Rel(u, FormulaRelationOperator.MemberOf, d),
                Rel(Call("card", Call("sdiff", Call("neighborFinset", Call("sierGraph", r, m), u), d)),
                    FormulaRelationOperator.LessThanOrEqual, k))));
        return Disp(Universal("r", Nat(), Universal("m", Nat(), Universal("k", Nat(),
            Universal("D", Call("Finset", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m))),
                Iff(Call("isKLimited", r, m, k, d), body))))));
    }

    private static Formula GammaFormula()
    {
        var r = F.Id("r");
        var m = F.Id("m");
        var k = F.Id("k");
        var n = F.Id("n");
        var d = F.Id("D");
        var set = SetBuilder(Seq(Typed(n, Nat()), Sp, Mid, Sp,
            Exists("D", Call("Finset", Arrow(Call("Fin", Add(r, D(1))), Call("Fin", m))),
                And(Call("isKLimited", r, m, k, d), Eqn(Call("card", d), n)))));
        return Disp(Universal("r", Nat(), Universal("m", Nat(), Universal("k", Nat(),
            Eqn(Call("gamma", r, m, k), Call("sInf", set))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var k = F.Id("k");
        var hypotheses = And(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, n),
            And(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, m),
                And(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, k),
                    Rel(k, FormulaRelationOperator.LessThanOrEqual,
                        Subtract(m, D(1))))));
        var conclusion = Eqn(Call("gamma", Subtract(n, D(1)), m, k),
            Multiply(Subtract(m, k), Power(m, Subtract(n, D(1)))));
        var body = Universal("n", Nat(), Universal("m", Nat(), Universal("k", Nat(),
            Implies(hypotheses, conclusion))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Universal(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Neq(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula SetBuilder(Formula body) => Seq(OpenBrace, body, CloseBrace);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
}
