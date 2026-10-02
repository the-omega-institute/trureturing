using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class RelaxedHardyNoSignallingOptimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/bhattacharya2015hardy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For four parties with two outcomes each, every no-signalling box that satisfies the relaxed Hardy conditions of S. S. Bhattacharya, A. Roy, A. Mukherjee and R. Rahaman (arXiv:1507.07327) has success probability q at most 1/4. This refutes their conjecture that the optimal success probability under no-signalling is 1/3 for any number of parties and any dimension, and corrects their observation of the value 1/3 for four parties.",
        H("The relaxed Hardy test under no-signalling: at most 1/4 for four parties"),
        Blocks(
            Node("box", "No-signalling boxes", BoxFormula(),
                "A box of N parties with d outcomes assigns to every input string s in {u, v}^N (in Lean a map Fin N -> Bool, with false for u and true for v) a probability distribution P(s, .) on the outcome strings x in (Fin d)^N. It is no-signalling when, for every party p and all input strings s, t that agree away from p, the marginal of the other parties is the same: summing P(s, x) over the outcome a of p, with x[p := a] the string x with a at p, gives the same value for s and t.",
                "IsNSBox", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hardy", "The relaxed Hardy conditions", HardyFormula(),
                "The outcome value 0 stands for the paper's outcome 1 and the value d - 1 for its outcome d. With all inputs u, all outcomes 1 have probability q > 0. With v at party r only, every outcome string with 1 at the other parties and a value other than d at r has probability 0. For one fixed party j and every i other than j, with v at i and j, the outcome string with d at i and j and 1 elsewhere has probability 0. In the display an input string is written as the set of parties with input v: the empty set for all inputs u, {r} for v at r only, {i, j} for v at i and j (in Lean the maps k |-> false, k |-> decide (k = r) and k |-> decide (k = i or k = j)).",
                "RelaxedHardy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every number N >= 3 of parties, every common number d >= 2 of outcomes and every epsilon > 0, some no-signalling box satisfies the relaxed Hardy conditions with success probability q > 1/3 - epsilon. The paper conjectures that the optimal success probability is 1/3 for any dimension and any number of parties, which implies this whether the optimum is read as a maximum or a supremum; requiring N >= 3 and a common d only weakens the claim, and the fixed party j may be chosen.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "At most 1/4 for four parties", Disp(new Formula.Not(F.Id("claim"))),
                "Take N = 4, d = 2 and a box with success probability q. Let m_r be the probability of 1 at all parties other than r under the inputs u. No-signalling at r and the second condition give probability m_r to the outcome d at r and 1 elsewhere under S_r. For i other than j, no-signalling at j, the third condition and nonnegativity give the outcome d at i and 1 elsewhere probability at least m_i under S_ij, and symmetrically for j. No-signalling at i and at j moves the marginal of the remaining parties back to the inputs u, so the outcome d at i and j with 1 elsewhere has probability at least q under u. These three outcome strings and the all-1 string are distinct, so normalization gives 4 q <= 1, and q > 1/3 - 1/12 = 1/4 is impossible. In Lean the four choices of j are split, and in each case the instantiated equalities and inequalities are combined by linarith.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhattacharya-2015-relaxed-hardy-no-signalling-optimum"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("relaxedhardy-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Prob(Formula s, Formula x) => Call(F.Id("P"), s, x);
    private static Formula Update(Formula x, Formula p, Formula a) =>
        Seq(x, OpenBracket, p, Sp, Colon, Eq, Sp, a, CloseBracket);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index), Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Inputs(Formula n) => Arrow(Fin(n), Named(F.Id("Bool")));
    private static Formula Outcomes(Formula n, Formula d) => Arrow(Fin(n), Fin(d));
    private static Formula BoxType(Formula n, Formula d) =>
        Arrow(Parenthesized(Inputs(n)), Arrow(Parenthesized(Outcomes(n, d)), Real()));
    private static Formula Last(Formula d) => Seq(d, F.Minus, D(1));
    private static Formula Set(params Formula[] items)
    {
        Formula[] parts = new Formula[items.Length * 2 + 1];
        parts[0] = OpenBrace;
        for (int k = 0; k < items.Length; k++)
        {
            parts[2 * k + 1] = items[k];
            parts[2 * k + 2] = k + 1 < items.Length ? Seq(Comma, Sp) : CloseBrace;
        }
        return Seq(parts);
    }

    private static Formula Definition(Formula name, Formula n, Formula d, Formula body, params Formula[] extra)
    {
        Formula p = F.Id("P");
        Formula head = Call(name, [n, d, p, .. extra]);
        Formula inner = Iff(head, body);
        foreach (Formula q in extra) inner = All(q, Real(), inner);
        return Disp(All(n, Nat(), All(d, Nat(), All(p, BoxType(n, d), inner))));
    }

    private static Formula BoxFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), p = F.Id("p"), s = F.Id("s"), t = F.Id("t");
        Formula x = F.Id("x"), a = F.Id("a"), k = F.Id("k");
        Formula nonneg = All(s, Inputs(n), All(x, Outcomes(n, d), Le(D(0), Prob(s, x))));
        Formula normalized = All(s, Inputs(n), Equal(SumOver(x, Prob(s, x)), D(1)));
        Formula agree = All(k, Fin(n), Implies(NotEqual(k, p), Equal(Sub(s, k), Sub(t, k))));
        Formula marginal = Equal(SumOver(a, Prob(s, Update(x, p, a))),
            SumOver(a, Prob(t, Update(x, p, a))));
        Formula signalling = All(p, Fin(n), All(s, Inputs(n), All(t, Inputs(n),
            Implies(Parenthesized(agree), All(x, Outcomes(n, d), marginal)))));
        return Definition(F.Id("IsNSBox"), n, d, And(nonneg, And(normalized, signalling)));
    }

    private static Formula HardyFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), q = F.Id("q"), r = F.Id("r"), i = F.Id("i"), j = F.Id("j");
        Formula x = F.Id("x"), k = F.Id("k");
        Formula first = And(Lt(D(0), q), All(x, Outcomes(n, d),
            Implies(Parenthesized(All(k, Fin(n), Equal(Sub(x, k), D(0)))), Equal(Prob(Emptyset, x), q))));
        Formula second = All(r, Fin(n), All(x, Outcomes(n, d),
            Implies(Parenthesized(All(k, Fin(n), Implies(NotEqual(k, r), Equal(Sub(x, k), D(0))))),
                Implies(NotEqual(Sub(x, r), Last(d)), Equal(Prob(Set(r), x), D(0))))));
        Formula rest = All(k, Fin(n), Implies(Parenthesized(And(NotEqual(k, i), NotEqual(k, j))),
            Equal(Sub(x, k), D(0))));
        Formula third = Some(j, Fin(n), All(i, Fin(n), Implies(NotEqual(i, j), All(x, Outcomes(n, d),
            Implies(Parenthesized(And(Equal(Sub(x, i), Last(d)), And(Equal(Sub(x, j), Last(d)), rest))),
                Equal(Prob(Set(i, j), x), D(0)))))));
        return Definition(F.Id("RelaxedHardy"), n, d, And(first, And(second, third)), q);
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), q = F.Id("q"), p = F.Id("P"), eps = Varepsilon;
        Formula feasible = And(Call(F.Id("IsNSBox"), n, d, p),
            And(Call(F.Id("RelaxedHardy"), n, d, p, q),
                Lt(new Formula.Binary(new Formula.Fraction(D(1), D(3)), FormulaBinaryOperator.Subtract, eps), q)));
        Formula body = All(n, Nat(), All(d, Nat(), Implies(Le(D(3), n), Implies(Le(D(2), d),
            All(eps, Real(), Implies(Lt(D(0), eps),
                Some(p, BoxType(n, d), Some(q, Real(), feasible))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
