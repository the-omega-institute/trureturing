using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic binomial estimate controls the counting bases and averages of replicated graph families.",
        H("Replicated dominating-set averages"),
        Blocks(
            Node("replication-obstruction", "Finite replication obstruction", "replication_obstruction",
                ObstructionFormula(),
                "Write r=4hb²+2. For a>b≥1, the ratio a/b is at least 1+1/b. "
                    + "Its r-th power is at least 1+r/b+r(r−1)/(2b²), whose excess above "
                    + "1+2rh is r/b+r/(2b²)>0."),
            Node("counting-base-comparison", "Comparison of counting bases", "counting_base_le",
                BaseFormula(),
                "If a^r≤b^r(1+2rh) for every nonnegative integer r and b>0, then a≤b. "
                    + "The displayed finite replication count excludes the opposite inequality."),
            Node("strict-replicated-mean", "Strict inequality for unequal families", "replicated_mean_lt",
                MeanFormula(),
                "Suppose β≥0 and the replicated global bounds hold. If α≥2h/3, "
                    + "their left factors are at least one, and their right factors are at most "
                    + "1+2rh. This contradicts a>b, so α<2h/3."),
            Describe.Lean(DescribeId.Create("relaxed-mean-bound"),
                DeclarationHandle.Create(Prefix + "relaxed_mean_bound"),
                H("Bound and counting equality for relaxed means"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For naturals a,b,h and rational means α,β, assume b>0, "
                    + "b≤a, 0≤β≤2h/3, a=b implies α=β, and the replicated global inequalities "
                    + "hold for every nonnegative integer r. Then α≤2h/3, and α=2h/3 implies a=b."))),
                DescribeRole.Theorem),
            Node("stem-split-bound", "Numerical bound and equality in the stem split", "stem_split_bound",
                SplitFormula(),
                "For n=h+l+1, l≥1 and α≤2h/3, the stem-conditioned mean "
                    + "1+l/2+α is at most (4n+1)/6. Equality holds exactly when "
                    + "l=1 and α=2h/3.")), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Rat() => new Formula.NamedConstant(FormulaIdentifier.Create("Rat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Cast(Formula x) => Call("rat", x);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) =>
        new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => Call("pow", x, y);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Envelope(Formula a, Formula b, Formula h, Formula r) =>
        Le(Pow(Cast(a), r), Mul(Pow(Cast(b), r),
            Add(D(1), Mul(Mul(D(2), Cast(r)), Cast(h)))));
    private static Formula Replications(Formula b, Formula h) =>
        Add(Mul(Mul(D(4), h), Pow(b, D(2))), D(2));

    private static Formula ObstructionFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var h = F.Id("h");
        return Disp(All("a", Nat(), All("b", Nat(), All("h", Nat(),
            Imp(Lt(D(0), b), Imp(Lt(b, a),
                new Formula.Not(Envelope(a, b, h, Replications(b, h)))))))));
    }

    private static Formula BaseFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var h = F.Id("h"); var r = F.Id("r");
        return Disp(All("a", Nat(), All("b", Nat(), All("h", Nat(),
            Imp(Lt(D(0), b), Imp(All("r", Nat(), Envelope(a, b, h, r)), Le(a, b)))))));
    }

    private static Formula MeanFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var h = F.Id("h");
        var alpha = F.Id("alpha"); var beta = F.Id("beta"); var r = F.Id("r");
        var c = Div(Mul(D(2), Cast(h)), D(3));
        var global = Le(
            Mul(Pow(Cast(a), r), Add(D(1), Mul(Mul(D(6), Cast(r)), Sub(alpha, c)))),
            Mul(Pow(Cast(b), r), Add(D(1), Mul(Mul(D(3), Cast(r)), Sub(c, beta)))));
        return Disp(All("a", Nat(), All("b", Nat(), All("h", Nat(),
            All("alpha", Rat(), All("beta", Rat(),
                Imp(Lt(D(0), b), Imp(Lt(b, a), Imp(Le(D(0), beta),
                    Imp(All("r", Nat(), global), Lt(alpha, c)))))))))));
    }

    private static Formula SplitFormula()
    {
        var n = F.Id("n"); var l = F.Id("l"); var h = F.Id("h"); var alpha = F.Id("alpha");
        var c = Div(Mul(D(2), Cast(h)), D(3));
        var mean = Add(Add(D(1), Div(Cast(l), D(2))), alpha);
        var bound = Div(Add(Mul(D(4), Cast(n)), D(1)), D(6));
        var conclusion = And(Le(mean, bound),
            Iff(Eq(mean, bound), And(Eq(l, D(1)), Eq(alpha, c))));
        var body = Imp(Eq(n, Add(Add(h, l), D(1))),
            Imp(Le(D(1), l), Imp(Le(alpha, c), conclusion)));
        return Disp(All("n", Nat(), All("l", Nat(), All("h", Nat(), All("alpha", Rat(), body)))));
    }
}
