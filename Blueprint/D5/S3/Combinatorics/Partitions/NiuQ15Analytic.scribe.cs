using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuQ15AnalyticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuQ15Analytic.";

    public DocumentDefinition Create()
    {
        var k = V("k");
        var n = V("n");
        var r = V("r");
        var j = V("j");
        var point = V("point");
        var coefficient = Call("tailCoefficient", k, r);
        var tail = Call("finiteTail", k, n, r);
        var limit = Call("limitTail", k, r);
        var mass = Call("limitMass", k, r);
        var rowPower = Pow(Cast(k), r);
        var range = Call("range", r);
        var factor = new Formula.Fraction(Subtract(Cast(n), Cast(j)),
            Subtract(Multiply(Cast(k), Cast(n)), Cast(j)));
        var pointType = new Formula.TypeArrow(NatType(), new Formula.TypeArrow(NatType(), RealType()));
        var nextTail = Call("finiteTail", k, n, Add(r, D(1)));
        var pointPartition = All("n", NatType(), Imp(Lt(D(0), n), All("r", NatType(),
            Equal(tail, Add(Apply(point, n, r), nextTail)))));
        var alternating = Call("tsum",
            LambdaOf(r, Multiply(Pow(Parenthesized(Seq(Minus, D(1))), r), tail)));
        var evenSum = Indexed(Sum, r, Call("range", Add(n, D(1))),
            IfThenElse(Call("Even", r), Apply(point, n, r), D(0)));
        var factorialRatio = Multiply(Cast(coefficient), new Formula.Fraction(
            Cast(Call("descFactorial", n, r)), Cast(Call("descFactorial", Multiply(k, n), r))));
        var parityLimit = Pow(Parenthesized(new Formula.Fraction(Cast(k), Add(Cast(k), D(1)))), k);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite tails, normalized point limits and alternating sums for rectangular tableaux.",
            H("Limits of the Rectangle Tail and Point Laws"),
            Blocks(
                Def("tailCoefficient", "Binomial coefficient",
                    Equal(coefficient, Call("choose", Add(r, Parenthesized(Subtract(k, D(1)))), Subtract(k, D(1)))),
                    "The inputs and both subtractions are in the natural numbers."),
                Def("finiteTail", "Finite survival function",
                    Equal(tail, IfThenElse(AtMost(r, n),
                        Multiply(Cast(coefficient), Indexed(Prod, j, range, factor)), D(0))),
                    "The product is over j from zero through r − 1, and is one for r = 0. The ratios are in the real numbers."),
                Def("limitTail", "Limiting survival function",
                    Equal(limit, new Formula.Fraction(Cast(coefficient), rowPower)),
                    "This is the defining product of the cast coefficient and the rth power of the reciprocal of k. Division is the total real division used in Lean."),
                Def("limitMass", "Limiting point mass",
                    Equal(mass, new Formula.Fraction(Multiply(Cast(r), Cast(Call("choose",
                        Add(r, Parenthesized(Subtract(k, D(1)))), Subtract(k, D(2))))),
                        Pow(Cast(k), Add(r, D(1))))),
                    "The binomial coefficient is evaluated in the naturals before casting it to the reals."),
                Thm("finiteTail_above", "Survival above the width",
                    All("k", NatType(), All("n", NatType(), All("r", NatType(),
                        Imp(Lt(n, r), Equal(tail, D(0)))))),
                    "The guard selects the zero branch of finiteTail."),
                Thm("finiteTail_eq_descFactorial", "Finite survival as a factorial ratio",
                    All("k", NatType(), All("n", NatType(), All("r", NatType(),
                        Imp(AtMost(D(2), k), Imp(AtMost(r, n), Equal(tail, factorialRatio)))))),
                    "Both descending factorials are formed in the naturals and then cast to the reals. The formula includes zero width with r = 0."),
                Thm("tendsto_finiteTail", "Pointwise convergence of survival probabilities",
                    WithRows(k, All("r", NatType(), TendstoTo(LambdaOf(n, tail), limit))),
                    "For fixed threshold the finite product contains a fixed number of factors, each tending to the reciprocal of k."),
                Thm("tendsto_point", "Convergence of the point masses",
                    WithRows(k, All("point", pointType, Imp(Parenthesized(pointPartition),
                        All("r", NatType(), TendstoTo(LambdaOf(n, Apply(point, n, r)), mass))))),
                    "The hypothesis supplies the tail partition at each positive width. Subtract adjacent tails, take their limits, and simplify the binomial difference."),
                Thm("hasSum_limitMass", "Normalization of the point masses",
                    WithRows(k, Call("HasSum", Call("limitMass", k), D(1))),
                    "Adjacent limiting tails telescope from one to zero."),
                Thm("sum_even_point_eq_alternating", "Even indices as an alternating tail sum",
                    All("k", NatType(), All("point", pointType, Imp(Parenthesized(pointPartition),
                        All("n", NatType(), Imp(Lt(D(0), n), Equal(evenSum, alternating)))))),
                    "Pair a tail at each even threshold with the following tail. All tails beyond the width vanish."),
                Thm("tendsto_alternating_finiteTail", "Limit of the alternating tail sum",
                    WithRows(k, TendstoTo(LambdaOf(n, alternating), parityLimit)),
                    "A geometric bound independent of k and n gives dominated convergence. The alternating binomial series at −1/k evaluates the limit.")
            ), []));
    }

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("niuq15analytic-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value) => Call("cast", value);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula WithRows(Formula k, Formula body) => All("k", NatType(), Imp(AtMost(D(2), k), body));
    private static Formula LambdaOf(Formula x, Formula body) =>
        Parenthesized(Seq(x, Colon, Sp, NatType(), Sp, Mapsto, Sp, body));
    private static Formula IfThenElse(Formula test, Formula yes, Formula no) => Call("ite", test, yes, no);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Indexed(Formula op, Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(op, Seq(index, Sp, InMacro, Sp, domain)), Sp, body);
    private static Formula TendstoTo(Formula sequence, Formula limit) =>
        Call("Tendsto", sequence, V("atTop"), Call("nhds", limit));
}
