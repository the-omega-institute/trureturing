using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class ParameterClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/XuYangMillsRemainder/ParameterClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both sign classifications for the Gaussian Mills remainder at every truncation order.",
        H("Parameter thresholds for the original Mills remainder"), Blocks(
            Entry("B", All("j", N, Eq(C("B", V("j")), UnitIntegral("v",
                Mul(Pow(V("v"), Num(2)), Pow(Add(Num(1), Pow(V("v"), Num(2))), V("j")))))),
                "The second polynomial moment is integrated over the unit interval. The companion zeroth moment is Result.intPow. Both are finite, and the second moment is strictly between zero and the zeroth moment.", DescribeRole.Definition),
            Entry("theta", All("j", N, Eq(C("theta", V("j")),
                Div(Sub(Num(1), Div(C("Result.intPow", V("j")), C("B", V("j")))), Num(2)))),
                "The threshold uses the ratio of the zeroth polynomial moment to the second polynomial moment. Its denominator is strictly positive at every natural order.", DescribeRole.Definition),
            Entry("result", All("n", N, Imp(Le(Num(2), V("n")), All("a", R,
                And(And(Iff(Sign(false), CM(false)), Iff(CM(false), Le(V("a"), C("theta", Sub(V("n"), Num(2)))))),
                    And(Iff(Sign(true), CM(true)), Iff(CM(true), Le(C("theta", Sub(V("n"), Num(1))), V("a")))))))),
                "For every truncation order n at least two and every real a, global nonnegativity of the signed original remainder is equivalent to complete monotonicity and to the lower parameter range. The same equivalences for its negative give the upper parameter range. Both endpoints are included. Result.D uses the Gaussian tail Result.millsRatio, the original Gamma coefficients Result.u and the finite sum from one through n, with b equal to a minus two. Complete monotonicity includes smoothness and every derivative order, including zero. The weighted Taylor moments bound the signed Laplace density. Its polynomial envelope permits all Laplace derivatives. Clearing the finite remainder at zero proves the lower parameter restriction; the next remainder and its polynomial Laplace bound give the leading coefficient at infinity and the upper restriction.", DescribeRole.Theorem)
        )));

    private static Formula Native => Mul(Pow(new Formula.Negate(Num(1)), V("n")), C("Result.D", V("n"), V("x"), V("a")));
    private static Formula Value(bool negative) => negative ? new Formula.Negate(Native) : Native;
    private static Formula Sign(bool negative) => All("x", R, Imp(Lt(Num(0), V("x")), Le(Num(0), Value(negative))));
    private static Formula CM(bool negative) => C("Result.CompletelyMonotoneOn", Seq(V("x"), Colon, Sp, R, Mapsto, Sp, Value(negative)));
    private static DocumentBlock Entry(string name, Formula statement, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("mills-parameter-" + name), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(int n) => new Formula.Number(n);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula UnitIntegral(string n, Formula body) => C("intervalIntegral", Seq(V(n), Colon, Sp, R, Mapsto, Sp, body), Num(0), Num(1), C("volume"));
}
