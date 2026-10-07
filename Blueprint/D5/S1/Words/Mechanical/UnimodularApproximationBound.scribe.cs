using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class UnimodularApproximationBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unimodular pair with opposite approximation errors excludes smaller denominators.",
        H("Opposite errors and smaller denominators"),
        Blocks(Describe.Lean(
            DescribeId.Create("unimodular-opposite-error-bound"),
            DeclarationHandle.Create(
                "D5/S1/Words/Mechanical/UnimodularApproximationBound.unimodular_opposite_error_bound"),
            H("The opposite error is a uniform lower bound"),
            StatementSource.FromAuthor(BoundFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let q,p and s,r be integer pairs with determinant qr-ps=1 and positive "
                + "denominators. If their errors at a real slope alpha are d and -e, with "
                + "d,e positive, every positive integer denominator m below q has error "
                + "at least e against every integer numerator z. Integer quantities in the "
                + "two error equations and conclusion are coerced to real numbers.")),
                Paragraph(Text(
                    "The determinant gives integer coordinates a,b with m=aq+bs and z=ap+br. "
                    + "The inequalities 0<m<q force either a positive and b negative, or "
                    + "a nonpositive and b positive. In both cases the absolute error "
                    + "ad-be is at least e."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unimodular-gap-error-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/UnimodularApproximationBound.unimodular_gap_error_bound"),
                H("Every other denominator in the gap has larger error"),
                StatementSource.FromAuthor(GapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume in addition that 0<s<q and e is at least twice d. "
                    + "For q≤m<2q+s, excluding q, 2q and q+s raises the lower bound to d+e. "
                    + "Integer quantities in real error equations are coerced to real numbers. "
                    + "The integer coordinate b is either negative, at least two, zero or one. "
                    + "The first two cases give the error estimate; the last two force one "
                    + "of the three excluded denominators."))),
                DescribeRole.Theorem)), []));

    private static Formula BoundFormula()
    {
        Formula q = F.Id("q"), p = F.Id("p"), s = F.Id("s"), r = F.Id("r");
        Formula m = F.Id("m"), z = F.Id("z"), alpha = F.Id("alpha");
        Formula d = F.Id("d"), e = F.Id("e");
        Formula assumptions = And(Lt(D(0), q), And(Lt(D(0), s), And(Lt(D(0), m),
            And(Lt(m, q), And(Eq(Sub(Mul(q, r), Mul(p, s)), D(1)),
                And(Lt(D(0), d), And(Lt(D(0), e),
                    And(Eq(Sub(Mul(R(q), alpha), R(p)), d),
                        Eq(Sub(Mul(R(s), alpha), R(r)), new Formula.Negate(e))))))))));
        Formula body = new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            new Formula.Relation(e, FormulaRelationOperator.LessThanOrEqual,
                new Formula.Absolute(Sub(Mul(R(m), alpha), R(z)))));
        foreach (string name in new[] { "e", "d", "alpha" })
            body = All(name, Seq(Mathbb, Grp(F.Id("R"))), body);
        foreach (string name in new[] { "z", "m", "r", "s", "p", "q" })
            body = All(name, new Formula.Integers(), body);
        return Disp(body);
    }
    private static Formula GapFormula()
    {
        Formula q = F.Id("q"), p = F.Id("p"), s = F.Id("s"), r = F.Id("r");
        Formula m = F.Id("m"), z = F.Id("z"), alpha = F.Id("alpha");
        Formula d = F.Id("d"), e = F.Id("e");
        Formula assumptions = And(Lt(D(0), q), And(Lt(D(0), s), And(Lt(s, q),
            And(Le(q, m), And(Lt(m, Add(Mul(D(2), q), s)),
                And(Ne(m, q), And(Ne(m, Mul(D(2), q)), And(Ne(m, Add(q, s)),
                    And(Eq(Sub(Mul(q, r), Mul(p, s)), D(1)), And(Lt(D(0), d),
                        And(Le(Mul(D(2), d), e), And(Eq(Sub(Mul(R(q), alpha), R(p)), d),
                            Eq(Sub(Mul(R(s), alpha), R(r)), new Formula.Negate(e))))))))))))));
        Formula body = new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            Le(Add(d, e), new Formula.Absolute(Sub(Mul(R(m), alpha), R(z)))));
        foreach (string name in new[] { "e", "d", "alpha" })
            body = All(name, Seq(Mathbb, Grp(F.Id("R"))), body);
        foreach (string name in new[] { "z", "m", "r", "s", "p", "q" })
            body = All(name, new Formula.Integers(), body);
        return Disp(body);
    }
    private static Formula R(Formula x) => Seq(Operatorname, Grp(F.Id("real")), Parenthesized(x));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
