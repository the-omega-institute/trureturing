using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtLaurentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The principal part of the complete Mangoldt transform at each zeta zero",
        H("The local Laurent expansion of the Mangoldt transform"),
        Blocks(
            Describe.Lean(DescribeId.Create("transform"), DeclarationHandle.Create(Module + "transform"),
                H("The explicit transform"), StatementSource.FromAuthor(Definition()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The correction terms come from the logarithmic and linear terms of the inclusive remainder U."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("principal-part"),
                DeclarationHandle.Create(Module + "transform_integral_and_zero_germs"),
                H("The transform on the half-plane and its zero germs"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On Re(s)>1 the complete half-plane transform theorem gives the "
                        + "absolutely convergent integral. At a zero z, the expansion concerns the explicit "
                        + "transform function. Since ζ(0)=−1/2, zero is excluded. Classically ζ has a pole at 1. "
                        + "Lean assigns ζ(1) a nonzero value, so the zero hypothesis excludes 1 as well.")),
                    Paragraph(Text("Write ζ(s)=(s−z)ᵐu(s) near z, where u is analytic and u(z) is nonzero. "
                        + "Its logarithmic derivative splits as m/(s−z)+u′(s)/u(s). With d(s)=s(1−s), "
                        + "the identity d(z)−d(s)=(s−z)(s+z−1) absorbs exactly the varying denominator. "
                        + "The analytic remainder is m(s+z−1)/(d(s)d(z))+(u′(s)/u(s))/d(s) "
                        + "−1/(s−1)²+(1+γ)/(s−1). The residue m/d(z) is nonzero even at a multiple zero."))),
                DescribeRole.Theorem))));

    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula More(string name, Formula type, Formula body, bool exists = false) =>
        new Formula.Bind(exists ? FormulaQuantifier.Exists : FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Nonzero(Formula a) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, F.D(0));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula If(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Phi(Formula s) => Call("transform", s);

    private static Formula Definition()
    {
        var s = F.Id("s");
        var shift = Subtract(s, F.D(1));
        var logDerivative = Frac(new Formula.Negate(new Formula.Apply(F.Seq(F.Zeta, F.Apos), [s])),
            new Formula.Apply(F.Zeta, [s]));
        var correction = Frac(F.D(1), F.Seq(F.Open, shift, F.Close, F.Caret, F.Grp(F.D(2))));
        return F.Disp(More("s", Complex, Equal(Phi(s), Add(Subtract(Frac(logDerivative, Multiply(s, shift)), correction),
            Frac(Add(F.D(1), F.GammaLower), shift)))));
    }

    private static Formula Claim()
    {
        var y = F.Id("y");
        var s = F.Id("s");
        var rho = F.Id("z");
        var radius = F.Id("r");
        var order = Call("analyticOrderNatAt", F.Zeta, rho);
        var residue = Frac(order, Multiply(rho, Subtract(F.D(1), rho)));
        var body = Multiply(Call("exp", new Formula.Negate(Multiply(s, y))), Call("U", Call("exp", y)));
        var function = F.Seq(F.Open, F.LambdaLower, F.Sp, y, F.Sp, F.Mapsto, F.Sp, body, F.Close);
        var integral = F.Seq(F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(F.Infty),
            F.Sp, body, F.Sp, F.Id("d"), y);
        var halfPlane = More("s", Complex, If(Less(F.D(1), Call("Re",s)),
            And(Call("IntegrableOn", function, Call("Ioi",F.D(0))), Equal(integral, Phi(s)))));
        var distance = new Formula.Absolute(Subtract(s, rho));
        var equality = Equal(Phi(s), Add(Frac(residue, Subtract(s, rho)), Call("H", s)));
        var punctured = More("r", Real, And(Less(F.D(0), radius),
            More("s", Complex, If(And(Nonzero(distance), Less(distance, radius)), equality))), exists: true);
        var holomorphic = More("H", F.Seq(Complex,F.Sp,F.To,F.Sp,Complex),
            And(Call("AnalyticAt", Complex, F.Id("H"), rho), punctured), exists: true);
        var local = More("z", Complex, If(Equal(new Formula.Apply(F.Zeta,[rho]), F.D(0)),
            And(Nonzero(order), And(Nonzero(residue), holomorphic))));
        return F.Disp(And(halfPlane, local));
    }
}
