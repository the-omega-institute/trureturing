using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerCollisionCoefficientDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict increase of the ratio of leading LCM power coefficients.",
        H("Leading coefficients and parameter comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("collision-coefficient"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.coefficient"),
                H("Leading coefficient"),
                StatementSource.FromAuthor(CoefficientDefinition()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For real kappa and x define c(kappa,x) by the displayed formula. "
                    + "On kappa>1 and x>1 it is positive. It is the leading coefficient "
                    + "in the large-exponent limit of the LCM power threshold from Definition 4.2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("collision-coefficient-positive"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.coefficient_pos"),
                H("Positivity"),
                StatementSource.FromAuthor(Positivity()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If kappa>1 and x>1, every factor in the defining numerator and "
                    + "denominator is strictly positive. This fact is used in the logarithmic "
                    + "derivative, the leading-term limit, and the comparison at interval endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collision-coefficient-ratio-monotone"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient.log_coefficient_ratio_strictMono"),
                H("Strict parameter comparison"),
                StatementSource.FromAuthor(RatioComparison()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For all real bases 1<p<q, the function kappa -> log(c(kappa,p)/c(kappa,q)) "
                        + "is strictly increasing on kappa>1. No primality assumption is needed.")),
                    Paragraph(Text(
                        "Put s=log(x). The logarithmic derivative in kappa is "
                        + "s/(exp((kappa-1)*s)-1)-s/(exp(kappa*s)-1). "
                        + "The function z/sinh(z) strictly decreases for z>0, since "
                        + "z*cosh(z)-sinh(z) has derivative z*sinh(z)>0 and vanishes at zero. "
                        + "Consequently (s/(2*sinh(v*s/2)))^2 strictly decreases in s for v>0. "
                        + "For s<t, differentiating s/(exp(v*s)-1)-t/(exp(v*t)-1) "
                        + "in v therefore gives a strictly negative derivative. Its value at "
                        + "kappa-1 exceeds its value at kappa. This difference is exactly the "
                        + "derivative of the logarithmic coefficient ratio, proving the claim."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Seq(Open, a, Close), b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);

    private static Formula CoefficientDefinition()
    {
        var k = F.Id("kappa"); var x = F.Id("x");
        return Disp(All("kappa", Real, All("x", Real,
            Rel(Call("c", k, x), FormulaRelationOperator.Equal,
                Div(Multiply(Subtract(x, D(1)), Subtract(Pow(x, Subtract(k, D(1))), D(1))),
                    Multiply(Subtract(Pow(x, k), D(1)), Call("log", x)))))));
    }

    private static Formula Positivity()
    {
        var k = F.Id("kappa"); var x = F.Id("x");
        return Disp(All("kappa", Real, All("x", Real,
            Implies(And(Lt(D(1), k), Lt(D(1), x)), Lt(D(0), Call("c", k, x))))));
    }

    private static Formula RatioComparison()
    {
        var p = F.Id("p"); var q = F.Id("q");
        var a = F.Id("alpha"); var b = F.Id("beta");
        return Disp(All("p", Real, All("q", Real, All("alpha", Real, All("beta", Real,
            Implies(And(And(Lt(D(1), p), Lt(p, q)), And(Lt(D(1), a), Lt(a, b))),
                Lt(Call("log", Div(Call("c", a, p), Call("c", a, q))),
                   Call("log", Div(Call("c", b, p), Call("c", b, q))))))))));
    }
}
