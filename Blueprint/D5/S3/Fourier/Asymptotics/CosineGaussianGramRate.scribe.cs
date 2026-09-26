using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineGaussianGramRateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineGaussianGramRate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian weighting approximates the cosine-integral Gram integral with an explicit inverse-radius error.",
        H("Gaussian Weighting of the Cosine-Integral Gram Product"),
        Blocks(Describe.Lean(
            DescribeId.Create("gaussian-cosine-integral-gram-error"),
            DeclarationHandle.Create(Module + "result"),
            H("An error bound for all positive scales and radii"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a, b, beta and R be arbitrary positive real numbers. The product "
                    + "Ci(a|z|)Ci(b|z|) multiplied by exp(-beta(z/R)^2) is Lebesgue "
                    + "integrable on the real line. Its integral differs from pi/max(a,b) "
                    + "by at most 8(beta+1)/(abR). Here Ci is the real cosine integral "
                    + "defined at positive x by sin(x)/x minus the integral of sin(t)/t^2 "
                    + "from x to infinity."),
                    Ref("D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral")),
                Paragraph(Text(
                    "The unweighted product is integrable and has integral pi/max(a,b). "
                    + "Since the Gaussian factor is continuous and lies between zero and "
                    + "one, multiplication by it preserves integrability."),
                    Ref("D5/S3/Fourier/Asymptotics/CosineIntegralGram.result")),
                Paragraph(Text(
                    "For every x>0, the sine-tail representation gives |Ci(x)|<=2/x: "
                    + "the first term has absolute value at most 1/x, and the integral "
                    + "of t^(-2) from x to infinity is 1/x. Consequently the absolute "
                    + "value of the product at z different from zero is at most 4/(abz^2).")),
                Paragraph(Text(
                    "For u>=0 the Gaussian decrement satisfies "
                    + "0<=1-exp(-u)<=min(u,1). On the interval |z|<=R, the absolute "
                    + "error integrand is therefore at most 4beta/(abR^2), except at "
                    + "the null singleton zero. Outside that interval it is at most "
                    + "4/(abz^2). The two integrated bounds are 8beta/(abR) and "
                    + "8/(abR), respectively, yielding the stated estimate.")),
                Paragraph(Text(
                    "If a and b range over compact subsets of the positive real axis "
                    + "and beta remains bounded above, the displayed constant is "
                    + "uniform. Thus the approximation error is uniformly O(1/R). "
                    + "This statement concerns deterministic Lebesgue integrals."))),
            DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Positive(Formula x) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, x);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Lambda(string name, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, F.Sp, Reals, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula Integral(Formula variable, Formula integrand) =>
        F.Seq(F.Int, F.Underscore, F.Grp(Reals), F.Sp, integrand,
            F.Sp, F.Id("d"), variable);

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), beta = F.Id("beta"),
            radius = F.Id("R"), z = F.Id("z");
        Formula product = Multiply(Call("Ci", Multiply(a, new Formula.Absolute(z))),
            Call("Ci", Multiply(b, new Formula.Absolute(z))));
        Formula exponent = F.Seq(F.Minus, Multiply(beta,
            new Formula.Power(new Formula.Fraction(z, radius), F.D(2))));
        Formula weighted = Multiply(product, Call("exp", exponent));
        Formula difference = F.Seq(Integral(z, weighted), F.Minus,
            new Formula.Fraction(F.Pi, Call("max", a, b)));
        Formula bound = new Formula.Fraction(
            Multiply(F.D(8), F.Grp(F.Seq(beta, F.Plus, F.D(1)))),
            Multiply(Multiply(a, b), radius));
        Formula statement = And(Call("Integrable", Lambda("z", weighted)),
            new Formula.Relation(new Formula.Absolute(difference),
                FormulaRelationOperator.LessThanOrEqual, bound));
        Formula positive = And(And(Positive(a), Positive(b)),
            And(Positive(beta), Positive(radius)));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("a"), Reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("b"), Reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("beta"), Reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("R"), Reals)],
            new Formula.Logic(positive, FormulaLogicOperator.Implies, statement)));
    }
}
