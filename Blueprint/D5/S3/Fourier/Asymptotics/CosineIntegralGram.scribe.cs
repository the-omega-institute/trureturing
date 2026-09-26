using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineIntegralGramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineIntegralGram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive dilations of the real cosine-integral tail have an absolutely integrable product and an exact Gram integral.",
        H("The Cosine-Integral Gram Integral"),
        Blocks(Describe.Lean(
            DescribeId.Create("cosine-integral-product-integrability-and-mass"),
            DeclarationHandle.Create(Module + "result"),
            H("All positive scales, including equal scales"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every pair of positive real numbers a and b, the product "
                    + "Ci(a|z|)Ci(b|z|) is Lebesgue integrable on the real line and its "
                    + "integral is pi/max(a,b). In particular, the square at scale a "
                    + "has integral pi/a. Ci is the existing real cosine integral, "
                    + "defined for positive x as sin(x)/x minus the absolutely "
                    + "convergent integral of sin(t)/t^2 from x to infinity."),
                    Ref("D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral")),
                Paragraph(Text(
                    "On the positive half-line set S(x)=sinc(x) and T(x)=Ci(x)-S(x). "
                    + "The sine-tail representation and the fundamental theorem of calculus "
                    + "give T'(x)=S(x)/x. Consequently B(x)=x T(ax)T(bx) has derivative "
                    + "Ci(ax)Ci(bx)-S(ax)S(bx).")),
                Paragraph(Text(
                    "The tail is bounded by 1/x. Near zero, the normalized finite "
                    + "cosine-sum estimate at N=1 gives |Ci(x)|<=1+2K+|log(x)| "
                    + "for one K>0 and 0<x<=1. Thus sqrt(x)T(x) tends to zero. "
                    + "These estimates show that B tends to zero at both endpoints "
                    + "of the positive half-line."),
                    Ref("D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.result")),
                Paragraph(Text(
                    "Add the integral of S(at)S(bt) from zero to x to B(x), obtaining "
                    + "a primitive P with derivative Ci(ax)Ci(bx). For a=b this derivative "
                    + "is nonnegative. The finite limit of P at infinity and continuity "
                    + "at zero therefore establish square integrability by the nonnegative "
                    + "form of the fundamental theorem of calculus. The L2 product inequality "
                    + "then establishes integrability for arbitrary a and b, allowing the "
                    + "same primitive to transfer the integral to the sinc product.")),
                Paragraph(Text(
                    "The existing integral of (sin(x)/x)^2 is pi. Scaling gives the "
                    + "integral of (sin(cx)/x)^2 as pi|c|, with c=0 treated directly. "
                    + "Put p=(a+b)/2 and q=(a-b)/2. The sine-product identity expresses "
                    + "S(ax)S(bx), away from zero, as the difference of the squared "
                    + "sine quotients at p and q divided by ab. Its integral is therefore "
                    + "pi(p-|q|)/(ab)=pi/max(a,b). Reflection transfers the positive "
                    + "half-line calculation to the real line; the singleton at zero "
                    + "has Lebesgue measure zero."))),
            DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Positive(Formula x) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, x);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Lambda(string name, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, F.Sp, domain, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula Integral(Formula variable, Formula integrand) =>
        F.Seq(F.Int, F.Underscore, F.Grp(Reals), F.Sp, integrand,
            F.Sp, F.Id("d"), variable);

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), z = F.Id("z");
        Formula product = Multiply(Call("Ci", Multiply(a, new Formula.Absolute(z))),
            Call("Ci", Multiply(b, new Formula.Absolute(z))));
        Formula statement = And(Call("Integrable", Lambda("z", Reals, product)),
            Equal(Integral(z, product), new Formula.Fraction(F.Pi, Call("max", a, b))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("a"), Reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("b"), Reals)],
            new Formula.Logic(And(Positive(a), Positive(b)), FormulaLogicOperator.Implies, statement)));
    }
}
