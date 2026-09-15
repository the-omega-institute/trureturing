using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class DyadicComplexDecayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fourier-Laplace transform of the dyadic convolution density has "
            + "inverse-power decay of every natural order, with an explicit finite "
            + "constant and exponential growth controlled by the imaginary part.",
        H("Explicit Complex Decay of the Dyadic Transform"),
        Blocks(Describe.Lean(
            DescribeId.Create("dyadic-transform-explicit-strip-decay"),
            DeclarationHandle.Create(
                "D5/S3/Fourier/DyadicComplexDecay.dyadic_transform_explicit_strip_decay"),
            H("An explicit bound at every complex frequency"),
            StatementSource.FromAuthor(DecayFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The transform uses the kernel exp(i z x). The half-width with "
                        + "index j is ell divided by 2 to the power j+2, starting with "
                        + "ell/4. Their sum is ell/2. The density transform equals the "
                        + "infinite product of the corresponding complex sinc factors, "
                        + "with the removable value at zero equal to one.")),
                Paragraph(Text(
                    "For a positive half-width, the uniform probability integral "
                        + "bounds the factor norm by exp(a abs(Im z)). The exponential "
                        + "formula for sine also bounds the factor norm times norm(z) "
                        + "by exp(a abs(Im z))/a. Adding these inequalities gives the "
                        + "factor bound with numerator exp(a abs(Im z)) times (1+1/a) "
                        + "and denominator 1+norm(z).")),
                Paragraph(Text(
                    "Apply the inverse-power bound to the first k factors. Normalize "
                        + "all other factors by their exponential bounds, so their "
                        + "norms are at most one. The total half-width bounds the "
                        + "combined exponential, and convergence of the finite products "
                        + "passes the inequality to the density transform.")),
                Paragraph(Text(
                    "The denominator is positive at every frequency. For order zero "
                        + "the finite product is empty and equals one, giving the "
                        + "exponential bound alone. Restricting the imaginary part to "
                        + "any bounded interval makes the exponential uniform there."))),
            DescribeRole.Theorem))));

    private static Formula DecayFormula()
    {
        Formula ell = F.Id("ell");
        Formula k = F.Id("k");
        Formula z = F.Id("z");
        Formula j = F.Id("j");
        Formula width = Call("dyadicHalfWidth", ell, j);
        Formula constant = Seq(
            Prod, Underscore, Grp(j, Sp, InMacro, Sp, Call("range", k)), Sp,
            Open, Seq(D(1), Sp, Plus, Sp, new Formula.Fraction(D(1), width)), Close);
        Formula exponential = Call("exp", new Formula.Fraction(
            Multiply(ell, Call("abs", Call("im", z))), D(2)));
        Formula bound = new Formula.Fraction(Multiply(exponential, constant),
            new Formula.Power(
                new Formula.Binary(D(1), FormulaBinaryOperator.Add, Call("norm", z)), k));
        Formula transform = Call("norm", Call("densityFourierLaplace",
            Call("dyadicConvolutionDensity", ell), z));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("ell", Call("Real"))],
            new Formula.Logic(
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, ell),
                FormulaLogicOperator.Implies,
                new Formula.BindMany(FormulaQuantifier.ForAll,
                    [Bound("k", Call("Natural")), Bound("z", Call("Complex"))],
                    new Formula.Relation(transform, FormulaRelationOperator.LessThanOrEqual, bound)))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
