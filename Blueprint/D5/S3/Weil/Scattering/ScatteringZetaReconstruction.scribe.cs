using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ScatteringZetaReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All shifted normalized modular-scattering readings reconstruct the Riemann zeta value.",
        H("Scattering-Zeta Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scattering-zeta-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/ScatteringZetaReconstruction."
                        + "scattering_zeta_reconstruction"),
                H("The shifted scattering products converge to zeta"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every complex z with real part greater than one, the first displayed "
                            + "factor is the normalized zeta ratio at the shifted half-argument. "
                            + "Its finite products telescope exactly to zeta(z) divided by zeta(z+N).")),
                    Paragraph(Text(
                        "A vertical-translate L-series with unit-modulus coefficients proves that "
                            + "zeta(z+N) tends to one for arbitrary fixed imaginary part. Gamma "
                            + "nonvanishing on the relevant right half-plane then cancels the "
                            + "Archimedean factors in the second displayed product."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("z");
        Formula premise = new Formula.Relation(
            RealPart(z),
            FormulaRelationOperator.GreaterThan,
            D(1));
        Formula normalizedLimit = ProductLimit(z, false);
        Formula expandedLimit = ProductLimit(z, true);
        Formula conclusion = new Formula.Logic(
            normalizedLimit,
            FormulaLogicOperator.And,
            expandedLimit);
        return Disp(Seq(
            Forall, Sp, z, Sp, InMacro, Sp, Complexes(), Comma, Esc,
            premise, Sp, Rightarrow, Sp, conclusion));
    }

    private static Formula ProductLimit(Formula z, bool expanded)
    {
        Formula n = F.Id("N");
        Formula j = F.Id("j");
        Formula s = new Formula.Fraction(Add(Add(z, j), D(1)), D(2));
        Formula factor = expanded ? ExpandedFactor(z, j, s) : ZetaRatio(s);
        Formula product = Seq(
            Prod, Underscore, Grp(j, Eq, D(0)), Caret, Grp(n, Minus, D(1)), Sp, factor);
        return Equal(
            Seq(Lim, Underscore, Grp(n, To, Infty), Sp, product),
            ZetaAt(z));
    }

    private static Formula ExpandedFactor(Formula z, Formula j, Formula s)
    {
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula sqrtPi = Seq(Sqrt, Grp(Pi));
        Formula gammaShift = GammaAt(Subtract(s, half));
        Formula gamma = GammaAt(s);
        Formula scatteringCoefficient = Multiply(
            new Formula.Fraction(Multiply(sqrtPi, gammaShift), gamma),
            ZetaRatio(s));
        Formula archimedeanRemoval = new Formula.Fraction(
            gamma,
            Multiply(sqrtPi, GammaAt(new Formula.Fraction(Add(z, j), D(2)))));
        return Multiply(scatteringCoefficient, archimedeanRemoval);
    }

    private static Formula ZetaRatio(Formula s) => new Formula.Fraction(
        ZetaAt(Subtract(Multiply(D(2), s), D(1))),
        ZetaAt(Multiply(D(2), s)));

    private static Formula ZetaAt(Formula argument) => Seq(Zeta, Open, argument, Close);

    private static Formula GammaAt(Formula argument) => Seq(Gamma, Open, argument, Close);

    private static Formula RealPart(Formula argument) => Seq(Re, Open, argument, Close);

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
