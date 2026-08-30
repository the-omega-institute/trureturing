using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class MasslessTangentConeLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit.";

    public DocumentDefinition Create()
    {
        Formula sigma = F.Id("sigma");
        Formula lambda = F.Id("lambda");
        Formula epsilon = Varepsilon;
        Formula frequency = F.Id("k");
        Formula bandSize = F.Id("n");
        Formula mode = F.Id("j");
        Formula coefficients = F.Id("c");
        Formula index = F.Id("m");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteBand = Call("FiniteFourierBand", bandSize);
        Formula phiSigma = new Formula.Subscript(Phi, Seq(sigma));
        Formula epsilonSquared = Seq(epsilon, Caret, Grp(D(2)));
        Formula scale = Seq(sigma, Sp, Plus, Sp, D(2), index);
        Formula scaleSquared = Seq(Open, scale, Close, Caret, Grp(D(2)));
        Formula towerDefinition = Disp(Seq(
            Forall, Sp, sigma, Comma, Sp, lambda, InMacro, Sp, reals, Comma, Sp,
            phiSigma, Open, lambda, Close, Sp, Eq, Sp,
            Sum, Underscore, Grp(index, Eq, D(0)), Caret, Grp(Infty), Sp,
            Call("log", Seq(
                D(1), Sp, Plus, Sp,
                new Formula.Fraction(lambda, scaleSquared))), Dot));

        Formula scalarLimit = Seq(
            Forall, Sp, lambda, InMacro, Sp, reals, Comma, Sp,
            D(0), Sp, Leq, Sp, lambda, Sp, Rightarrow, Sp,
            Lim, Underscore, Grp(epsilon, To, D(0), Caret, Grp(Plus)), Sp,
            epsilon, Sp,
            phiSigma, Open, new Formula.Fraction(lambda, epsilonSquared), Close,
            Sp, Eq, Sp,
            new Formula.Fraction(Pi, D(2)), Sp, Sqrt, Grp(lambda));
        Formula multiplierLimit = Seq(
            Forall, Sp, bandSize, InMacro, Sp, naturals, Comma, Sp,
            frequency, Colon, Sp, Call("Fin", bandSize), Sp, To, Sp, reals, Comma, Sp,
            coefficients, InMacro, Sp, finiteBand, Comma, Sp,
            Lim, Underscore, Grp(epsilon, To, D(0), Caret, Grp(Plus)), Sp,
            Call("M", Seq(
                mode, Sp, Mapsto, Sp,
                epsilon, Sp, phiSigma, Open,
                new Formula.Fraction(
                    Seq(frequency, Open, mode, Close, Caret, Grp(D(2))),
                    epsilonSquared), Close)),
            Open, coefficients, Close, Sp, Eq, Sp,
            Call("M", Seq(
                mode, Sp, Mapsto, Sp,
                new Formula.Fraction(Pi, D(2)), Sp,
                new Formula.Absolute(Seq(frequency, Open, mode, Close)))),
            Open, coefficients, Close);
        Formula tangentConeLimit = Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, sigma, InMacro, Sp, reals, Comma, Sp,
                D(0), Sp, Lt, Sp, sigma, Sp, Rightarrow),
            Seq(Grp(), OpenBracket, scalarLimit, CloseBracket, Sp, Land),
            Seq(Grp(), OpenBracket, multiplierLimit, CloseBracket, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The logarithmic Archimedean tower has the universal massless tangent symbol.",
            H("Massless Tangent-Cone Limit"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("archimedean-dispersion"),
                    DeclarationHandle.Create(Prefix + "archimedean_dispersion"),
                    H("The logarithmic tower dispersion"),
                    StatementSource.FromAuthor(towerDefinition),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The function is constructed directly as the infinite sum over the "
                            + "source scales sigma plus twice the natural index."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("massless-tangent-cone-limit"),
                    DeclarationHandle.Create(Prefix + "massless_tangent_cone_limit"),
                    H("The scaled tower converges to the massless symbol"),
                    StatementSource.FromAuthor(tangentConeLimit),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For positive sigma, monotone sum-integral comparison traps the "
                                + "tower between an explicit integral and that integral plus "
                                + "its first summand. Both scaled bounds converge to pi over two.")),
                        Paragraph(Text(
                            "The second public conjunct is the operator clause on a concrete "
                                + "finite Fourier coefficient space. For every finite frequency "
                                + "band and every coefficient vector, the diagonal continuous "
                                + "linear multipliers converge in the coefficient-space norm, "
                                + "which is strong operator convergence on each fixed band. The "
                                + "claim does not assert bounded operator-norm convergence on the "
                                + "whole L2 circle, where the limiting absolute-frequency "
                                + "multiplier is unbounded."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
