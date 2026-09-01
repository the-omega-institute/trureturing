using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class LogNormDirectionalDerivativeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic norm of a nonvanishing holomorphic germ has the "
            + "directional logarithmic derivative predicted by the complex chain rule.",
        H("Log-Norm Directional Derivative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("riesz-potential-real-direction-derivative"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/LogNormDirectionalDerivative."
                        + "riesz_potential_real_direction_hasDerivAt"),
                H("The rotated Riesz potential follows the real logarithmic derivative"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Writing Xi(z) = xi(1/2 - i z) rotates the upper-half-plane height "
                            + "into the positive real direction of xi. At a nonzero value, "
                            + "the resulting log-norm potential therefore has derivative "
                            + "Re(xiPrime/xi).")),
                    Paragraph(Text(
                        "The proof differentiates the squared norm and then applies the real "
                            + "logarithm, so it is valid at every nonzero complex value and "
                            + "does not impose a branch cut for the complex logarithm.")),
                    Paragraph(Text(
                        "For the unrotated path x + i omega, the same general theorem gives "
                            + "minus the imaginary part instead. The module checks this sign "
                            + "numerically for f(z) = z and f(z) = z squared at 1 + i."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula xi = F.Id("xi");
        Formula xiPrime = F.Id("xiPrime");
        Formula Xi = F.Id("Xi");
        Formula z = F.Id("z");
        Formula x = F.Id("x");
        Formula omega = F.Id("omega");
        Formula u = F.Id("u");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula rotatedPoint = Seq(
            half, Sp, Plus, Sp, omega, Sp, Minus, Sp,
            F.Id("i"), Sp, Times, Sp, x);
        Formula XiDefinition = Lambda(
            z,
            Apply(
                xi,
                Seq(half, Sp, Minus, Sp,
                    F.Id("i"), Sp, Times, Sp, z)));
        Formula potentialPath = Lambda(
            u,
            Seq(
                Log,
                new Formula.Absolute(
                    Apply(
                        Xi,
                        Seq(x, Sp, Plus, Sp,
                            F.Id("i"), Sp, Times, Sp, u)))));
        Formula derivative = Seq(
            Re,
            Open,
            new Formula.Fraction(xiPrime, Apply(xi, rotatedPoint)),
            Close);
        Formula conclusion = Call(
            "HasDerivAt", potentialPath, derivative, omega);

        return Disp(Seq(
            Forall, Sp,
            xi, Colon, Sp, new Formula.TypeArrow(complex, complex), Comma, Sp,
            xiPrime, InMacro, complex, Comma, Sp,
            x, Comma, Sp, omega, InMacro, real, Comma, RowBreak,
            Grp(), Operatorname, Grp(F.Id("let")), Sp,
            Xi, Sp, Colon, Eq, Sp, XiDefinition, Comma, RowBreak,
            Grp(), conclusion, Dot));
    }
}
