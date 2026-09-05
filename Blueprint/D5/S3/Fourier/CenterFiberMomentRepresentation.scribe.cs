using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CenterFiberMomentRepresentationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CenterFiberMomentRepresentation."
            + "center_fiber_moment_representation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even difference moments are Fourier transforms of nonnegative center-fiber densities.",
        H("Center-Fiber Moment Representation"),
        Blocks(Describe.Lean(
            DescribeId.Create("center-fiber-moment-representation"),
            DeclarationHandle.Create(Declaration),
            H("The center-fiber density represents the even moment"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let phi be a continuous nonnegative real function. The source did not "
                        + "state the positivity assumption needed for the claimed pointwise "
                        + "nonnegativity of C_m, so it is explicit here.")),
                Paragraph(Text(
                    "We also require absolute integrability of the real center-fiber moment "
                        + "kernel. This supplies the missing analytic hypothesis for Fubini and "
                        + "for both displayed Lebesgue integrals.")),
                Paragraph(Text(
                    "The proof applies the real linear map (x,y) maps to (x+y,x-y). Its "
                        + "determinant is minus two, so the inverse Jacobian contributes the "
                        + "factor one half in C_m.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies Haar-measure transport for an invertible linear "
                        + "map and Fubini's theorem. Evenness of the exponent and nonnegativity "
                        + "of phi give C_m(u) nonnegative for every real u."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula phi = Varphi;
        Formula m = F.Id("m");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula twoM = Seq(D(2), m);
        Formula factorial = Call("factorial", twoM);
        Formula PhiAt(Formula argument) => Apply(phi, argument);
        Formula exponential(Formula argument) =>
            Call("exp", Seq(F.Id("i"), Sp, t, Sp, argument));
        Formula momentKernel = Seq(
            PhiAt(x), PhiAt(y),
            new Formula.Power(Grp(x, Minus, y), twoM),
            exponential(Grp(x, Plus, y)));
        Formula fiberKernel = Seq(
            new Formula.Power(v, twoM),
            PhiAt(new Formula.Fraction(Seq(u, Plus, v), D(2))),
            PhiAt(new Formula.Fraction(Seq(u, Minus, v), D(2))));
        Formula density = new Formula.Subscript(F.Id("C"), m);
        Formula moment = new Formula.Subscript(Seq(Mathcal, Grp(F.Id("J"))), m);
        Formula densityDefinition = Seq(
            Apply(density, u), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(2), factorial), Sp,
            Integral(v, fiberKernel));
        Formula momentDefinition = Seq(
            Apply(moment, t), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(factorial), Sp,
            Integral(x, Integral(y, momentKernel)));
        Formula representation = Seq(
            Apply(moment, t), Sp, Eq, Sp,
            Integral(u, Seq(Apply(density, u), exponential(u))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, phi, Colon, Sp, new Formula.TypeArrow(real, real), Comma, Sp,
            m, InMacro, Sp, naturals, Comma, Sp, t, InMacro, Sp, real, Comma,
            RowBreak, Grp(),
            Call("Continuous", phi), Sp, Land, Sp,
            Open, Forall, Sp, x, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Leq, Sp, PhiAt(x), Close, Sp, Land,
            RowBreak, Grp(),
            Call("Integrable", LambdaPair(u, v, fiberKernel)),
            Sp, Rightarrow, RowBreak, Grp(),
            densityDefinition, Comma, RowBreak, Grp(),
            momentDefinition, Comma, RowBreak, Grp(),
            representation, Sp, Land, Sp,
            Forall, Sp, u, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(density, u), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula LambdaPair(Formula first, Formula second, Formula body) =>
        Seq(Open, Open, first, Comma, Sp, second, Close,
            Sp, Mapsto, Sp, body, Close);

    private static Formula Integral(Formula variable, Formula integrand) =>
        Seq(Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            integrand, Sp, F.Id("d"), variable);
}
