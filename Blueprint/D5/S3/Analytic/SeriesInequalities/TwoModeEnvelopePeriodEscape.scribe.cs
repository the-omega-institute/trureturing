using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class TwoModeEnvelopePeriodEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.";
    private static Formula B => F.Id("b");
    private static Formula G => F.Id("g");
    private static Formula V => F.Id("v");
    private static Formula G1 => new Formula.Subscript(G, D(1));
    private static Formula G2 => new Formula.Subscript(G, D(2));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula P(Formula x) => Seq(Open, x, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full period defeats an opposite-phase two-mode contact throughout a real parameter range.",
        H("Two-Mode Envelope Period Escape"),
        Blocks(
            Entry("mode", "mode", "A damped mode and its lag",
                Disp(Seq(Call("mode", B, G, V), Eq,
                    Exp, P(Seq(Minus, P(Seq(D(1), Minus, B)), V)),
                    P(Seq(Call("c", B, G), Call("cos", Seq(G, V)), Minus,
                        Call("d", B, G), Sin, P(Seq(G, V)))), Minus,
                    Call("a", B, G), Exp, P(Seq(Minus, V)))),
                "Set alpha=1-b, Da(b,g)=g^2+alpha^2 and Db(b,g)=g^2+b^2. "
                + "The real coefficients are c(b,g)=2(alpha/Da+b/Db), "
                + "d(b,g)=2g(2b-1)/(Da Db) and a(b,g)=2b/Db. "
                + "For rho=b+ig, the complex coefficient -2/(rho(rho-1)) has "
                + "real part c and imaginary part d. Thus the oscillatory term "
                + "uses c cos(gv)-d sin(gv); the lag uses exp(-v).",
                DescribeRole.Definition),
            Entry("profile", "profile", "The opposite-phase profile",
                Disp(Seq(Call("profile", B, G1, G2, V), Eq,
                    Call("mode", B, G1, V), Minus, Call("mode", B, G2, V))),
                "Subtracting the second mode implements the relative phase pi, "
                + "including the difference of the lag coefficients. The same "
                + "real part b and time coordinate v are used for both modes.",
                DescribeRole.Definition),
            Entry("period-escape", "result", "The first period strictly beats the origin",
                Disp(Seq(Forall, Sp, B, Comma, G1, Comma, G2, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    P(Seq(Q(D(7), D(1, 0)), Le, Sp, B, Land, Sp, B, Lt, D(1), Land, Sp,
                        D(1, 4), Le, Sp, G1, Land, Sp, G1, Lt, G2)), Sp, Implies, Sp,
                    Call("profile", B, G1, G2, D(0)), Lt,
                    Call("profile", B, G1, G2, Q(Seq(D(2), Pi), G1)))),
                "All parameters are real: 7/10<=b<1 and 14<=g1<g2. "
                + "At v=2pi/g1 the first mode returns to its initial phase. "
                + "Exponential bounds and the denominator comparison give a strict "
                + "difference between the same-phase increments. When g2<=3g1/2, "
                + "the second-mode sine is nonnegative and cannot erase that gain. "
                + "For larger g2, the possible phase gain is at most g2^(-4), "
                + "which is smaller than the first-period increment difference. "
                + "Consequently the origin cannot dominate this profile at all real times. "
                + "The strict margin depends on the parameters. The conclusion covers "
                + "this profile and this real-part range; it does not identify a "
                + "profile limit of actual ordinary-integer Robin sources, establish "
                + "their phase realization, or bound the remaining zeta zero modes.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
