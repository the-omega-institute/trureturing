using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Toroidal;

internal sealed class InnernessSelfImprovementDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Toroidal/InnernessSelfImprovement."
            + "innerness_self_improvement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterated strict improvement whose thresholds converge to zero upgrades eventual "
            + "innerness beyond one half to innerness at every positive width.",
        H("Innerness Self-Improvement"),
        Blocks(Describe.Lean(
            DescribeId.Create("innerness-self-improvement"),
            DeclarationHandle.Create(Declaration),
            H("Convergent threshold improvement reaches zero"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write I(a) for innerness at every width omega greater than a. The "
                        + "initial hypothesis is I(1/2). At every positive threshold at most "
                        + "one half, F remains positive, is strictly smaller, and transports "
                        + "I(a) to I(F(a)).")),
                Paragraph(Text(
                    "Induction gives I at every iterate of one half while keeping each iterate "
                        + "in the positive half interval. Convergence to zero then places an "
                        + "iterate below any prescribed positive omega, whose I-property gives "
                        + "innerness at omega.")),
                Paragraph(Text(
                    "The convergence hypothesis repairs a gap in the source statement: strict "
                        + "decrease of an arbitrary, possibly discontinuous map does not imply "
                        + "that its iterates converge to zero. The nearby frozen threshold "
                        + "identity supplies context but no iterative improvement theorem."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula innerAt = F.Id("innerAt");
        Formula improvement = F.Id("F");
        Formula a = F.Id("a");
        Formula omega = F.Id("omega");
        Formula n = F.Id("n");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula real = Reals();
        Formula innerBeyond(Formula threshold) => Seq(
            Forall, Sp, omega, InMacro, real, Comma, Sp,
            threshold, Sp, Lt, Sp, omega, Sp, Rightarrow, Sp,
            Apply(innerAt, omega));
        Formula improved = Apply(improvement, a);
        Formula iterate = Call("iterate", improvement, n, half);
        Formula domain = Seq(
            D(0), Sp, Lt, Sp, a, Sp, Land, Sp, a, Sp, Leq, Sp, half);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, innerAt, Colon, Sp, real, Sp, To, Sp,
                Seq(Operatorname, Grp(F.Id("Prop"))), Comma, Sp,
                improvement, Colon, Sp, real, Sp, To, Sp, real, Comma),
            Seq(
                Open, innerBeyond(half), Close, Sp, Land, Sp,
                Open, Forall, Sp, a, InMacro, real, Comma, Sp,
                domain, Sp, Rightarrow, Sp, D(0), Sp, Lt, Sp, improved,
                Sp, Lt, Sp, a, Close, Sp, Land),
            Seq(
                Open, Forall, Sp, a, InMacro, real, Comma, Sp,
                domain, Sp, Rightarrow, Sp,
                Open, innerBeyond(a), Close, Sp, Rightarrow, Sp,
                Open, innerBeyond(improved), Close, Close, Sp, Land),
            Seq(
                Call("Tendsto", Seq(
                    Open, n, Mapsto, iterate, Close), D(0)), Sp, Rightarrow),
            Seq(innerBeyond(D(0)), Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
