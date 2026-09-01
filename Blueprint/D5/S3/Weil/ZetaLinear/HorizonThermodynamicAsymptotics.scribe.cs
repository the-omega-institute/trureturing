using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class HorizonThermodynamicAsymptoticsDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/HorizonThermodynamicAsymptotics."
            + "single_defect_horizon_thermodynamic_asymptotics";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squeezing coordinate, occupation number, and free energy of a positive "
            + "single-defect depth have exact horizon identities and first-order "
            + "boundary asymptotics.",
        H("Single-Defect Horizon Thermodynamic Asymptotics"),
        Blocks(Describe.Lean(
            DescribeId.Create("single-defect-horizon-thermodynamic-asymptotics"),
            DeclarationHandle.Create(Declaration),
            H("The horizon corrections have universal leading coefficients"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every nonzero nonnegative depth delta, the existing horizon "
                        + "determinant law is retained. In the strict interior, the "
                        + "negative-log free energy equals both twice log cosh of the "
                        + "artanh squeezing coordinate and log of one plus occupation.")),
                Paragraph(Text(
                    "Writing epsilon=delta-omega and approaching zero from above, the "
                        + "three normalized errors converge respectively to "
                        + "-1/(4 delta), -3/4, and 1/(2 delta). These exact limits "
                        + "strengthen the source's two O(epsilon) and one O(1) claims.")),
                Paragraph(Text(
                    "The Lean module computes the interior point delta=2, omega=1 and "
                        + "the excluded zero-depth case exactly, preventing totalized "
                        + "division or logarithms from making the theorem vacuous."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Limit(Formula epsilon, Formula expression, Formula value) =>
        Seq(Lim, Underscore, Grp(epsilon, To, Sp, D(0), Caret, Grp(Plus)), Sp,
            expression, Sp, Eq, Sp, value);

    private static Formula Formula()
    {
        Formula delta = F.Id("delta");
        Formula omega = F.Id("omega");
        Formula epsilon = F.Id("epsilon");
        Formula determinant = Call("D", delta, omega);
        Formula freeEnergy = Call("F", delta, omega);
        Formula squeeze = Call("r", delta, omega);
        Formula occupation = Call("N", delta, omega);
        Formula deltaSquared = Seq(delta, Caret, D(2));
        Formula omegaSquared = Seq(omega, Caret, D(2));
        Formula quotient = Seq(
            Frac, Grp(deltaSquared, Minus, omegaSquared), Grp(deltaSquared));
        Formula interior = Seq(Lvert, omega, Rvert, Sp, Lt, Sp, delta);
        Formula leadingSqueeze = Seq(
            Frac, Grp(D(1)), Grp(D(2)), Sp, Call("log",
                Seq(Frac, Grp(D(2), delta), Grp(epsilon))));
        Formula leadingOccupation = Seq(Frac, Grp(delta), Grp(D(2), epsilon));
        Formula leadingFreeEnergy = Call("log",
            Seq(Frac, Grp(delta), Grp(D(2), epsilon)));
        Formula nearHorizon = Seq(delta, Minus, epsilon);
        Formula realNonnegative = Seq(Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, D(0)));

        return Disp(Seq(
            Forall, Sp, delta, Sp, InMacro, Sp, realNonnegative, Comma, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp, Open,
            Open, Forall, Sp, omega, Comma, Sp, determinant, Sp, Eq, Sp, quotient, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, omega, Comma, Sp, interior, Sp, Rightarrow, Sp,
            freeEnergy, Sp, Eq, Sp,
            D(2), Call("log", Call("cosh", squeeze)), Sp, Eq, Sp,
            Call("log", Seq(D(1), Plus, occupation)), Close,
            Sp, Land, Sp,
            Limit(epsilon,
                Seq(Frac,
                    Grp(Call("r", delta, nearHorizon), Minus, leadingSqueeze),
                    Grp(epsilon)),
                Seq(Minus, Frac, Grp(D(1)), Grp(D(4), delta))),
            Sp, Land, Sp,
            Limit(epsilon,
                Seq(Call("N", delta, nearHorizon), Minus, leadingOccupation),
                Seq(Minus, Frac, Grp(D(3)), Grp(D(4)))),
            Sp, Land, Sp,
            Limit(epsilon,
                Seq(Frac,
                    Grp(Call("F", delta, nearHorizon), Minus, leadingFreeEnergy),
                    Grp(epsilon)),
                Seq(Frac, Grp(D(1)), Grp(D(2), delta))),
            Sp, Land, Sp,
            Lim, Underscore, Grp(omega, To, Sp, delta, Caret, Grp(Minus)), Sp,
            freeEnergy, Sp, Eq, Sp, Infty,
            Close, Dot));
    }
}
