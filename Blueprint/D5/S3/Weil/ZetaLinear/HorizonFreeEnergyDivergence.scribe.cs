using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class HorizonFreeEnergyDivergenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/HorizonFreeEnergyDivergence."
            + "single_defect_horizon_free_energy_universal_divergence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero single-defect depth has a positive horizon determinant exactly inside "
            + "the horizon, and its negative-log free energy diverges at the boundary.",
        H("Single-Defect Horizon Free-Energy Divergence"),
        Blocks(Describe.Lean(
            DescribeId.Create("single-defect-horizon-free-energy-divergence"),
            DeclarationHandle.Create(Declaration),
            H("The horizon free energy diverges universally"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a nonzero nonnegative defect depth delta, field normalization gives "
                        + "the determinant D_delta(omega) = (delta^2 - omega^2) / delta^2. "
                        + "Its sign and zero locus are therefore controlled exactly by the "
                        + "absolute-value horizon inequalities.")),
                Paragraph(Text(
                    "On approach to the positive horizon from below, the determinant stays "
                        + "positive and tends to zero. Mathlib's right-hand logarithm limit "
                        + "then sends -log D_delta to positive infinity.")),
                Paragraph(Text(
                    "The Lean module also checks delta=2 at omega=1 and omega=2 exactly, and "
                        + "provides the explicit sequence omega_n=2-1/(n+1) as a nonvacuous "
                        + "witness of the divergence."))),
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

    private static Formula Formula()
    {
        Formula delta = F.Id("delta");
        Formula omega = F.Id("omega");
        Formula determinant = Call("D", delta, omega);
        Formula deltaSquared = Seq(delta, Caret, D(2));
        Formula omegaSquared = Seq(omega, Caret, D(2));
        Formula quotient = Seq(
            Frac, Grp(deltaSquared, Minus, omegaSquared), Grp(deltaSquared));
        Formula absOmega = Seq(Lvert, Sp, omega, Rvert);
        Formula absDelta = Seq(Lvert, Sp, delta, Rvert);
        Formula realNonnegative = Seq(Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, D(0)));

        return Disp(Seq(
            Forall, Sp, delta, Sp, InMacro, Sp, realNonnegative, Comma, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Open,
            Open, Forall, Sp, omega, Comma, Sp,
            determinant, Sp, Eq, Sp, quotient, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, omega, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, determinant, Sp, Iff, Sp,
            absOmega, Sp, Lt, Sp, absDelta, Close, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, omega, Comma, Sp,
            Open, determinant, Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            absOmega, Sp, Eq, Sp, absDelta, Close, Close,
            Sp, Land, Sp,
            Lim, Underscore, Grp(omega, To, Sp, delta, Caret, Grp(Minus)), Sp,
            Call("F", delta, omega), Sp, Eq, Sp, Infty,
            Close, Dot));
    }
}
