using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class FiniteIndexHorizonExclusionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/FiniteIndexHorizonExclusion."
            + "finite_index_horizon_exclusion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform finite inclusion-index bound excludes noncritical zeta zeros.",
        H("Finite-Index Horizon Exclusion"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-index-horizon-exclusion"),
            DeclarationHandle.Create(Declaration),
            H("A finite horizon bound forces critical-line location"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The inclusionIndex function models the information index of the "
                        + "observer inclusion at each positive depth below the critical "
                        + "abscissa, and bound is its uniform finite upper bound.")),
                Paragraph(Text(
                    "For a right-side nontrivial zero rho, the controlled matrix is the "
                        + "one-by-one Hankel matrix with entry omega divided by the canonical "
                        + "criticalDisplacement of rho. Its effective index is the reciprocal "
                        + "singular factor, which exceeds every fixed bound near the horizon.")),
                Paragraph(Text(
                    "Repository reflection transports any left-side nontrivial zero to the "
                        + "excluded right side, so every nontrivial zero has critical real part."))),
            DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula inclusionIndex = F.Id("inclusionIndex");
        Formula bound = F.Id("bound");
        Formula omega = F.Id("omega");
        Formula rho = Rho;
        Formula critical = F.Id("criticalAbscissa");
        Formula displacement = Call("criticalDisplacement", rho);
        Formula indexAtOmega = Call(inclusionIndex, omega);
        Formula normalizedEntry = Seq(Frac, Grp(omega), Grp(displacement));
        Formula singletonHankel = Call("singletonMatrix", normalizedEntry);

        Formula uniformBound = Seq(
            Open,
            Forall, Sp, omega, Sp, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, omega, Sp, Rightarrow, Sp,
            omega, Sp, Lt, Sp, critical, Sp, Rightarrow, Sp,
            indexAtOmega, Sp, Leq, Sp, bound,
            Close);

        Formula horizonControl = Seq(
            Open,
            Forall, Sp, rho, Sp, InMacro, Sp, complex, Comma, Sp,
            Call("IsNontrivialZero", rho), Sp, Rightarrow, RowBreak, Grp(),
            critical, Sp, Lt, Sp, Call("Re", rho), Sp, Rightarrow, Sp,
            Forall, Sp, omega, Sp, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, omega, Sp, Rightarrow, Sp,
            omega, Sp, Lt, Sp, displacement, Sp, Rightarrow, RowBreak, Grp(),
            Call("horizonEffectiveIndex", singletonHankel), Sp, Leq, Sp,
            indexAtOmega,
            Close);

        Formula conclusion = Seq(
            Forall, Sp, rho, Sp, InMacro, Sp, complex, Comma, Sp,
            Call("IsNontrivialZero", rho), Sp, Rightarrow, Sp,
            Call("Re", rho), Sp, Eq, Sp, critical);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, inclusionIndex, Colon, Sp,
            new Formula.TypeArrow(real, real), Comma, Sp,
            bound, Sp, InMacro, Sp, real, Comma, RowBreak, Grp(),
            uniformBound, Sp, Land, RowBreak, Grp(),
            horizonControl, Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
