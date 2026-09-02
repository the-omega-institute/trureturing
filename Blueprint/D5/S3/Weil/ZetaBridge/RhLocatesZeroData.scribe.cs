using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RhLocatesZeroDataDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/RhLocatesZeroData."
            + "zeroData_zero_on_critical_line_of_rh";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under Mathlib's Riemann hypothesis, every zero in supplied ZeroData lies on the "
            + "critical line.",
        H("RH Locates ZeroData on the Critical Line"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-locates-zero-data-on-the-critical-line"),
            DeclarationHandle.Create(Declaration),
            H("RH puts every supplied ZeroData zero on the critical line"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("hRH"), Colon, Sp,
                Operatorname, Grp(F.Id("RiemannHypothesis")), Comma, Sp,
                Forall, Sp, F.Id("Z"), Colon, Sp,
                Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                Sp, Eq, Sp, Operatorname, Grp(F.Id("criticalAbscissa"))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The ZeroData field zero_isNontrivial supplies the nontrivial-zero "
                        + "premise. Through the definitional identification with "
                        + "Zeta23.IsNontrivialZero, the frozen RH_implies_on_line theorem "
                        + "then gives real part one half; unfolding criticalAbscissa closes "
                        + "the displayed equality. Trivial-zero and pole exclusion are already "
                        + "inside that frozen theorem.")),
                Paragraph(Text(
                    "This is a conditional one-line composition for the R-F consumer. It does "
                        + "not prove the Riemann hypothesis, O-6, or any zero count."))),
            DescribeRole.Theorem))));
}
