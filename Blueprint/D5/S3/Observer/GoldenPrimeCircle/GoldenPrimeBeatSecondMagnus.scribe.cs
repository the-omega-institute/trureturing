using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenPrimeBeatSecondMagnusDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenPrimeBeatSecondMagnus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden long-short frequency gap is log p, so pi divided by log p maximizes the alternating two-slot Magnus kernel and twice that time restores resonance.",
        H("Golden Prime Beat Second-Magnus Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-beat-separation-recurrence"),
                DeclarationHandle.Create(
                    Prefix + "prime_beat_separation_recurrence"),
                H("Half-beat separation and full-beat recurrence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Norm, Open,
                    Operatorname, Grp(F.Id("secondMagnusSwapKernel")),
                    Close, Sp, Eq, Sp, D(2), Comma, Sp,
                    Operatorname, Grp(F.Id("fullBeatKernel")), Sp,
                    Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The deterministic alphabet frequencies phi log p and phi squared log p differ by exactly log p. At time pi divided by log p their relative phase is minus one, and the alternating kernel reaches its universal norm-two bound.")),
                    Paragraph(Text(
                        "At twice that time the relative phase completes a full turn and the kernel vanishes. The calibration is prime dependent and does not provide one common window for an infinite prime family."))),
                DescribeRole.Theorem))));
}
