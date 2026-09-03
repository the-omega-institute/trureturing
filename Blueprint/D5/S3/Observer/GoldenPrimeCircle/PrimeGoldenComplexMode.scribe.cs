using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class PrimeGoldenComplexModeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/PrimeGoldenComplexMode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "A first golden prime mode splits into prime-faithful heat amplitude "
                + "and recurrent unit-circle phase.",
            H("Prime Golden Complex Mode"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create(
                        "complex-mode-amplitude-phase-dichotomy"),
                    DeclarationHandle.Create(
                        Prefix + "complex_mode_amplitude_phase_dichotomy"),
                    H("Positive amplitude identifies primes while phase recurs"),
                    StatementSource.FromAuthor(
                        Disp(F.Id(
                            "positive amplitude is injective; zero-sigma phase recurs"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The real coordinate controls modulus and the imaginary "
                                + "coordinate controls rotation.")),
                        Paragraph(Text(
                            "This is an analytic-time statement and does not identify "
                                + "the parameter with laboratory time."))),
                    DescribeRole.Theorem))));
}
