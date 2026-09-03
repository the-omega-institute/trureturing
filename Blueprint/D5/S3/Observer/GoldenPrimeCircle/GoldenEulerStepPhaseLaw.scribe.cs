using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenEulerStepPhaseLawDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Deterministic Zeckendorf long-short steps become a two-letter "
                + "Euler phase alphabet in each prime channel.",
            H("Golden Euler Step Phase Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("prime-step-phase-euler"),
                    DeclarationHandle.Create(Prefix + "prime_step_phase_euler"),
                    H("Each deterministic step obeys Euler's formula"),
                    StatementSource.FromAuthor(
                        Disp(F.Id("stepPhase = cos(theta) + i sin(theta)"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Zeckendorf chooses the phi or phi-squared frequency "
                                + "increment before the phase is evaluated.")),
                        Paragraph(Text(
                            "Scalar unit-circle multiplication forgets adjacent "
                                + "step order, exposing an endpoint chronology "
                                + "obstruction."))),
                    DescribeRole.Theorem))));
}
