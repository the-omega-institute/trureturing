using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class GoldenEulerGapWordConstraintsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/GoldenEulerGapWordConstraints.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The deterministic golden Euler frequency word forbids two consecutive short steps "
            + "and three consecutive long steps, and Euler phase letters inherit the same grammar.",
        H("Golden Euler Gap Word Constraints"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("short-frequency-forces-next-long"),
                DeclarationHandle.Create(Prefix + "short_frequency_forces_next_long"),
                H("A short frequency step forces a following long step"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("short_frequency_forces_next_long")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The golden word identifies true letters with phi-squared prime-log "
                            + "gaps and false letters with phi prime-log gaps. Existing golden "
                            + "desubstitution proves that false-false never occurs, so every "
                            + "short frequency letter is followed by a long one.")),
                    Paragraph(Text(
                        "The same module proves that three long letters never occur and transports "
                            + "both forbidden-word laws to the Euler phase alphabet. This is a "
                            + "deterministic symbolic constraint; an explicit stochastic non-iid "
                            + "theorem would additionally require a chosen probability measure."))),
                DescribeRole.Theorem))));
}
