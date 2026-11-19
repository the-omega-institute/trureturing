using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class PhaseTwirledGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent and incoherent Gram terms",
        H("Coherent and incoherent Gram terms"),
        Blocks(Describe.Lean(
            DescribeId.Create("phase-averaged-gram-decomposition"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/PhaseTwirledGram.phase_averaged_gram_decomposition"),
            H("Coherent and incoherent Gram terms"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Independent diagonal phase conjugations preserve a rank-one Gram term on the coherent coordinates. Each other coordinate contributes its own nonnegative diagonal mass."))),
            DescribeRole.Theorem))));
}
