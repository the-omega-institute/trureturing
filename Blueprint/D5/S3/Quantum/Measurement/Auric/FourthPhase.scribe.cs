using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class FourthPhaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent fourth-root phase average",
        H("Independent fourth-root phase average"),
        Blocks(Describe.Lean(
            DescribeId.Create("independent-phase-average"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/FourthPhase.independent_phase_average"),
            H("Independent fourth-root phase average"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Averaging independently over four phases deletes each nontrivial character. Coherent diagonal pairs and matching off-diagonal coordinates survive."))),
            DescribeRole.Theorem))));
}
