using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class SimulatorUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform error of the actual finite simulator",
        H("Uniform error of the actual finite simulator"),
        Blocks(Describe.Lean(
            DescribeId.Create("matching-simulator-upper"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/SimulatorUpper.matchingSimulator_upper"),
            H("Uniform error of the actual finite simulator"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Finite phase and permutation averaging separates the coherent blocks. Positive Choi domination at the matching tilt bounds the error of the realized simulator for every finite reference and complex input."))),
            DescribeRole.Theorem))));
}
