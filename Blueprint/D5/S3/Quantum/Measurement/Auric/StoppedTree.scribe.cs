using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class StoppedTreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Almost-sure stopping on the original register",
        H("Almost-sure stopping on the original register"),
        Blocks(Describe.Lean(
            DescribeId.Create("tape-stopping-closure"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/StoppedTree.inClosure_of_tape_stopping"),
            H("Almost-sure stopping on the original register"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each classical tape the cutoff stops every unfinished terminal branch with a fixed flag and retains its quantum state. Integrating the truncated actions and controlling the unfinished mass gives a diamond approximation."))),
            DescribeRole.Theorem))));
}
