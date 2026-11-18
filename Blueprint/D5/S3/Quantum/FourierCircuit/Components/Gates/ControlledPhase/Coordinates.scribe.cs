using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase;

internal sealed class CoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates ControlledPhase Coordinates", H("Components Gates ControlledPhase Coordinates"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Coordinates.qftControlledPhaseFactor_coordinates"),
                H("qftControlledPhaseFactor coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The original addressed phase reads exactly the supplied logical control and target bits."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Coordinates.qftControlledPhaseOperator_coordinates"),
                H("qftControlledPhaseOperator coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Reindexing the unchanged target yields its exact diagonal on the ordered physical bits."))), DescribeRole.Lemma))));
}
