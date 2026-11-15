using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Realization;

internal sealed class PlacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base UnitaryCircuit Realization Placement", H("Core Base UnitaryCircuit Realization Placement"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Placement.embed_matrix"),
                H("embed matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The embedded circuit acts by the physical embedding of its original operator."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Placement.embed_eventTrace"),
                H("embed eventTrace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Embedding retains every native occurrence, including expanded macro bodies."))), DescribeRole.Lemma))));
}
