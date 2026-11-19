using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Gate;

internal sealed class ModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Gate Model", H("Core Base Gate Model"), Blocks(
            Paragraph(Text("For every GateModel model and Occurrence gate, QuantumAlg.GateModel.Occurrence.coordinate gate is model.coordinate gate.token. Its operator reindexes model.operator gate.token along the certified placement index equivalence; the occurrence does not supply an independently chosen matrix.")),
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.GateModel"),
                H("GateModel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("An elementary-gate language with fixed physical and unitary semantics."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model.Occurrence"),
                H("Occurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("One occurrence of a gate from a specific model. No independently supplied operator, event count, depth or space claim is stored here."))), DescribeRole.Definition))));
}
