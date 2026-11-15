using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum;

internal sealed class RelabelingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Layout Quantum Relabeling", H("Core Base Layout Quantum Relabeling"), Blocks(
            Paragraph(Text("For every injective physical map from Nat to Nat, QuantumAlg.QuantumWire.relabel changes each wire identity by that map and preserves its dimension. QuantumAlg.QuantumLayout.relabel applies the same map to every wire and proves identity injectivity by composition; every original logical position and basis value is retained.")),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling.relabelBasis"),
                H("relabelBasis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Logical basis values retain the same finite dimension at every original position."))), DescribeRole.Definition))));
}
