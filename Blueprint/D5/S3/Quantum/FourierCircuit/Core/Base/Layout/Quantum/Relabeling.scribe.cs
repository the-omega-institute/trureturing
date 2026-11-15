using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum;

internal sealed class RelabelingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Layout Quantum Relabeling", H("Core Base Layout Quantum Relabeling"), Blocks(
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Relabeling.relabelBasis"),
                H("relabelBasis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("Logical basis values retain the same finite dimension at every original position."))), DescribeRole.Definition))));
}
