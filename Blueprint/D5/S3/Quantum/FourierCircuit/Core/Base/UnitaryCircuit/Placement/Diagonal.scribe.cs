using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement;

internal sealed class DiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base UnitaryCircuit Placement Diagonal", H("Core Base UnitaryCircuit Placement Diagonal"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Diagonal.operatorAt_diagonal"),
                H("operatorAt diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("A placed diagonal target reads exactly the selected ambient coordinates."))), DescribeRole.Lemma))));
}
