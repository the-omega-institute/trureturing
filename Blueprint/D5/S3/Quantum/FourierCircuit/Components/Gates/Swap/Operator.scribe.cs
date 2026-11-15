using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.Swap;

internal sealed class OperatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates Swap Operator", H("Components Gates Swap Operator"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/Swap/Operator.qftSwapOperator"),
                H("qftSwapOperator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("A genuine addressed wire swap, decomposed semantically into the usual three addressed CNOT permutations."))), DescribeRole.Definition))));
}
