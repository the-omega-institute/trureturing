using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FinitePreparationChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite density-state preparation as an actual quantum channel", H("FinitePreparationChannel"), Blocks(
            Describe.Lean(DescribeId.Create("finite-preparation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FinitePreparationChannel.finite_preparation_quantum_channel"),
                H("Finite density-state preparation as an actual quantum channel"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For an arbitrary finite family of actual density matrices, there exists a canonical CPTP map whose action on every complex input matrix X is the sum of its diagonal entries Xii times the respective density matrices. The construction uses columns of each positive square root as Kraus operators. The normalization follows from the actual trace-one condition, including singular outputs, and the full-algebra action is proved from the same Kraus family. For x in [0,1], take the two prepared qubits (I+xX plus or minus sqrt(1-x squared)Z)/2. On the diagonal input (I+tZ)/2, the formula gives (I+xX+t sqrt(1-x squared)Z)/2 for every real t. For t in [-1,1], these inputs and outputs are density states. This physical preparation operation asserts no entropy inequality by itself."))), DescribeRole.Theorem))));
}
