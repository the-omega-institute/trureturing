using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class QubitNormalFormStateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual closed-disk qubit entropy", H("QubitNormalFormState"), Blocks(
            Describe.Lean(DescribeId.Create("qubit-entropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/QubitNormalFormState.qubit_state_entropy"),
                H("The actual closed-disk qubit entropy"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("The matrix is (I+xX+zZ)/2 in the computational basis, with real x and z and x squared plus z squared at most one. Its constructor proves positivity and trace one, including the pure boundary. The entropy on the left is the canonical CFC von Neumann entropy in natural logarithms. The proof reuses FormationBounds.qubit_entropy_det, cancels its log(2) conversion from bits, and uses the original spectral/CFC bridge."))), DescribeRole.Theorem))));
}
