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
                Blocks(Paragraph(Text("The matrix is (I+xX+zZ)/2 in the computational basis, with real x and z and x squared plus z squared at most one. Its constructor proves positivity and trace one, including the pure boundary. The entropy on the left is the canonical CFC von Neumann entropy in natural logarithms. The proof reuses FormationBounds.qubit_entropy_det, cancels its log(2) conversion from bits, and uses the original spectral/CFC bridge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-preparation"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/QubitNormalFormState.qubit_preparation_channel"),
                H("A physical preparation for the pure local pair"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For each x in [0,1], one actual CPTP channel maps the diagonal qubit matrix with parameter t to the normal-form matrix with Bloch coordinates x and t times the square root of one minus x squared. The channel equation holds for every real t, and the inputs are density states on [-1,1]. The same channel prepares both pure local endpoints and all intermediate mixtures; its complete positivity is supplied by the finite square-root Kraus construction."))), DescribeRole.Theorem))));
}
