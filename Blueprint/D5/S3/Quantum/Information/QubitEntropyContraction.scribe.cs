using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class QubitEntropyContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic contraction for an actual symmetric qubit ensemble", H("QubitEntropyContraction"), Blocks(
            Describe.Lean(DescribeId.Create("holevo-contraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction"),
                H("Quadratic contraction for an actual symmetric qubit ensemble"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For every point of the closed qubit disk and every t in [0,1], the symmetric binary Holevo entropy is nonnegative and contracts by at most t squared when z is replaced by tz. The proof derives concavity of u mapped to binary entropy of (1+sqrt(u))/2 from scalar derivatives on (0,1), with continuity at both endpoints. The matrix statement then uses the actual qubit density states and their spectral entropy, including pure, zero-separation and maximal-mixing cases."))), DescribeRole.Theorem))));
}
