using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class ReductionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Composition of polynomial many-one reductions.",
        H("Composition of polynomial many-one reductions"),
        Blocks(
            Paragraph(Text("Reduction transitivity composes total deterministic polynomial transducers and the two all-word membership equivalences. NP-hardness and completeness transfer consume that composition theorem; they supply no new SAT premise.")),
            Describe.Lean(
                DescribeId.Create("supplied-reductions"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/Reductions.trans"),
                H("PolyRed.trans"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text(
                    "This declaration and its proof are attributed immutable source supply. "
                    + "The mathematical namespace and proof body are preserved. Full license, "
                    + "source correspondence and the finite retirement contract are recorded "
                    + "in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies "
                    + "no new classification or independent mathematical escape content."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Composition"))]));
}
