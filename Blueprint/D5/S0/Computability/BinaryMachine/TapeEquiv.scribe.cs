using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class TapeEquivDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Blank-padding equivalence of tape execution.",
        H("Blank-padding equivalence of tape execution"),
        Blocks(
            Paragraph(Text("Tape equivalence compares the bi-infinite tape modulo irrelevant trailing blanks. It preserves the current read symbol, each write and move, output bytes and halting executions. A finite representation with extra blank storage therefore supports the same physical computation.")),
            Describe.Lean(
                DescribeId.Create("supplied-tapeequiv"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/TapeEquiv.run_some_of_equivalent"),
                H("run_some_of_equivalent"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Machine"))]));
}
