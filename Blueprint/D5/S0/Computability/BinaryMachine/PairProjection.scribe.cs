using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class PairProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total exact binary pair projections.",
        H("Total exact binary pair projections"),
        Blocks(
            Paragraph(Text("The supplied decoder detects missing unary delimiters, oversized length claims and short payloads. For a valid pair the selected component is returned unchanged; for an invalid outer word the literal fixed fallback is written. Both left and right projections are total polynomial transducers in the same tape model, and arbitrary payload bytes and empty components are preserved.")),
            Describe.Lean(
                DescribeId.Create("polytime-project"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/PairProjection.polyTime_project"),
                H("polyTime_project"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The supplied decoder detects missing unary delimiters, oversized length claims and short payloads. For a valid pair the selected component is returned unchanged; for an invalid outer word the literal fixed fallback is written. Both left and right projections are total polynomial transducers in the same tape model, and arbitrary payload bytes and empty components are preserved."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PairPreimage"))]));
}
