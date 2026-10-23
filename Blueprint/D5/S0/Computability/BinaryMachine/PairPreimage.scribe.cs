using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class PairPreimageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Preserving witnesses under polynomial instance maps.",
        H("Preserving witnesses under polynomial instance maps"),
        Blocks(
            Paragraph(Text("Every raw outer word is decoded by the supplied finite pair parser. On success the concrete transducer transforms only the instance, keeping the entire certificate in a disjoint register; the pair constructor re-encodes the result. On outer failure it returns the empty raw word. A uniform all-word polynomial tape bound follows from executed decoder, transducer and constructor runs.")),
            Describe.Lean(
                DescribeId.Create("polytime-map"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/PairPreimage.polyTime_map"),
                H("polyTime_map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Every raw outer word is decoded by the supplied finite pair parser. On success the concrete transducer transforms only the instance, keeping the entire certificate in a disjoint register; the pair constructor re-encodes the result. On outer failure it returns the empty raw word. A uniform all-word polynomial tape bound follows from executed decoder, transducer and constructor runs."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TransducerPair"))]));
}
