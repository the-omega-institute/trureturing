using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class PairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.",
        H("The continuous observable trace pairing"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-pairing"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/Pairing.tracePairingContinuousLinearMap_apply"),
            H("The continuous observable trace pairing"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("The map sending a bounded A to the functional T maps to Tr(A T) is complex linear and continuous from the operator norm into the strong dual of the genuine trace-class Banach space. Its norm is bounded by one. The trace-class slot uses the trace norm.")),
                Paragraph(Text("Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers."))),
            DescribeRole.Theorem))));
    private static Formula Endpoint() => Equal(Call("tracePairingContinuousLinearMap", F.Id("A")), Call("tracePairing", F.Id("A")));
}
