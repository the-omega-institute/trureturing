using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseRecordSpectralMemoryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseRecordSpectralMemory.";
    private static LibraryNoteRef DetectorDual => LibraryNoteRef.Create("D5/L/Entropy/eldar2003detectors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading spectrum of the discrimination dual limits decoding through a finite memory.",
        H("Spectral bounds for finite-memory discrimination"),
        Blocks(
            Describe.Lean(DescribeId.Create("pure-state-memory-dual-spectrum"),
                DeclarationHandle.Create(Module + "pure_success_le_largestEigenvalueSum"),
                H("Pure-state success is bounded by the leading dual eigenvalues"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(DetectorDual),
                Blocks(Paragraph(Text("For normalized pure signals, any feasible discrimination dual bounds the score after a CPTP encoder into a memory of dimension M and an output POVM. Each pulled-back effect is compressed to a score-preserving rank-one effect bounded by the original effect. Their sum is a positive contraction of trace at most M. Pairing with the dual bounds the score by its largest M eigenvalues, with the sum cut off at the input dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("phase-memory-spectral-tail"),
                DeclarationHandle.Create(Module + "phase_pGuess_spectral_tail_gap"),
                H("The omitted phase amplitudes quantify lost guessing success"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite orthogonal phase ensemble with N labels and total amplitude S, the loss in optimal guessing after compression is at least S/N times the sum of the amplitudes omitted by selecting the largest M amplitudes. The theorem permits equal and zero amplitudes."))),
                DescribeRole.Theorem))));
}
