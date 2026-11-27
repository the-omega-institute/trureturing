using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.RecordWriting;

internal sealed class LocalBathWeakRecordingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/chung2026thermodynamicobjectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cost bound for weak records under local bath steps and collective reversible control.",
        H("Weak recording with local baths"),
        Blocks(Describe.Lean(
            DescribeId.Create("collective-local-bath-bound"),
            DeclarationHandle.Create(Module + "recording_bound"),
            H("The cost of several readable coordinates"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "Each conditional register law starts uniform. A scheduled bath uses the same "
                + "two-state transition probabilities in all fibers of one bit and satisfies an edgewise "
                + "charge bound. The protocol may apply joint reversible permutations in either branch. "
                + "The cost multiplies the branch-averaged transition activity by the branch-averaged "
                + "certified edge charge. The logarithmic specialization evaluates the two fluxes "
                + "at the input law of the step. Total bath variation controls the largest departure from uniform, and the "
                + "single-bit geometry bounds the Euclidean speed from the two bath costs. "
                + "Orthogonality of the coordinate signs gives a lower coefficient of R/2 "
                + "for the squared common Bayes bias in the weak-recording limit at fixed dimension."))),
            DescribeRole.Theorem))));
}
