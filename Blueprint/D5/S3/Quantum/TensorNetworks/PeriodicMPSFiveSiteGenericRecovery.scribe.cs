using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteGenericRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteGenericRecovery";
    private static LibraryNoteRef MarginalSource =>
        LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");
    private static LibraryNoteRef TraceSource =>
        LibraryNoteRef.Create("D5/L/Geometry/czaplinskimichalekseynnaeve2023umps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic five-site recovery from one adjacent marginal",
        H("Generic five-site recovery from one adjacent marginal"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitegenericrecovery-result"),
            DeclarationHandle.Create(Module + ".generic_rawTwo_unitPhase_recovery"),
            H("Generic five-site recovery from one adjacent marginal"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(MarginalSource, TraceSource),
            Blocks(
                Paragraph(Text("The locus is relatively open and dense in the actual unit-mass five-site periodic binary bond-two amplitude image. Equality of the adjacent two-site marginals with any periodic binary bond-two competitor forces equality of the full amplitudes up to unit phase. The marginal trace gives the competitor's unit mass.")),
                Paragraph(Text("The proof removes the boundary and critical observations from a compact extension of the ordinary trace chart. A classified four-point fiber and four distinct normal cubic coefficients separate the local analytic branches. Analytic continuation on the path-connected regular locus gives generic recovery.")),
                Paragraph(Text("The conclusion concerns the physical marginal at length five. The cited trace-parametrization theorem starts with the full amplitude and addresses core invariants."))),
            DescribeRole.Theorem))));
}
