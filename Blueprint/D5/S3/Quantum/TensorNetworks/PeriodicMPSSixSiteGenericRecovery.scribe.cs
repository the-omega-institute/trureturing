using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSSixSiteGenericRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSSixSiteGenericRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic six-site recovery from one adjacent marginal",
        H("Generic six-site recovery from one adjacent marginal"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitegenericrecovery-result"),
            DeclarationHandle.Create(Module + ".generic_rawTwo_unitPhase_recovery"),
            H("Generic six-site recovery from one adjacent marginal"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps"),
                LibraryNoteRef.Create("D5/L/Geometry/czaplinskimichalekseynnaeve2023umps")),
            Blocks(
                Paragraph(Text("The target belongs to a relatively Euclidean-open dense locus of the actual unit-mass six-site periodic binary bond-two amplitude image. Every actual competitor with the same adjacent two-site marginal has the same full amplitude up to a unit phase. The marginal trace supplies its mass.")),
                Paragraph(Text("The proof compactifies the cubic invariant map on the quadric cone of weight-two trace data. It classifies one complete two-point observation fiber and distinguishes the two local image germs by their normal cubic coefficients.")),
                Paragraph(Text("The critical and compact boundary values admit differentiable covers of real dimension at most six. The two selected critical minors are certified by full-degree line restrictions and a residue-field Bézout identity. Removing the fibers over excluded values leaves a connected regular locus on which the local separation propagates.")),
                Paragraph(Text("The result addresses the six-site case of the physical marginal reconstruction question. The full-tensor inversion theorem of Czapliński, Michałek and Seynnaeve addresses the recovery of core invariants from the full amplitude."))),
            DescribeRole.Theorem))));
}
