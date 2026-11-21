using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteGenericRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGenericRecovery";
    private const string Title = "Generic seven-site recovery from one adjacent two-site density";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitegenericrecovery-result"),
            DeclarationHandle.Create(Module + ".generic_twoSite_recovery"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps"),
                LibraryNoteRef.Create("D5/L/Geometry/czaplinskimichalekseynnaeve2023umps")),
            Blocks(
                Paragraph(Text("A nonzero periodic binary bond-two tensor gives a rank-one state projector. A relatively Euclidean-open dense subset of the compact closure consists of actual projectors. One adjacent two-site marginal identifies each target in this subset against every competitor in the compact closure.")),
                Paragraph(Text("The weighted trace graph supplies the ordinary chart and a compact boundary of Hausdorff dimension at most six. Two certified critical minors give a codimension-two bound on the remaining rank defects. Six seven-letter trace contrasts identify the compact lift over an open neighborhood of the hard-core state. The locally unique fibers seed analytic continuation on the connected regular region.")),
                Paragraph(Text("The reconstruction uses a static partial trace. Its hypotheses involve the ring length, the bond dimension, and the periodic trace-word family."))),
            DescribeRole.Theorem))));
}
