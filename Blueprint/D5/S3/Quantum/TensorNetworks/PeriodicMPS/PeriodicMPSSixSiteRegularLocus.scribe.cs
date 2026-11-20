using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteRegularLocusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuation of a separated six-site observation fiber",
        H("Continuation of a separated six-site observation fiber"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteregularlocus-compact-generic-recovery-of-separated-fiber"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteRegularLocus.compact_generic_recovery_of_separated_fiber"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A critical cover and separation at one good compact fiber give a relatively open dense locus of singleton observation fibers."))), DescribeRole.Theorem))));
}
