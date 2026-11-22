using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformCollisionTaylorDocument : IScribeDocumentDefinition
{
    private const string Title = "Normalized Taylor polynomial at the fourfold collision";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcollisiontaylor-charpoly-sq-dvd-taylor-sub"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCollisionTaylor.charpoly_sq_dvd_taylor_sub"),
                H("The binomial tail lies in the squared characteristic ideal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every omitted term has a factor of the eighth power of the centered coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformcollisiontaylor-taylor-ambient-jet"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCollisionTaylor.taylor_ambient_jet"),
                H("Evaluation on arbitrary colliding matrix lifts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The degree-seven polynomial evaluates to the normalized literal power on every dual perturbation of a transfer with fourfold weight one quarter."))),
                DescribeRole.Theorem))));
}
