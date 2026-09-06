using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class ProjectiveReadoutSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Least-energy cancellation and the exact robustness threshold for a scalar readout.",
        H("Projective Readout Sharpness"),
        Blocks(
            Describe.Lean(DescribeId.Create("least-energy-cancellation"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveReadoutSharpness.least_energy_readout_cancellation"), H("Construct the least-energy cancelling error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs an actual candidate-orthogonal perturbation along the projected readout representer, proves exact cancellation, computes its energy and proves minimal energy among all cancelling perturbations. This sharpness concerns the Hilbert error ball, not the subset of errors realized by a fixed arithmetic operator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robust-nonvanishing-iff"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveReadoutSharpness.robust_readout_nonvanishing_iff"), H("Exact robust nonvanishing criterion"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonvanishing for every perturbation in the closed orthogonal error ball is equivalent to the strict centered readout margin. Both zero-radius and zero-orthogonal-component cases are included. The forward direction constructs a failure witness whenever the margin fails."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("angle-criterion"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveReadoutSharpness.robust_readout_angle_iff"), H("Squared overlap threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rewrites the same sharp condition as delta times the readout norm squared being less than (1+delta) times the squared candidate overlap. This gives the form directly consumed by rational numerical certificates."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout"))]));
}
