using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ThreeMomentMemoryRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three fixed matrix elements suffice in the exact symmetric two-copy model.",
        H("Three-Moment Memory Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-moment-memory-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/ThreeMomentMemoryRecovery.three_moments_recover_all_lags"),
                H("Actual response moments determine every hidden-return lag"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix any real matrix representation rho on a nonzero finite carrier W. "
                    + "On two copies use the actual symmetric block [[u,v],[v,w]] tensor I, "
                    + "with the first-copy projector fixed. The group acts as I tensor rho; "
                    + "both the operator and observation commute with this action. A single "
                    + "fixed retained coordinate gives moments r1=u, r2=u^2+v^2, "
                    + "r3=u^3+2uv^2+v^2w. The combinations g=r2-r1^2 and "
                    + "z=r3-2r1r2+r1^3 equal v^2 and v^2w. Every actual return kernel is "
                    + "g*w^k*P. If g is zero the kernel is identically zero; otherwise w=z/g. "
                    + "Only times 1,2,3 and one retained coordinate are queried, regardless "
                    + "of dim W. An actual block-power recurrence proves all lags. This "
                    + "constructs neither a Monster representation nor a universal "
                    + "tomography theorem for arbitrary equivariant dynamics."))),
                DescribeRole.Theorem))));
}
