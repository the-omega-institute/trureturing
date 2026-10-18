using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class ThreeLinesSchurMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar three-lines interpolation with propagation of equality to the full right boundary.",
        H("Three-lines interpolation and equality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-strip-data"),
                DeclarationHandle.Create(Prefix + "StripData"),
                H("Analytic strip data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "StripData records an entire complex function with a uniform finite norm bound on the closed vertical strip 0≤Re(z)≤1. The data are closed under finite sums, addition and multiplication. Exponentials exp(a z+b) with real slope a have this property, and the API supplies the boundedness required by the three-lines theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("schur-strip-moment-bound"),
                DeclarationHandle.Create(Prefix + "strip_moment_bound_and_equality"),
                H("The scalar interpolation bound and its equality boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M>0. A complex function continuous on the closed strip and differentiable in its interior, bounded there, with left boundary norm at most one and right boundary norm at most M, has norm at most M^(Re z) throughout the strip. If equality occurs at a real interior point theta with 0<theta<1, then the norm equals M at every right boundary point 1+iy. The equality argument applies the maximum modulus principle to exp(−z log M) times the function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-rotating-phase-injective"),
                DeclarationHandle.Create(Prefix + "rotating_phase_injective"),
                H("Rotating phases determine their frequencies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex u,v with u nonzero and real a,b, if u exp(iya)=v exp(iyb) for every real y, then u=v and a=b. Evaluation at zero determines the phase, and equality of derivatives at zero determines the frequency."))),
                DescribeRole.Theorem))));
}
