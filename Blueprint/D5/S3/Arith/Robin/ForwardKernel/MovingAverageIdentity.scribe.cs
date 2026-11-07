using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingAverageIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingAverageIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A forward change of variables decomposes the average of E(x+s*x^a)-E(x) into three increment terms.",
        H("Forward substitution for a moving increment average"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-average-forward-identity"),
                DeclarationHandle.Create(Prefix + "moving_average_forward_identity"),
                H("The three-term forward identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on compact intervals, a>0, s>=0, x>0, and M>0. Write L(y)=s*y^a, Lprime(y)=s*a*y^(a-1), phi(y)=y+L(y), Q0=x+M+L(x), and delta=L(x+M)-L(x). Then M times the M-window average of the moving increment equals the integral of D_M E(x+r) from zero to L(x), minus the integral of Lprime(x+r)*(E(phi(x+r))-E(x)) from zero to M, plus the integral of E(Q0+v)-E(x) from zero to delta. Forward substitution uses the nonnegative derivative of phi. The fundamental theorem of calculus gives the integral of Lprime(x+r) as delta, so the constant E(x) cancels between the two correction terms. No continuity or derivative of E is required."))),
                DescribeRole.Theorem))));
}
