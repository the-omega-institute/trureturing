using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform cumulative variance controls the moving-length strip.",
        H("Uniform cumulative variance controls the moving-length strip"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-strip-variance-bound"),
                DeclarationHandle.Create(Prefix + "moving_strip_variance_bound"),
                H("Uniform variance on the length strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If E is measurable and locally bounded and its cumulative variance has the uniform asymptotic Y u log(Y/u) throughout Y^(3/4)<=u<=Y^(7/8), then eventually every u in [X^(4/5),4X^(4/5)] has increment square integral on [X,2X] at most 32 X X^(4/5) log X. At Y=2X the whole strip eventually lies in the variance band. The cumulative variance bounds the dyadic integral, and log(2X/u)<=2 log X."))),
                DescribeRole.Theorem))));
}
