using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthMeanSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform operator control extends the cell mean-square law to every integrable real profile.",
        H("The moving-length L1 profile law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-profile-operator-bound"),
                DeclarationHandle.Create(Prefix + "moving_profile_operator_bound"),
                H("A uniform L1 to L2 operator bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on compact intervals, and let 0<alpha<theta<beta<1 satisfy the uniform cumulative variance asymptotic. There is C>0 and one threshold independent of g such that the L2 norm of the moving average P_(x^theta,g) on [X,2X] is at most C times the L1 norm of g times sqrt(X^(1-theta) log X). Weighted scalar Cauchy-Schwarz and Fubini reduce this to the uniform moving-increment square bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-profile-mean-square-tendsto"),
                DeclarationHandle.Create(Prefix + "moving_profile_mean_square_tendsto"),
                H("The full integrable-profile limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same variance band hypothesis, for every real integrable Borel profile g, the square integral of P_(x^theta,g)(x) on [X,2X], divided by X^(1-theta) log X, tends to Q(g)(2^(1-theta)-1). First take a Lipschitz profile, fix n equal cells, and freeze the length at each left endpoint. The head and tail dilation estimate bounds the normalized total square error by a constant depending on g divided by n. The fixed-cell limits and the convergent rectangle constants then give the limit. Approximate a general profile in L1 by Lipschitz profiles. The uniform operator bound and the inequality |sqrt(Q(g))-sqrt(Q(f))| <= ||g-f||_1 control the two approximation errors, taking X to infinity before the approximation parameter."))),
                DescribeRole.Theorem))));
}
