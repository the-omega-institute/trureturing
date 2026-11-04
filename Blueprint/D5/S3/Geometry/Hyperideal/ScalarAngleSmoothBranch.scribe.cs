using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class ScalarAngleSmoothBranchDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The raw scalar cosine branch is smooth while its clipped angle has an endpoint cusp.",
        H("Smooth raw cosine versus singular clipped angle"),
        Blocks(
            Paragraph(Text(
                "On the length slice used in Section 68, the first-slot raw cosine is "
                + "the elementary function (8-cosh(s))/9. It is differentiable for every "
                + "real length parameter. The preceding cusp theorem shows that applying "
                + "the clipped arccosine at the endpoint still defeats every finite scalar "
                + "linear bound.")),
            Paragraph(Text(
                "This separates the smoothness of the raw cosine from the endpoint behavior "
                + "of the extension angle. It is a scalar regularity statement only: it does "
                + "not assert a global face pairing, a global curvature field, a complete "
                + "flow theorem, or a uniqueness result.")),
            Describe.Lean(
                DescribeId.Create("scalar-length-raw-cosine-reduction"),
                DeclarationHandle.Create(Prefix + "scalarLengthRawCosine_eq"),
                H("Exact raw cosine on the length slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The six-variable formula reduces exactly to (8-cosh(s))/9 when "
                    + "the varying slot is the fourth coordinate and the other five "
                    + "coordinates are fixed at 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-length-raw-cosine-smooth"),
                DeclarationHandle.Create(Prefix + "scalarLengthRawCosine_differentiable"),
                H("The raw scalar cosine is differentiable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differentiability follows from the exact reduction and the standard "
                    + "differentiability of the hyperbolic cosine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth-raw-branch-cusp-angle"),
                DeclarationHandle.Create(Prefix + "smooth_raw_branch_but_angle_not_parameter_lipschitz"),
                H("Smooth raw branch with an unbounded clipped-angle ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The combined theorem places the differentiable raw branch beside the "
                    + "previously proved endpoint cusp: for every finite nonnegative K, "
                    + "some epsilon in (0,1) has an angle gap larger than K times "
                    + "epsilon divided by sqrt(255)."))),
                DescribeRole.Theorem))));
}
