using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class ProfileLengthComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/ProfileLengthComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Freezing a variable length for bounded Lipschitz profiles has a quadratic error bound.",
        H("Frozen-length profile comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-factor-square-le"),
                DeclarationHandle.Create(Prefix + "bounded_factor_square_le"),
                H("Square bound for a bounded factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a measurable factor k is bounded in absolute value by C on an interval [a,b], then the square of the integral of k times f is at most C^2 times the interval length times the integral of f^2. The estimate uses the integral triangle inequality followed by Cauchy-Schwarz."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("variable-profile-square-error-le"),
                DeclarationHandle.Create(Prefix + "variable_profile_square_error_le"),
                H("The square error from freezing a profile length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and measurable, let g be an integrable Borel profile bounded by M>=0 and Lipschitz with constant L on [0,1], and let a measurable H lie in [h,h+d] on [a,b], where h>0 and d>=0. If every increment of length u in [0,h+d] has square integral at most V on [a,b], then the square integral of P_H,g minus P_h,g is at most 2*((2M+L)^2+M^2)*d^2*V/h^4. Split the physical interval at h. On its head, the coefficient difference is bounded by (2M+L)*d/h^3; on its tail, the coefficient is bounded by M/h^2. Cauchy-Schwarz bounds both terms, and exchanging the step and starting-point integrals gives the stated constant."))),
                DescribeRole.Theorem))));
}
