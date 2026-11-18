using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class ReductionLocalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arithmetic bounds for exception counting.",
        H("Local factor comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-factor-upper-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.local_factor_upper_bound"),
                H("Local factor upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For kappa at least one, reciprocal r between zero and one half, and exponent a at least one, the normalized local factor is at most (1-r)^(-kappa)(1-r^kappa). Convexity compares equal-length increments of the real power function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint-monotone"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.endpoint_monotone"),
                H("Monotone endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For kappa at least one, the endpoint (1-r)^(-kappa)(1-r^kappa) is nondecreasing with r on [0,1). Writing r/(1-r) as a new coordinate reduces this to monotonicity of unit increments of a convex real power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support-product-le"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal.support_product_le"),
                H("Finite support replacement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A support S of smaller cardinality has no larger product when f(p) is nonnegative for every p in S, every displaced factor is below a boundary value B and every replacement factor is above B, with B at least one. The proof retains the common support and compares the two remaining products through powers of B."))),
                DescribeRole.Theorem))));
}
