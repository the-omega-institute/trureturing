using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class TypedJacobianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.",
        H("TypedJacobian"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-message-product"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.messageProduct"),
                H("messageProduct"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Product over precisely the retained children; an empty product is one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-log-argument"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.logArgument"),
                H("logArgument"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The single log argument. It is positive on the real box and has no vanishing issue at activity zero, where it equals b0-a0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-row-map"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap"),
                H("rowMap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual transformed hard-core map. There is no logarithm of the activity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-jacobian-entry"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.jacobianEntry"),
                H("jacobianEntry"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coefficients of the full differential in the child coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-activity-entry"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.activityEntry"),
                H("activityEntry"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coefficient of activity variation in the same differential."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-row-map-has-deriv-at"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_hasDerivAt"),
                H("rowMap hasDerivAt"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative along every differentiable complex input curve. Since both activity and all child tangent values are arbitrary, this identifies the full Jacobian, including mixed simultaneous input perturbations and all pruning sets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-row-map-differentiable-at"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.rowMap_differentiableAt"),
                H("rowMap differentiableAt"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Joint holomorphy of the actual finite-dimensional map on its pole-free principal-log domain; it is not inferred just from a pointwise Jacobian fit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-inverse-row-map"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.inverse_rowMap"),
                H("inverse rowMap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inverse coordinates return the actual vacancy recursion. Both possible rational poles are stated; the quantitative tube later excludes them uniformly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-holo-typedjacobian-jacobian-vacancy-identity"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/TypedJacobian.jacobian_vacancy_identity"),
                H("jacobian vacancy identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Jacobian entry is exactly the previously certified message ratio. This is a rational identity; no assumed derivative identification is used."))), DescribeRole.Theorem))));
}
