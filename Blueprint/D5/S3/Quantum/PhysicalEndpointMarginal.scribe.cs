using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class PhysicalEndpointMarginalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PhysicalEndpointMarginal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both physical endpoint partial traces of the compact target encoding agree with the corresponding ideal marginals for every logical matrix.",
        H("Physical Endpoint Marginals"),
        Blocks(
            Paragraph(Text(
                "Let d assign a positive finite target rank to every logical sector. "
                + "The compact target encoding places each logical sector in an orthogonal "
                + "maximally entangled block of rank d(s). For an arbitrary complex logical "
                + "matrix Y, encode it on the two physical target factors and trace either "
                + "physical endpoint.")),
            Describe.Lean(
                DescribeId.Create("encoded-target-matrix"),
                DeclarationHandle.Create(Prefix + "encodedTarget"),
                H("Encoded target matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The encoded matrix is targetEncoding(d) multiplied by Y and by the "
                    + "adjoint target encoding. This definition acts on every complex logical matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("target-endpoint-marginal"),
                DeclarationHandle.Create(Prefix + "targetMarginal"),
                H("Ideal endpoint marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ideal marginal is diagonal in the compact physical basis. At a coordinate "
                    + "x it equals the diagonal logical entry Y(s,s) divided by d(s) when the "
                    + "two physical coordinates agree, and is zero otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-target-marginal"),
                DeclarationHandle.Create(Prefix + "right_target_marginal"),
                H("Right endpoint identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Tracing the right physical factor of the encoded target matrix gives the "
                    + "ideal endpoint marginal on the left physical factor for every logical matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("left-target-marginal"),
                DeclarationHandle.Create(Prefix + "left_target_marginal"),
                H("Left endpoint identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Tracing the left physical factor gives the same ideal marginal on the right "
                    + "physical factor for every logical matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-endpoint-marginals"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both physical endpoint identities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two endpoint identities hold together for every positive rank family "
                    + "and every complex logical matrix, including off-diagonal sector entries."))),
                DescribeRole.Theorem)
        )));
}
