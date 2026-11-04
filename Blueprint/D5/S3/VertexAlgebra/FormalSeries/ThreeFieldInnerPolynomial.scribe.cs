using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldInnerPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inner clearing and supported cancellation", H("Inner clearing and supported cancellation"), Blocks(
            Describe.Lean(DescribeId.Create("inner-polynomial"),
                DeclarationHandle.Create(Prefix + "innerPolynomial"),
                H("The literal original multiplier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The multiplier is x^a0 (x-b-z)^k (x-z)^k b^k (b+z)^a1 z^a2 in the original x,b,z coordinates. Its action is the existing finite Laurent-polynomial convolution."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inner-action-expansion"),
                DeclarationHandle.Create(Prefix + "inner_action_expansion"),
                H("Finite original clearing expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The accepted polynomial expansion gives the p,q,h finite action formula on an arbitrary signed coefficient distribution. No support premise is used for multiplication."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inner-action-rotate"),
                DeclarationHandle.Create(Prefix + "inner_action_rotate"),
                H("Reordering coefficient arguments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reordering the exponent arguments as b,z,x conjugates the literal polynomial action to the rotated multiplier. This is a coordinate reorder on coefficients, with no substitution into an unrestricted distribution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inner-injective"),
                DeclarationHandle.Create(Prefix + "inner_injective"),
                H("Cancellation in the b-small chamber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two distributions with a uniform lower b bound and, for each b, a lower z bound uniform in x are equal when the original clearing actions agree. Induction in b removes the preceding row of the x-b-z recurrence. The remaining x-z recurrence is cancelled using the current row's own z bound and supported_reconstruction. Finite powers preserve this nested support. Neither a uniform x cutoff nor a global z cutoff is required. Zero exponents and the zero complex algebra remain included."))), DescribeRole.Theorem))));
}
