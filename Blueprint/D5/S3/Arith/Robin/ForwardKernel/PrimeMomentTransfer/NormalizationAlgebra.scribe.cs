using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class NormalizationAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact normalization identities for positive interval lengths and logarithmic scales.",
        H("Moment normalization algebra"),
        Blocks(
            Describe.Lean(DescribeId.Create("normalizer-powers"), DeclarationHandle.Create(Prefix + "normalizer_powers"), H("Powers of the standard deviation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For positive H and L, both (HL)^(3/2) and (HL)^2 are positive. The third and fourth powers of the square root of HL equal these two quantities, respectively."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cubic-formal-ratio"), DeclarationHandle.Create(Prefix + "cubic_formal_ratio"), H("Cubic formal normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For positive H and L and any real E, dividing E(HL)^(3/2)+HL^2 by (HL)^(3/2) gives E plus the square root of L/H."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourth-formal-ratio"), DeclarationHandle.Create(Prefix + "fourth_formal_ratio"), H("Fourth formal normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For positive H and L and any real E, dividing EH^2L^2+H^2L by (HL)^2 gives E+1/L."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arithmetic-ratio-three"), DeclarationHandle.Create(Prefix + "arithmetic_ratio_three"), H("Cubic arithmetic normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For positive N, H and log N and any real epsilon, N^(1/2+epsilon)H^3 divided by N(H log N)^(3/2) equals N^(-1/2+epsilon)H^(3/2)(log N)^(-3/2)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arithmetic-ratio-four"), DeclarationHandle.Create(Prefix + "arithmetic_ratio_four"), H("Fourth arithmetic normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For positive N, H and log N and any real epsilon, N^(1/2+epsilon)H^4 divided by N(H log N)^2 equals N^(-1/2+epsilon)H^2(log N)^(-2)."))), DescribeRole.Theorem))));
}
