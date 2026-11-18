using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMChargeGermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The negative-square coordinate of the original four-point Laurent diagonal.",
        H("The Original Four-Point Germ in the Negative Square"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourm-diagonal-sewn"), DeclarationHandle.Create(Prefix + "diagonalSewn"),
                H("Projected sewn charge sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each external occupation, sum the native sewn terms over the chosen mod-two charge class. "
                    + "Apply the finite lowering powers, signed factorial weights and Laurent selectors to those "
                    + "sums. On the diagonal t = E + t₀, both Laurent exponents decrease by 2E and the selectors "
                    + "reduce to their degree-zero forms. The homogeneous right weights L and N give t₀ = L − N − 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-coset-negative-square"),
                DeclarationHandle.Create(Prefix + "cosetSeries_negative_square_germ"),
                H("Negative-square descent for each charge class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normal convergence makes each fixed-occupation charge-class sum holomorphic near zero. "
                    + "The native Taylor formula uses the finite charge sublevel at total energy E. "
                    + "After finite lowering and projection, averaging the values at z and −z keeps order 2E "
                    + "and cancels the odd powers. In the variable −z² the degree-E coefficient is the "
                    + "original coset coefficient at t = E + t₀ multiplied by (−1)ᴱ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-scalar-negative-square"),
                DeclarationHandle.Create(Prefix + "fourM_scalar_negative_square_germ"),
                H("Taylor series of the original four-point scalar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the actual rank-24 parity and homogeneous left-state hypotheses, weight each "
                    + "descended coset by the ordered left and right ground forms and sum over charge classes. "
                    + "The resulting holomorphic germ has Taylor coefficients equal to the original four-point "
                    + "scalar at Laurent indices k = H + K − E − 1 and t = E + t₀ for every natural E. "
                    + "Its pullback near zero is the same ground-weighted sum of the actual sewn even parts."))),
                DescribeRole.Theorem))));
}
