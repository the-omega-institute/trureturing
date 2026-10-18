using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class RankOneComplexPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/RankOneComplexPowers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit complex powers of the identity plus the all-ones matrix.",
        H("Complex powers from a rank-one projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-power-H"),
                DeclarationHandle.Create(Prefix + "H"),
                H("The explicit matrix power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural n and complex s, H(n,s) is I plus ((n+1)^s−1) times J/n, where the scalar power is exp(s log(n+1)). For n>0 these matrices multiply by adding exponents, H(n,0)=I, H(n,1)=I+J, and imaginary powers are unitary. The auxiliary positivePower function uses a real logarithm and agrees with Real.rpow on positive bases and real exponents."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-one-power-column-norm"),
                DeclarationHandle.Create(Prefix + "column_norm_sq"),
                H("The column norm and the sharp coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>0 and every real p, each column r_j of H(n,p/2), regarded as a complex Euclidean vector, has squared norm ((n+1)^p+n−1)/n. The inner products of distinct columns are ((n+1)^p−1)/n. For p>0 every pairwise inner product is nonzero, including diagonal pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-one-power-sandwich"),
                DeclarationHandle.Create(Prefix + "sandwich_eq_sum_columns"),
                H("The rank-one expansion of a diagonal sandwich"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural n, real p and complex diagonal d, the matrix H(n,p/2) diag(d) H(n,p/2) is the sum over j of d_j times r_j r_j*. The columns are those of the same explicit Hermitian power. This expansion connects the interpolation matrix to the unitary rank-one trace estimate."))),
                DescribeRole.Theorem))));
}
