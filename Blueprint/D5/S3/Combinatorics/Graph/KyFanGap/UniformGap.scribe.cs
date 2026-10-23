using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class UniformGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/UniformGap.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth moments and uniform bilinear defect gaps.",
        H("Bilinear defect gaps"), Blocks(
            Describe.Lean(DescribeId.Create("kyfan-bilinear-kernel"),
                DeclarationHandle.Create(Owner + "bilinearKernel"),
                H("A diagonal bilinear form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real coefficient vector q and coordinate vectors x,y, the kernel is the sum of q(i)x(i)y(i). It is symmetric in its two arguments. Neither the coefficients nor the coordinate vectors are required to be nonnegative."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kyfan-empirical-defect"),
                DeclarationHandle.Create(Owner + "empiricalDefect"),
                H("Empirical sign and row defects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n coordinate vectors, average the squared sign residual (H(x(r),x(s))^2-1)^2 over ordered pairs, and add the average squared difference between each normalized kernel row sum and c. The first term is separately quartic in the two vectors. The second becomes quadratic in one vector when the empirical coordinate mean is fixed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kyfan-bilinear-defect-gap"),
                DeclarationHandle.Create(Owner + "bilinear_defect_gap"),
                H("A gap independent of sample size"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonsquare coordinate dimension k and every common entry bound M, there is a positive lower bound on the empirical defect at c=1/sqrt(k), uniform over every positive sample size, every real coefficient vector, and every family whose kernel values have absolute value at most M. Fourth-moment compression gives exactly choose(k+4,4)+1 weighted nodes from the family. Powers of the bilinear form expand as finite sums of products of monomials. The first and second defects, and the coordinate mean used in the second, are preserved exactly. The resulting bounded symmetric model is subject to the fixed-order positive defect gap."))),
                DescribeRole.Theorem))));
}
