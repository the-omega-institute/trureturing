using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class GaussianCoefficientScalingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientScaling.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GaussianCoefficientScaling", H("GaussianCoefficientScaling"), Blocks(
            Paragraph(Text("Diagonal congruence scales each ordinary Gaussian coefficient by the product of its coordinate weights. Principal supports extend this identity to arbitrary index types.")),
            N("finite_diagonal_congruence","Exact finite diagonal congruence","Substitute X_i by w_i X_i in the actual quadratic Q_K=(1/2) sum_ij K_ij X_i X_j. The algebra homomorphism preserves powers and the scalar 1/n!, while each monomial acquires product_i w_i^d_i. Thus the ordinary gaussianCoefficient transforms by precisely that factor. Zero scalars and odd occupations are included."),
            N("diagonal_congruence","Principal-support scaling","Compute the actual InfiniteGaussianFock.coefficient on the finite principal support of the occupation. Injective mapDomain preserves the product of the diagonal weights. This transfers the finite identity to any index type, with no enumeration or analytic premise."),
            N("external_scaling","Scaling the external occupation","Take w=t on external modes and w=1 on internal modes. The exact occupation splitting gives c_(D K D)(d,n)=t^degree(d)c_K(d,n). External coefficients remain ordinary; the internal factorial weight is unchanged.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("gaussiancoefficientscaling-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
