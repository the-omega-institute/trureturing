using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class CreationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual odd-weight creation exponential satisfies the native polynomial derivation law.",
        H("Half-Integer Creation Derivatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("halfexponentialderivation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Creation.half_exponential_derivation"),
                H("Coefficientwise Exponential Chain Rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every complex-linear polynomial derivation extends coefficientwise through the original halfCreationExponential. The difference between the two sides has zero constant coefficient and satisfies the same formal differential equation as the exponential. Induction on the coefficient degree proves that every coefficient of this difference vanishes. This is an algebraic statement about formal series; it uses no analytic convergence or occupation cutoff. The coefficientwise derivation and its commutation with formal differentiation are reused from ActualSeriesDerivation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("halfannihilationlogarithm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Creation.half_annihilation_logarithm"),
                H("Exact Odd-Weight Logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original Gram-weighted annihilation derivative selects precisely the variable at odd Laurent weight 2n+1. Its logarithm coefficient is 2/(2n+1) times the integral Gram pairing with the charge. All even coefficients vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("halfannihilationcreation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Creation.half_annihilation_creation"),
                H("Unrestricted Integer Creation Coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer coefficient degree, annihilation shifts the degree by the original odd weight. The coefficient factor remains 2/(2n+1) times the original Gram pairing. Negative creation coefficients are zero, and the coefficient formula handles the insufficient-degree case explicitly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("halfcurrentcreation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Creation.half_current_creation"),
                H("Native Current Normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive half-integer current multiplies the Gram-weighted derivative by n+1/2. This cancels the factor 2/(2n+1), leaving exactly the integral Gram pairing. Creation multiplication transpose uses this normalization and the negative BPZ creator adjoint."))),
                DescribeRole.Theorem))));
}
