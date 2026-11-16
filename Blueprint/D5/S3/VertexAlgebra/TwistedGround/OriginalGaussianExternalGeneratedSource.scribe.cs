using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalGeneratedSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Generated Source Displacement", H("Signed Generated Source Displacement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundary-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.boundary_normalization"),
                H("boundary_normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 0<r<1, sqrt(1-r) times the actual sourceAmplitude(false,0,r) equals one. The actual analytic binomial branch supplies this normalization."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("modescale"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeScale"),
                H("modeScale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either signed label and complex u, modeScale is 1 for the positive label and u for the negative label. This polynomial multiplier preserves the negative zero-mode boundary without dividing by u."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("modea"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeA"),
                H("modeA"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either label and complex u,x, modeA is the scaled actual U amplitude: positive (1-2u+(1-x)u squared)/(2(1-(1-x)u)), negative u(1-u)/(2(1-x-u))-1/2."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("modeb"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeB"),
                H("modeB"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either label modeB is the scaled boundary coefficient, positive 1/2 and negative -1/2."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("modeh"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.modeH"),
                H("modeH"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either label and complex u,x,lambdaRatio, modeH is the scaled diagonal jet amplitude: positive -xu/(1-(1-x)u), negative xu/(1-x-u), in either case minus modeA and minus 2x modeScale lambdaRatio."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("external-displacement-generated"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_displacement_generated"),
                H("external_displacement_generated"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed labels, 0<r<1 and norm(u)+r,norm(v)+r<1, the complete double mode series of the original J frequency sum and original T frequency difference converge to (1-r)(UV+VU)/2 and (1-r)(UV-VU)/2, respectively. Every summand carries both modeScale multipliers and u to p times v to q. Here U=M modeA-modeB Aminus(0), V=M modeH+modeB Aminus(0), x=r and lambdaRatio is the original period logarithmic derivative. These are genuine normally convergent source displacement sums; identification of the left sums with differential operators on J/T remains separate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-negative-zero-generated"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_negative_zero_generated"),
                H("external_negative_zero_generated"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either remaining label, 0<r<1 and norm(u)+r<1, the complete original negative-zero J row with modeScale weight sums to sqrt(1-r)/2 times M(modeH-modeA) plus modeB. The actual binomial branch proves sqrt(1-r) Aminus(0)=1. The original negative-zero T row sums to sqrt(1-r)/2 times M(modeH+modeA). The T identity contribution is included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-radial-generated"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.external_radial_generated"),
                H("external_radial_generated"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed labels, 0<r<1 and norm(u)+r,norm(v)+r<1, the complete scaled two-mode T radial remainder sums to (1-r)(VV-UU)/2. The summand is 2r times the actual fixed-mode radial derivative minus both frequency actions, with both modeScale factors and u/v powers. U,V are the same literal source amplitudes as in the displacement sums. This does not yet exchange the radial derivative with the complete two-mode T sum."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernelmode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode"),
                H("kernelMode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For three Boolean labels and complex u,v,z, this is the literal full two-mode tsum of externalT when square is true and externalJ otherwise, with u to p times v to q. It assumes no candidate kernel value."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kernelmode-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource.kernelMode_derivative"),
                H("kernelMode_derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either original J or T and all signed modes, norm(u)+norm(z)<1 and norm(v)+norm(z)<1 justify the complex derivative in u. The series of p times the original kernel coefficient times u to p-minus-one times v to q has that derivative as its sum. Normal convergence is proved on an intermediate mode disk from the actual bilinear contraction bound."))), DescribeRole.Theorem))));
}
