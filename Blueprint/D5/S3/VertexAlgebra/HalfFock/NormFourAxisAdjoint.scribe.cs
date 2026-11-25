using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class NormFourAxisAdjointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian adjoints for norm-four axis modes on the actual odd twisted sector.",
        H("Adjoints of the Odd Norm-Four Axis Modes"),
        Blocks(
            Paragraph(Text("Let D be lattice data with unit Gram determinant, and let H be the inherited "
                + "tensor form on the actual negative parity sector. For a charge a and a complex parameter s, "
                + "write L(s,n) for coefficient n + 1 of the negative parity slice of the actual fixed source "),
                Ref("D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.normFourFixedSource"),
                Text(".")),
            Describe.Lean(DescribeId.Create("norm-four-axis-adjoint-mode"),
                DeclarationHandle.Create(Prefix + "mode_adjoint"),
                H("Adjoint with conjugated source parameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If B(a,a) = 4, then H(L(s,n)x,y) = H(x,L(t,−n)y), where t is "
                    + "the complex conjugate of s. This holds for every complex s, integer n, "
                    + "and pair of odd twisted states x and y."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("norm-four-axis-adjoint-ising-mode"),
                DeclarationHandle.Create(Prefix + "ising_mode_adjoint"),
                H("Positive form and opposite-mode adjoints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the real Gram matrix is positive definite, B(a,a) = 4, "
                    + "and s² = 1. The real part of H(x,x) is positive for every nonzero odd twisted x, "
                    + "and H(L(s,n)x,y) = H(x,L(s,−n)y) for all integer n and odd twisted x and y."))),
                DescribeRole.Theorem))));
}
