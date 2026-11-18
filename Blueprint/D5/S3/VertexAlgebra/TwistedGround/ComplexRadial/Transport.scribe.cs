using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial;

internal sealed class TransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Radial Identity Transport", H("Complex Radial Identity Transport"), Blocks(
            Paragraph(Text("The original kernel is holomorphic in the radial amplitude by the compiled all-mode normal-sum derivative theorem. Positive real amplitudes t approach zero inside the exact source disk. Equality supplied at r=t^2 therefore extends by the identity theorem throughout that connected disk. This transport is a consumed helper; the concrete applications discharge its real-supplier premise.")),
            Describe.Lean(DescribeId.Create("kernelmode-eq-candidate-complex-of-real"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Transport.kernelMode_eq_candidate_complex_of_real"), H("kernelMode_eq_candidate_complex_of_real"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("An actual positive-real radial supplier for the selected literal kernel and signed formula implies their equality at every complex z satisfying the original source bounds. All analyticity and denominator facts are derived from those bounds."))), DescribeRole.Theorem))));
}
