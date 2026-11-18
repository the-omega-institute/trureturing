using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceNomeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Original Source Nome",
        H("Exact Original Source Nome"),
        Blocks(
            Paragraph(Text("The literal source nome and the original complementary-period nome have the same logarithmic derivative on the entire open real unit interval. The existing Wronskian derivative supplies the period side. Continuity of the original Banach source and inverse column at zero makes the source pairing tend to zero. The existing original_nome_quotient endpoint fixes the ratio constant to one. The strict range follows from F greater than or equal to one at both real arguments.")),
            Describe.Lean(
                DescribeId.Create("original-source-nome"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceNome.original_source_nome"),
                H("original_source_nome"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 0<r<1, r times exp(2 sourceConstant(sqrt(r))) divided by 16 equals the complex embedding of exp(-pi F(1-r)/F(r)), and that real exponential is strictly positive and strictly less than one."))), DescribeRole.Theorem))));
}
