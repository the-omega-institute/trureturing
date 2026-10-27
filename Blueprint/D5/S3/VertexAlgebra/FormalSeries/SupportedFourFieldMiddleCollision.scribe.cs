using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedFourFieldMiddleCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native middle collision", H("Native middle collision"), Blocks(
            Describe.Lean(DescribeId.Create("supportedfourfieldmiddlecollision-middle-slice-extend"),
                DeclarationHandle.Create(Prefix + "middleSlice_extend"),
                H("Original first and fourth spectators"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any commutative complex algebra and any generally infinite four-variable power series P, the bivariate slice fixes original labels zero and three at arbitrary signed x,y. Its signed extension at v,t is exactly signedExtend P at x,v,t,y, including either negative spectator or active coordinate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedfourfieldmiddlecollision-middle-collision-signed"),
                DeclarationHandle.Create(Prefix + "middleCollision_signed"),
                H("Native substitution at x,b+z,z,y"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed x,b,z,y, the signed coefficient of the legal native substitution P[X0,X1+X2,X2,X3] equals the bivariate collision of the original u,q slice at b,z. The change of labels is the permutation zero,two,three,one and its inverse. The existing four-field native collision supplies the coefficient law after this permutation. Only power series with nonnegative native indices are substituted; arbitrary raw distributions are never substituted. Carnahan attribution for the supported collision supplier is preserved."))), DescribeRole.Theorem))));
}
