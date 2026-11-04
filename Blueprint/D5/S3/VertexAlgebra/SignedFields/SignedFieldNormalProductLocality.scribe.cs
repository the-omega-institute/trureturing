using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SignedFields;

internal sealed class SignedFieldNormalProductLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed normal-product locality", H("Signed normal-product locality"), Blocks(
            Paragraph(Text("The finite-support constructions and residue telescope retain the Scott Carnahan vertexAlg Apache-2.0 attribution of their existing suppliers. The signed proof calculations adapt the actual bc ghost supplier to arbitrary complex modules, while reusing the existing generic PairSpace cancellation kernel and delta-binomial identity. This is classical Dong locality and creative reconstruction, with no literature novelty claim.")),
            Describe.Lean(DescribeId.Create("signed-normal-product-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SignedFields/SignedFieldNormalProductLocality.signedNormal_locality"),
                H("Independent signs and uniform residue cancellation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary complex modules and three fields A,B,C, locality with independent signs x,y,z implies locality of the signed normal product with C and sign yz. The order is Na+Nb+Nc, independent of every input vector. The signed triple pair has the two annihilators required by the existing PairSpace cancellation kernel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-divided-derivative-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SignedFields/SignedFieldNormalProductLocality.signedDerivative_locality"),
                H("Every divided derivative preserves the sign"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The degree d divided derivative of A has locality order N+d against B, with the original sign. A finite-difference Leibniz calculation and the derivative/factorial identity establish the bound. No global support of endomorphism families is assumed."))), DescribeRole.Theorem))));
}
