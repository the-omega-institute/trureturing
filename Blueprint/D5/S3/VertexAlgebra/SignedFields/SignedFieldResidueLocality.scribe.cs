using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SignedFields;

internal sealed class SignedFieldResidueLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed all-integer residue calculus", H("Signed all-integer residue calculus"), Blocks(
            Paragraph(Text("The finite-support constructions and residue telescope retain the Scott Carnahan vertexAlg Apache-2.0 attribution of their existing suppliers. The signed proof calculations adapt the actual bc ghost supplier to arbitrary complex modules, while reusing the existing generic PairSpace cancellation kernel and delta-binomial identity. This is classical Dong locality and creative reconstruction, with no literature novelty claim.")),
            Describe.Lean(DescribeId.Create("signed-all-integer-dong-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_locality"),
                H("Dong locality for every integer residue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary fields and independent AB,AC,BC signs x,y,z, every integer signed residue of A and B is local with C with sign yz. Nonnegative residues are boundaries of shifted signed triple pairs. Residue degree -d-1 is the signed normal product of the degree d divided derivative of A and B. Each coefficient sum has finite support after application to a vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-residue-translation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_translation"),
                H("Original translation passes through the residue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If both input fields are covariant under the same endomorphism T, every signed integer residue is covariant under that T. Integer-binomial recurrence and vectorwise finite telescopes justify all reindexing and sum exchanges."))), DescribeRole.Theorem))));
}
