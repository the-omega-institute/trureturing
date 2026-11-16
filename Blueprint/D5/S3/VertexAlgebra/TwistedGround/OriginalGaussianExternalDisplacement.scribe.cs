using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalDisplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual All-mode Resolvent Displacement",
        H("Actual All-mode Resolvent Displacement"),
        Blocks(
            Paragraph(Text("Weighted bilinear expansions and absolutely convergent products contract the original signed_resolvent_displacement. All four signs and every p=0 or q=0 predecessor remain in the equations. Ordinary bilinear transpose is used throughout.")),
            Describe.Lean(
                DescribeId.Create("modefrequency"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalDisplacement.modeFrequency"),
                H("modeFrequency"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex array on signed natural modes, the mode frequency is alpha times its difference with the actual predecessor."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("external-displacement"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalDisplacement.external_displacement"),
                H("external_displacement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0<=r<1, at z=sqrt(r), the sum of the two actual J mode frequencies equals half the symmetric product of the Rminus and Rplus source pairings. The difference of the two actual T mode frequencies equals half their antisymmetric product. All signed modes are quantified."))), DescribeRole.Theorem))));
}
