using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Signed;

internal sealed class SpatialUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Spatial Uniqueness",
        H("Signed Spatial Uniqueness"),
        Blocks(
            Paragraph(Text("Let F be jointly complex differentiable on the bidisk of radius R, where 0<R<=1. In each J or T sector with at least one negative label, the homogeneous spatial equation forces F to vanish on the whole bidisk. Both axes, the origin and the diagonal are included; no separate boundary value is assumed.")),
            Paragraph(Text("For a negative first label, four rational characteristic paths remain in the bidisk on a sufficiently small first-coordinate disk. The equation forces the initial axis value to vanish. A squared integrating factor makes h squared times P divided by the path parameter constant; differentiability removes its singularity at zero. The endpoint value is zero. Analytic uniqueness extends each slice, continuity supplies the missing zero slice, and coordinate interchange treats a negative second label.")),
            Describe.Lean(DescribeId.Create("signed-spatial-zero"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness.signed_spatial_zero"), H("signed_spatial_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For either J or T and either pair of labels with at least one negative label, joint differentiability and the literal homogeneous spatial equation imply F(u,v)=0 for all norm(u)<R and norm(v)<R, provided 0<R<=1."))), DescribeRole.Theorem)
        )));
}
