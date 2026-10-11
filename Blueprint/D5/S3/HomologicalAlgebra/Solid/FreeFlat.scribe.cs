using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FreeFlatDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor exactness for the concrete cells used in solidification. The proof uses flat free modules in presheaves and left exact sheafification; it does not assume enough projectives in light condensed abelian groups.",
        H("Free Flat"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-freeflat-tensorfree-preservesfinitelimits"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeFlat.tensorFree_preservesFiniteLimits"),
                H("tensor Free preserves Finite Limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Free light condensed abelian groups are flat, including free groups on arbitrary light condensed sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-freeflat-tensorp-preservesfinitelimits"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeFlat.tensorP_preservesFiniteLimits"),
                H("tensor P preserves Finite Limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Tensoring with the protected `P` is exact. This is a tensor-flatness statement, separate from the protected internal-projectivity instance."))),
                DescribeRole.Theorem))));
}
