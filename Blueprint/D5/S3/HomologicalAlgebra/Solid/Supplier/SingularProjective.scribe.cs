using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid.Supplier;

internal sealed class SingularProjectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Singular Projective"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-singularprojective-singularchains-qh-map-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Supplier/SingularProjective.singularChains_Qh_map_bijective"),
                H("singular Chains Qh map bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Morphisms from protected singular chains into any derived object represented in the homotopy category are precisely homotopy classes of chain maps."))),
                DescribeRole.Theorem))));
}
