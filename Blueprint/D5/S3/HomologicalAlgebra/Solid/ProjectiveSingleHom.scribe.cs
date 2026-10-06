using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ProjectiveSingleHomDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Projective Single Hom"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-projectivesinglehom-derivedsinglehomologymap-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ProjectiveSingleHom.derivedSingleHomologyMap_bijective"),
                H("derived Single Homology Map bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every target in the unbounded derived category is allowed. No replacement hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-projectivesinglehom-projectivesinglehomequiv-naturality"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ProjectiveSingleHom.projectiveSingleHomEquiv_naturality"),
                H("projective Single Hom Equiv naturality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem))));
}
