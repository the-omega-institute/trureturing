using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ProjectiveHomCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Projective Hom Compatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-projectivehomcompatibility-exactderivedhomology-single"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ProjectiveHomCompatibility.exactDerivedHomology_single"),
                H("exact Derived Homology single"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-projectivehomcompatibility-derivedsinglehomologymap-exact"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ProjectiveHomCompatibility.derivedSingleHomologyMap_exact"),
                H("derived Single Homology Map exact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem))));
}
