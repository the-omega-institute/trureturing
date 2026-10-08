using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedHomTriangleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. The actual Hom diagram chase needed to extend the protected generator comparison through finite complex filtrations. This proves a transfer across a distinguished triangle; it assumes no derived adjunction, unbounded resolution, or full faithfulness of the functor. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1. The chase uses Mathlib's proved yoneda exactness at commit 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22 (Joël Riou, Apache-2.0).",
        H("Derived Hom Triangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedhomtriangle-maphom-bijective-triangle-middle"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedHomTriangle.mapHom_bijective_triangle_middle"),
                H("map Hom bijective triangle middle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A five-term Hom chase, with the comparison the literal functor map. Only the four adjacent source Hom comparisons are used."))),
                DescribeRole.Theorem))));
}
