using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedGeneratorSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. Full faithfulness of the exact protected derived inclusion on arbitrary small sums of the concrete generator, in every integer degree and against arbitrary unbounded solid targets. The sums are actual colimits, and the comparison is the literal derivedInclusion.map. No all-source full faithfulness, realization, or derived adjunction is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.",
        H("Derived Generator Sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedgeneratorsums-derivedinclusion-generatorcopower-map-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedGeneratorSums.derivedInclusion_generatorCopower_map_bijective"),
                H("derived Inclusion generator Copower map bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the actual map on derived morphisms from any generator copower, for every integer n and every arbitrary unbounded target."))),
                DescribeRole.Theorem))));
}
