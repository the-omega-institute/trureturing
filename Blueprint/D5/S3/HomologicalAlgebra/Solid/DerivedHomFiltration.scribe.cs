using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedHomFiltrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. Extension of the literal generator comparison to every unbounded DSolid source. The inputs are the actual kernel resolution, finite lower layers, and the two actual truncation telescopes. No generation, replacement, derived full faithfulness, or derived adjunction is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1. This file is a proof attempt until a matching compiler/audit receipt exists.",
        H("Derived Hom Filtration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedhomfiltration-derivedinclusion-map-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusion_map_bijective"),
                H("derived Inclusion map bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal protected derived inclusion is bijective on morphisms from EVERY unbounded source to EVERY unbounded target. The proof uses the constructed generator resolution and both actual telescopes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedhomfiltration-derivedinclusionfullyfaithful"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration.derivedInclusionFullyFaithful"),
                H("derived Inclusion Fully Faithful"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual full-faithfulness data, with inverse induced by the proved literal-map bijection. No full-faithfulness premise is introduced."))),
                DescribeRole.Definition))));
}
