using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureOrdinaryReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatibility of the actual canonical P-measure computation with the protected ordinary reflection unit. This does not assert DSolid realization, derived full faithfulness or the existence of an unbounded derived adjunction. New proofs, Apache-2.0; the generator route follows Rodriguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.",
        H("Measure Ordinary Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measureordinaryreflection-solidptointegermeasures-unit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureOrdinaryReflection.solidPToIntegerMeasures_unit"),
                H("solid PTo Integer Measures unit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Compatibility of the actual canonical P-measure computation with the protected ordinary reflection unit. This does not assert DSolid realization, derived full faithfulness or the existence of an unbounded derived adjunction. New proofs, Apache-2.0; the generator route follows Rodriguez Camargo, Notes on Solid Geometry, Theorem 3.3.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measureordinaryreflection-solidptointegermeasures-isiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureOrdinaryReflection.solidPToIntegerMeasures_isIso"),
                H("solid PTo Integer Measures is Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Compatibility of the actual canonical P-measure computation with the protected ordinary reflection unit. This does not assert DSolid realization, derived full faithfulness or the existence of an unbounded derived adjunction. New proofs, Apache-2.0; the generator route follows Rodriguez Camargo, Notes on Solid Geometry, Theorem 3.3.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measureordinaryreflection-solidpintegermeasuresiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureOrdinaryReflection.solidPIntegerMeasuresIso"),
                H("solid PInteger Measures Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Compatibility of the actual canonical P-measure computation with the protected ordinary reflection unit. This does not assert DSolid realization, derived full faithfulness or the existence of an unbounded derived adjunction. New proofs, Apache-2.0; the generator route follows Rodriguez Camargo, Notes on Solid Geometry, Theorem 3.3.1."))),
                DescribeRole.Definition))));
}
