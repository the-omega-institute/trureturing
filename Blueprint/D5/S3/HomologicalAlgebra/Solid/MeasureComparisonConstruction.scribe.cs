using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureComparisonConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete bounded inverse, dyadic integer-quotient cancellation and canonical P-measure comparison. The bounded inverse and integer-quotient continuation are separate compilation units at their existing component boundary. All new proofs are Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4. Immutable formal suppliers retain their source/commit/license identities. No DSolid realization or original HasLeftDerivedFunctor/derived adjunction is assumed.",
        H("Measure Comparison Construction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measurecomparisonconstruction-localptointegermeasures-isiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureComparisonConstruction.localPToIntegerMeasures_isIso"),
                H("local PTo Integer Measures is Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The required concrete P-measure computation is unconditional. It is an equivalence in Dlocal, and does not identify Dlocal with DSolid."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measurecomparisonconstruction-localintegermeasureiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureComparisonConstruction.localIntegerMeasureIso"),
                H("local Integer Measure Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Concrete bounded inverse, dyadic integer-quotient cancellation and canonical P-measure comparison. The bounded inverse and integer-quotient continuation are separate compilation units at their existing component boundary. All new proofs are Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4. Immutable formal suppliers retain their source/commit/license identities. No DSolid realization or original HasLeftDerivedFunctor/derived adjunction is assumed."))),
                DescribeRole.Definition))));
}
