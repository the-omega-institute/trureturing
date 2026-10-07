using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureComparisonBoundedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete bounded tail, descent and two-sided inverse of the protected P-measure unit in the derived-local reflector. Exact proofs are retained from the reviewed constructor at its existing component boundary. Apache-2.0; research construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Lemma 3.3.3.",
        H("Bounded Measure Comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measurecomparisonbounded-boundedmeasuretail-tensorsquare"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureComparisonBounded.boundedMeasureTail_tensorSquare"),
                H("Bounded tail tensor square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual bounded tail descends through the defining finite-difference tensor square, supplying the first inverse identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measurecomparisonbounded-localboundedmeasureiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureComparisonBounded.localBoundedMeasureIso"),
                H("Derived-local bounded measure equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine two-sided inverse identifies the reflected protected P with the reflected bounded integer measures. The integer-quotient continuation consumes this equivalence."))),
                DescribeRole.Definition))));
}
