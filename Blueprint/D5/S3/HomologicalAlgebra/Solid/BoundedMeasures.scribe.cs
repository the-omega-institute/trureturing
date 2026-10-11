using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class BoundedMeasuresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual bounded-coefficient tensor square for the protected measure map. New proofs, Apache-2.0. This implements the uniformly bounded-family part of Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.3.",
        H("Bounded Measures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-boundedmeasures-boundedcoefficientmap-coordinate"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedMeasures.boundedCoefficientMap_coordinate"),
                H("bounded Coefficient Map coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual bounded-coefficient tensor square for the protected measure map. New proofs, Apache-2.0. This implements the uniformly bounded-family part of Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-boundedmeasures-boundedmeasuretensorsquare"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedMeasures.boundedMeasureTensorSquare"),
                H("bounded Measure Tensor Square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite difference of the tail projections lands in the actual protected P. This is the genuine bounded-family version of the tensor square in Lemma 3.3.3."))),
                DescribeRole.Theorem))));
}
