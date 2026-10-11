using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasuresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical measure map from the protected P to the countable product of discrete integers. This is the concrete map in Rodriguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4. The proofs here are new, Apache-2.0. No realization or total-derived existence is assumed.",
        H("Measures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measures-measurenumeratorcoordinate-relation"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Measures.measureNumeratorCoordinate_relation"),
                H("measure Numerator Coordinate relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The canonical measure map from the protected P to the countable product of discrete integers. This is the concrete map in Rodriguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4. The proofs here are new, Apache-2.0. No realization or total-derived existence is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measures-integermeasures-solid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Measures.integerMeasures_solid"),
                H("integer Measures solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The canonical measure map from the protected P to the countable product of discrete integers. This is the concrete map in Rodriguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4. The proofs here are new, Apache-2.0. No realization or total-derived existence is assumed."))),
                DescribeRole.Theorem))));
}
