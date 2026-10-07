using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual diagonal/tail-difference identity, by a two-piece closed cover. This compares morphisms into the protected P itself; no injectivity of its map into integer measures is assumed. New proofs, Apache-2.0; research construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Lemma 3.3.3.",
        H("Measure Diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measurediagonal-measurepointedtail-difference"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureDiagonal.measurePointedTail_difference"),
                H("measure Pointed Tail difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal identity holds in free condensed P by genuine closed-cover joint epimorphy, not by testing coordinates of the integer-measure map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measurediagonal-boundedcoefficientmap-unitvectors"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureDiagonal.boundedCoefficientMap_unitVectors"),
                H("bounded Coefficient Map unit Vectors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient map on the unit-vector family is its sole nonzero selector, with coefficients {0,1}."))),
                DescribeRole.Theorem))));
}
