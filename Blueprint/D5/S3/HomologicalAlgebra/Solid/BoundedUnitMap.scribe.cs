using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class BoundedUnitMapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical protected map q : P -> B_Z and its exact factorization of PToIntegerMeasures. All bounded test families have actual free maps to B_Z. New proofs, Apache-2.0; the concrete bounded intermediary is from Rodríguez Camargo's Notes on Solid Geometry, Lemmas 3.3.3--3.3.4.",
        H("Bounded Unit Map"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-boundedunitmap-ptoboundedintegermeasures-comparison"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedUnitMap.PToBoundedIntegerMeasures_comparison"),
                H("PTo Bounded Integer Measures comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The canonical protected map q : P -> B_Z and its exact factorization of PToIntegerMeasures. All bounded test families have actual free maps to B_Z. New proofs, Apache-2.0; the concrete bounded intermediary is from Rodríguez Camargo's Notes on Solid Geometry, Lemmas 3.3.3--3.3.4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-boundedunitmap-boundedfamilymap-range-independent"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedUnitMap.boundedFamilyMap_range_independent"),
                H("bounded Family Map range independent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordinary maps into B_Z do not depend on a presentation of the bound."))),
                DescribeRole.Theorem))));
}
