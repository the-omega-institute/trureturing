using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class CellFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-stage factorization for the concrete two-term localization cells.",
        H("Cell Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-cellfactorization-solidcellularcolimit-cellmap-factors"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CellFactorization.solidCellularColimit_cellMap_factors"),
                H("solid Cellular Colimit cell Map factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every chain map from a defining two-term cell into the full cellular colimit factors through an actual finite stage. The incoming complex is arbitrary and unbounded."))),
                DescribeRole.Theorem))));
}
