using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class CellularSolidificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete unbounded cellular construction from the protected defining maps. Each step attaches mapping cones along every chain map from every integer placement of a defining cell. The proved null-homotopies below are actual data. The sequential colimit is a construction in complexes; locality and the derived universal property are not claimed here.",
        H("Cellular Solidification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-cellularsolidification-solidcellularcolimit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimit"),
                H("solid Cellular Colimit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual sequential colimit, formed degreewise, of all cellular stages. This definition alone asserts neither locality nor a derived adjunction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-cellularsolidification-solidcellularcolimithomotopy"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimitHomotopy"),
                H("solid Cellular Colimit Homotopy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Maps from defining cells that enter at any finite stage are explicitly null-homotopic in the full sequential colimit."))),
                DescribeRole.Definition))));
}
