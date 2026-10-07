using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class TelescopeComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual comparison from the mapping telescope to the previously saved ordinary cellular colimit. This defines and proves the comparison equations; its quasi-isomorphism property is an explicit remaining theorem, not an assumed bridge. New proofs, released under Apache 2.0.",
        H("Telescope Comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-telescopecomparison-solidcellulartelescopetocolimit-input"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/TelescopeComparison.solidCellularTelescopeToColimit_input"),
                H("solid Cellular Telescope To Colimit input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In particular, the comparison preserves the map from the original arbitrary unbounded complex into the ordinary saved cellular colimit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-telescopecomparison-solidcellulartelescopeshortcomplex-exact"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/TelescopeComparison.solidCellularTelescopeShortComplex_exact"),
                H("solid Cellular Telescope Short Complex exact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exactness at the middle of the actual telescope presentation. The remaining short-exactness input is monicity of its first map."))),
                DescribeRole.Theorem))));
}
