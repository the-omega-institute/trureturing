using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedLocalReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A genuine reflector on the actual unbounded derived category onto its full subcategory of protected derived-local objects. This subcategory has not been identified with DerivedCategory Solid. In particular this file does not declare the protected total-left-derived functor. New proofs, released under the Apache 2.0 license.",
        H("Derived Local Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedlocalreflection-solidderivedlocaldegreewisecomparison-unit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedLocalReflection.solidDerivedLocalDegreewiseComparison_unit"),
                H("solid Derived Local Degreewise Comparison unit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural comparison factors the exact original degreewise unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedlocalreflection-solidcellularcolimit-derivedprecomp-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedLocalReflection.solidCellularColimit_derivedPrecomp_bijective"),
                H("solid Cellular Colimit derived Precomp bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual cellular colimit, not only the telescope, has the full derived universal comparison against all protected derived-local targets."))),
                DescribeRole.Theorem))));
}
