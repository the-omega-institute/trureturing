using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ColimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "# Preservation of coproducts from finite coproducts and filtered colimits This file adds a preservation counterpart to mathlib's construction of coproducts from finite coproducts and filtered colimits.",
        H("Colimits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-colimits-preservescolimitsofshape-discrete-of-preservesfinitecoproducts-and-filteredcolimits"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Colimits.preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts_and_filteredColimits"),
                H("preserves Colimits Of Shape discrete of preserves Finite Coproducts and filtered Colimits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A functor preserving finite coproducts and filtered colimits preserves coproducts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-colimits-issolid-coproduct"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Colimits.isSolid_coproduct"),
                H("is Solid coproduct"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any small coproduct of solid objects is solid."))),
                DescribeRole.Theorem))));
}
