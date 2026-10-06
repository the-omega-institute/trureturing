using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ExactFunctorNatTransDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural transformations of exact additive functors descend to the unbounded derived localization and commute with integer shifts.",
        H("Derived natural transformations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-exactfunctornattrans-mapderivedcategory"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory"),
                H("Descend an exact natural transformation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This supplier ports Joel Riou's proved Mathlib natural-transformation construction from commit 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22 to the native pin. The source retains the original Apache-2.0 notices. Shift compatibility is proved componentwise and transported through localization; no derived-existence hypothesis is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-exactfunctornattrans-representative-formula"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ExactFunctorNatTrans.mapDerivedCategory_app_Q_obj"),
                H("The formula on every unbounded representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer-indexed complex, the localized transformation is the degreewise map conjugated by the two exact-functor localization comparisons. This literal formula supplies the mate and defining-cell compatibility in the constructor."))),
                DescribeRole.Theorem))));
}
