using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.PointClass;

internal sealed class LinePointClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Point Class", H("Line Point Class"),
        Blocks(
            Paragraph(Text("Hodge–Tate image of dX/X is the units extension class mod (ker θ)². Cup product with the Hodge–Tate image of a point class on P¹ is injective.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/LinePointClass.exists_hodgeTateMap_pointClass_line"),
                H("exists_hodgeTateMap_pointClass_line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For k embedded in Q̄_p, λ_1 of the class of [1:0] in ℙ¹ comes from a degree-2 class η on p-adic tests such that x ↦ x × η has zero kernel on Ext^n(N, R[1/p]) for every flat-valued abelian functor N and every n.")))))));
}
