using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class KProjectiveCoproductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closure under arbitrary coproducts for an unbounded resolution construction.",
        H("KProjective Coproduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-kprojectivecoproduct-iskprojective-coproduct"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/KProjectiveCoproduct.isKProjective_coproduct"),
                H("is KProjective coproduct"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arbitrary coproducts of K-projective cochain complexes are K-projective. The members may have unrelated bounds, and may themselves be unbounded."))),
                DescribeRole.Theorem))));
}
