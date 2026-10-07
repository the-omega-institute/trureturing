using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class LocalizationCoproductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coproduct preservation for a localization with a right calculus of fractions. This is the specific missing sum argument needed for the actual unbounded cellular telescope. New proofs, released under Apache 2.0.",
        H("Localization Coproduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-localizationcoproduct-localization-coproduct-hom-zero"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/LocalizationCoproduct.localization_coproduct_hom_zero"),
                H("localization coproduct hom zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vanishing on every summand detects zero after localization, including all roofs. The proof refines the denominators separately and then sums the actual weak equivalences."))),
                DescribeRole.Theorem))));
}
