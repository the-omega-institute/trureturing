using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class GaussLemmaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a nonarchimedean place, the coefficient sup norm of a polynomial product is multiplicative.",
        H("Gauss Lemma"),
        Blocks(Describe.Lean(
            DescribeId.Create("gauss-lemma"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/GaussLemma.iSup_coeff_mul"),
            H("Gauss Lemma"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("At a nonarchimedean place, the coefficient sup norm of a polynomial product is multiplicative."))),
            DescribeRole.Theorem))));
}
