using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class PseudoBasisDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finitely generated module over a Dedekind domain admits a pseudo-basis.",
        H("Pseudo Basis"),
        Blocks(Describe.Lean(
            DescribeId.Create("pseudo-basis"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/PseudoBasis.exists_pseudoBasis"),
            H("Pseudo Basis"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A finitely generated module over a Dedekind domain admits a pseudo-basis."))),
            DescribeRole.Theorem))));
}
