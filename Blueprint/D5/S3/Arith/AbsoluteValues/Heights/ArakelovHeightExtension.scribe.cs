using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class ArakelovHeightExtensionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arakelov tuple height grows by the extension degree under scalar extension.",
        H("Arakelov Height Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("arakelov-height-extension"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/ArakelovHeightExtension.arakelovMulHeight_pow_finrank"),
            H("Arakelov Height Extension"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Arakelov tuple height over a number-field extension is the base-field height raised to the extension degree."))),
            DescribeRole.Theorem))));
}
