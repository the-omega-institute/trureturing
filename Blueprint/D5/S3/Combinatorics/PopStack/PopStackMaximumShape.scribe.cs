using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMaximumShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMaximumShape.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a permutation of size at least four with maximum second, consider its suffix after the first two entries. Require that values above the first entry decrease and that no value below the first entry has both a smaller and a larger such value later. These two conditions imply membership in C, and every simple member of C with maximum second satisfies them.",
        H("The two value regions below a second-position maximum"),
        Blocks(
            Node("pop-stack-popstackmaximumshape-maximum-second-shape", "The two value regions below a second-position maximum", "maximum_second_shape",
                "For a permutation of size at least four with maximum second, consider its suffix after the first two entries. Require that values above the first entry decrease and that no value below the first entry has both a smaller and a larger such value later. These two conditions imply membership in C, and every simple member of C with maximum second satisfies them.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
