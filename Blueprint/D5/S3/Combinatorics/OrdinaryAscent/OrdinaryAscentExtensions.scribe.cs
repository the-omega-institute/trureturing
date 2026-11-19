using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class OrdinaryAscentExtensionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentExtensions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/mazhang2026ordinary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordinary ascent words with literal adjacent-pair avoidance and exact boundary conditions.",
        H("Literal extensions and unique parents"),
        Blocks(
            Node("canappend", "CanAppend", "CanAppend",
                "The exact ordinary ascent bound, including the empty-root bound zero, together with exclusion of every new literal occurrence at the appended value.", DescribeRole.Definition),
            Node("append-avoiders-iff", "append_avoiders_iff", "append_avoiders_iff",
                "For every subset of the thirteen patterns and every length n, appending a letter gives an actual length n+1 avoider exactly when its parent is an actual length n avoider and the exact extension conditions hold.", DescribeRole.Theorem),
            Node("parent-admission", "parent_admission", "parent_admission",
                "Taking the length-n prefix of an actual length n+1 avoider and its final value gives an actual parent and a legal extension, including n=0.", DescribeRole.Theorem),
            Node("extensionequiv", "extensionEquiv", "extensionEquiv",
                "A genuine equivalence between actual length n+1 avoiders and pairs of an actual length-n parent and a legal appended value. Its inverse is literal concatenation, and both inverse identities are proved. No equivalence between different pattern classes is asserted.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("ordinaryascentextensions-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
