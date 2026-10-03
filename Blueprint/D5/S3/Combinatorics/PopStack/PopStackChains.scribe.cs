using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackChainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackChains.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a word with distinct entries, membership in D is equivalent to the existence of a value cut such that entries on each side of the cut occur in decreasing order. Every such word belongs to C.",
        H("A cut into decreasing chains"),
        Blocks(
            Node("pop-stack-popstackchains-ind", "The two-chain class", "InD",
                "The class D consists of words avoiding the classical patterns 123, 3142 and 3412.", DescribeRole.Definition),
            Node("pop-stack-popstackchains-two-decreasing-chains", "A cut into decreasing chains", "two_decreasing_chains",
                "For a word with distinct entries, membership in D is equivalent to the existence of a value cut such that entries on each side of the cut occur in decreasing order. Every such word belongs to C.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
