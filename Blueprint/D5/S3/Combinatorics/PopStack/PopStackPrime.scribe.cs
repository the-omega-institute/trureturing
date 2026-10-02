using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackPrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackPrime.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let a simple skeleton of size at least four be inflated at a valid position by a nonempty permutation block. Every proper nontrivial interval of the inflated permutation lies inside the inserted block. Conversely, each interval of the block with positive lower value becomes an interval at the corresponding position in the inflated permutation, with its values shifted by the skeleton entry minus one.",
        H("Intervals within a single inflated block"),
        Blocks(
            Node("pop-stack-popstackprime-inflation-intervals", "Intervals within a single inflated block", "inflation_intervals",
                "Let a simple skeleton of size at least four be inflated at a valid position by a nonempty permutation block. Every proper nontrivial interval of the inflated permutation lies inside the inserted block. Conversely, each interval of the block with positive lower value becomes an interval at the corresponding position in the inflated permutation, with its values shifted by the skeleton entry minus one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
