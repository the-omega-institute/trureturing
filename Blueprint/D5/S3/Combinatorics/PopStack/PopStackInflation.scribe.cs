using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackInflationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackInflation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inflating the second entry of a simple permutation of size at least four by a permutation block containing 12 produces an occurrence of 2341, provided that second entry is not the minimum.",
        H("An ascent in the second inflated block"),
        Blocks(
            Node("pop-stack-popstackinflation-inflate", "Inflating an entry", "inflate",
                "To inflate the entry of p at position i by a block b, replace that entry v by the entries of b, each first increased by v and then decreased by one. For every other entry greater than v, first add the length of b and then subtract one. The prefix before i and the suffix after i retain their order. Positions are numbered from zero, and an absent entry has value zero; subtraction is truncated at zero.", DescribeRole.Definition),
            Node("pop-stack-popstackinflation-ascending-first-inflation", "An ascent in the first inflated block", "ascending_first_inflation",
                "Inflating the first entry of a simple permutation of size at least three by a permutation block containing 12 produces an occurrence of 2341.", DescribeRole.Theorem),
            Node("pop-stack-popstackinflation-ascending-second-inflation", "An ascent in the second inflated block", "ascending_second_inflation",
                "Inflating the second entry of a simple permutation of size at least four by a permutation block containing 12 produces an occurrence of 2341, provided that second entry is not the minimum.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
