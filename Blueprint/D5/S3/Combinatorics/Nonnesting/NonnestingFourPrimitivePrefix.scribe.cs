using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitivePrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitivePrefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occurrences under a doubled largest prefix reduce to the tail or a smaller obstruction.",
        H("Patterns under a Largest-Letter Prefix"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitiveprefix-prefix-nesting-reduces", "Nesting patterns reduce to the tail", "prefix_nesting_reduces",
                "A 1221 or 2112 occurrence in a doubled-largest-prefix word already occurs in its tail.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourprimitiveprefix-prefix-pattern-reduces", "Four-pattern occurrence reduction", "prefix_pattern_reduces",
                "An occurrence of one of the four forbidden patterns in a doubled-largest-prefix word occurs in the tail or gives a descending three-letter sublist with its larger letter repeated.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
