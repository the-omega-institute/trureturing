using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfCountingCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfCountingCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-point subsets of one-line permutation words are counted by factorials and derangement numbers.",
        H("Counting Words by Their Fixed Points"),
        Blocks(
            Node("words", "Permutation words on a support", "words", "The finite set words(s) contains all lists that permute the elements of the finite set s.", DescribeRole.Definition),
            Node("word", "A word on a support", "Word", "Word(s) is the type of elements of the finite set words(s).", DescribeRole.Definition),
            Node("insert-word", "Insert a new singleton block", "insertWord", "Canonical insertion takes a word on s and a fresh value f to a word on s with f inserted.", DescribeRole.Definition),
            Node("erase-word", "Erase one support value", "eraseWord", "Erasing f from a word on s gives a word on the support s without f.", DescribeRole.Definition),
            Node("fixed-word-equivalence", "A fixed point is a free insertion", "fixedWordEquiv", "Words on s are equivalent to words on s with a fresh f whose inverse Foata map fixes f.", DescribeRole.Definition),
            Node("forced-fixed", "Prescribed fixed points", "ForcedFixed", "ForcedFixed(s,F) contains words on s whose hat map fixes every value in F.", DescribeRole.Definition),
            Node("forced-insert-equivalence", "Adding a prescribed fixed point", "forcedInsertEquiv", "For F contained in s and fresh f, fixed-point insertion gives an equivalence between ForcedFixed(s,F) and ForcedFixed(s with f,F with f).", DescribeRole.Definition),
            Node("forced-fixed-cardinality", "Count with prescribed fixed points", "card_forcedFixed", "If F is contained in s, the number of words fixing F is the factorial of the cardinality of s minus the cardinality of F.", DescribeRole.Theorem),
            Node("no-fixed", "Words with no fixed point", "NoFixed", "NoFixed(s) contains words on s whose hat map fixes no value of s.", DescribeRole.Definition),
            Node("no-fixed-cardinality", "Derangement count", "card_noFixed", "The number of words on s with no hat-fixed value equals the derangement number at the cardinality of s.", DescribeRole.Theorem),
            Node("exact-fixed", "An exact fixed-point set", "ExactFixed", "ExactFixed(s,F) contains words on s for which a value is hat-fixed exactly when it belongs to F.", DescribeRole.Definition),
            Node("exact-insert-equivalence", "Extending an exact fixed-point set", "exactInsertEquiv", "For a fresh f, insertion gives an equivalence between words with exact fixed set F and words with exact fixed set F with f.", DescribeRole.Definition),
            Node("exact-fixed-cardinality", "Count with an exact fixed-point set", "card_exactFixed", "If F is contained in s, the number of words with exact hat-fixed set F is the derangement number at the cardinality of s minus the cardinality of F.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
