using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152PrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Prefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inversion sequences with increasing positive entries correspond to weakly increasing inversion sequences.",
        H("A Catalan Bijection for Prefixes"),
        Blocks(
            Node("inversionseq-inversionseq152prefix-retain-increases", "Retaining increases", "retainIncreases",
                "Given a preceding nonnegative value p and a word, retain each entry when it is strictly larger than its immediate predecessor, using p before the first entry, and replace it by zero otherwise. Each comparison uses the predecessor in the original word.", DescribeRole.Definition),
            Node("inversionseq-inversionseq152prefix-catalan-prefix-bijection", "A bijection preserving length and maximum", "catalan_prefix_bijection",
                "For every nonnegative length n and maximum M, inversion sequences of length n and maximum M whose nonzero entries are strictly increasing in order of occurrence are in bijection with weakly increasing inversion sequences of length n and maximum M. The maximum of the empty sequence is taken to be zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
