using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152SuffixSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152SuffixSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded distinct-entry suffixes avoiding 201 and 210 have a generating function determined by binary choices.",
        H("Generating Function for Bounded Right Suffixes"),
        Blocks(
            Node("inversionseq-inversionseq152suffixseries-first-label-suffix-enumeration", "Enumeration by the first label", "first_label_suffix_enumeration",
                "Fix nonnegative integers l and h. Over the rational numbers, let S(x) have constant coefficient one and, in each positive degree n, the number of words of length n with pairwise distinct entries, all greater than l, avoiding 201 and 210 and satisfying the bound that the entry at position i is at most l + h + 1 + i, with positions numbered from zero. Let B(x) have coefficient 2 to the power n in degree n. Then 2 (1 - x) S(x) = 1 + B(x) to the power h.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
