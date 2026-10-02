using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152GapCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152GapCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly increasing gap words and words interspersed with a maximum have binomial enumerations.",
        H("Enumeration of Gap Suffixes"),
        Blocks(
            Node("inversionseq-inversionseq152gapcount-gap-suffix-enumerators", "Subset and multiset enumerations", "gap_suffix_enumerators",
                "Let G be a finite set of nonnegative integers all less than M, and let l be nonnegative. Strictly increasing words of length l + 1 over G are in bijection with subsets of G of size l + 1, and their number is the binomial coefficient choosing l + 1 from the cardinality of G. Words of length l + 1 over G together with M, whose first entry is not M and whose entries remaining after deleting M are strictly increasing, are in bijection with multisets over G of size l + 1. Their number is the binomial coefficient choosing l + 1 from the cardinality of G plus l.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
