using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateScanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A final value splits a 132-avoider into larger and smaller letters and gives an appended-letter criterion.",
        H("Splitting at the Final Value"),
        Blocks(
            Node("fundamental-bijection-thetaiteratescan-final-value-cut", "The cut determined by the final value", "final_value_cut",
                "A 132-avoiding permutation of size n ending with v greater than one has a cut at n minus v: all entries before the cut exceed v, all entries from the cut up to but excluding the final position are below v, the prefix permutes v plus one through n, and the intervening suffix permutes one through v minus one.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteratescan-avoids132-append-iff", "Avoidance after appending a letter", "avoids132_append_iff",
                "A word followed by v avoids 132 exactly when the word avoids 132 and no increasing positional pair in the word has its first value below v and its second value above v.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteratescan-avoids132-cons-max-append-iff", "Avoidance with an initial maximum", "avoids132_cons_max_append_iff",
                "If top exceeds every entry of a word followed by v, placing top before that word does not alter the criterion: avoidance of 132 is equivalent to avoidance in the word and the absence of an increasing positional pair whose values straddle v.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
