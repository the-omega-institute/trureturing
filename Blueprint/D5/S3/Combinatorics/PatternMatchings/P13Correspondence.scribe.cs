using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13CorrespondenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Correspondence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit normalized local scans and actual P13-avoiding perfect matchings are equivalent for every nonnegative size.",
        H("The full P13 matching and scan correspondence"),
        Blocks(
            Node("p13-p13correspondence-queueat", "The complete active opener set", "QueueAt",
                "At cut t, the ordered queue contains exactly the vertices x<t whose partners are at least t.", DescribeRole.Definition),
            Node("p13-p13correspondence-verticesat", "The complete remaining endpoint set", "VerticesAt",
                "The unscanned suffix contains exactly the vertices at least t.", DescribeRole.Definition),
            Node("p13-p13correspondence-encode-realizes", "Total encoding at every size", "encode_realizes",
                "Scanning any actual perfect matching with its complete ordered queue and remaining vertex suffix realizes the whole ranked scan. Every selected closing rank is in range, and insertion and deletion preserve increasing opener order.", DescribeRole.Theorem),
            Node("p13-p13correspondence-futureat", "The local law at one closure", "FutureAt",
                "Among surviving active openers x<y, x closes before y exactly when the just-closed opener lies between them.", DescribeRole.Definition),
            Node("p13-p13correspondence-futuresuffix", "The law at every remaining closure", "FutureSuffix",
                "Every vertex at or after the cut satisfies the exact local future-order law.", DescribeRole.Definition),
            Node("p13-p13correspondence-ordered-run-iff", "Scan orders are exactly the actual future laws", "ordered_run_iff",
                "For the complete active queue and remaining endpoint suffix of an actual matching, realization of every scan order is equivalent to the future-order law at all remaining closures.", DescribeRole.Theorem),
            Node("p13-p13correspondence-encode-accepted", "Every P13 avoider is accepted", "encode_accepted",
                "The full ranked encoding of every actual P13-avoiding matching is accepted from the empty normalized base with no pending openings.", DescribeRole.Theorem),
            Node("p13-p13correspondence-decode-avoids", "Every accepted scan produces a P13 avoider", "decode_avoids",
                "The actual perfect matching decoded from any complete accepted scan avoids the source set P13. All imposed survivor orders persist and the exact source-pattern criterion applies.", DescribeRole.Theorem),
            Node("p13-p13correspondence-realizes-unique", "The complete scan determines all partners", "realizes_unique",
                "Two actual matchings realizing the same ranked scan agree on every queued or remaining endpoint, including the endpoints paired at each closure.", DescribeRole.Theorem),
            Node("p13-p13correspondence-matchingequiv", "The unbounded carrier equivalence", "matchingEquiv",
                "For every n>=0, actual P13-avoiding perfect matchings of Fin(2n) are equivalent to scans accepted by the independent normalized local machine. Encoding and decoding are total inverses. The empty matching is included, and scans may return to zero and start another component. This structural correspondence does not state the enumeration or a generating function.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
