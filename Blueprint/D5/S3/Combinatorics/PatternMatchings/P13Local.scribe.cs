using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13LocalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Local.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source avoidance determines exactly the relative closing order of the active survivors.",
        H("The future order of arcs avoiding P13"),
        Blocks(
            Node("p13-p13local-p13", "The source pattern set", "P13",
                "The source labels are 132, 213 and 321, written as zero-based vectors. Their labels record complementary right-endpoint ranks.", DescribeRole.Definition),
            Node("p13-p13local-avoids", "Avoidance by an actual perfect matching", "Avoids",
                "An actual perfect matching avoids each of the three source patterns. An occurrence requires three increasing left endpoints preceding every one of the three right endpoints.", DescribeRole.Definition),
            Node("p13-p13local-closingoccurs", "Chronological closing words", "ClosingOccurs",
                "An eligible triple is indexed by increasing opener. The displayed word gives these indices in increasing order of their right endpoints. Source 132 corresponds to closing word 231, source 213 to 312, and source 321 to 123.", DescribeRole.Definition),
            Node("p13-p13local-futureorder", "The pairwise future-order law", "FutureOrder",
                "At a closure, consider two surviving active openers x<y. The older one closes before the younger one exactly when the opener just selected lies strictly between them.", DescribeRole.Definition),
            Node("p13-p13local-future-order-iff", "Exact local characterization", "future_order_iff",
                "For every perfect matching of Fin(2n), P13 avoidance is equivalent to the future-order law at every closure. The eligibility condition ensures that any two survivors and the just-closed arc form a source triple; conversely each forbidden eligible triple violates the law at its first closure.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
