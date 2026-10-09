using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimGrundyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimGrundy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal divisor rule gives a finite move set and a recursion on total stones.",
        H("Divisor Nim and Minimum Excluded Values"),
        Blocks(
            Node("dnim-divisornimgrundy-0", "Heap multisets", "Position",
                "A position is a finite multiset of natural heap sizes.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-1", "Positive heaps", "Positive",
                "Every heap appearing in the position has positive size.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-2", "A common divisor", "dividesAll",
                "The removal amount divides every heap in the given multiset.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-3", "Replace one heap", "successor",
                "Erase one occurrence of h and insert h minus d when this remainder is positive.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-4", "Legal removal", "legal",
                "The amount d is positive, is at most h, and divides every heap left after erasing one occurrence of h.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-5", "All followers", "moves",
                "For each occurring heap h, include each replacement by a legal amount from one through h.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-6", "Stone count decreases", "successor_sum_lt",
                "Replacing an occurring heap by its remainder under a legal positive removal strictly decreases the multiset sum.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-7", "Sprague–Grundy value", "grundy",
                "Recursion on the multiset sum takes the least natural number absent from the finite set of follower values.", DescribeRole.Definition),
            Node("dnim-divisornimgrundy-8", "Every follower is smaller", "move_sum_lt",
                "Every follower has strictly fewer stones than its parent.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-9", "The mex equation", "grundy_eq",
                "The value of a position equals the minimum excluded natural number of the values of its followers.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-10", "The current value is excluded", "grundy_not_follower",
                "No follower has the same Grundy value as the current position.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-11", "Smaller values are attained", "follower_mem_of_lt",
                "Every natural number smaller than the current Grundy value is the value of some follower.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-12", "Mex and cardinality", "mex_le_card",
                "The minimum excluded natural number of a finite set is at most its cardinality.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-13", "Count distinct exceptional values", "mex_counting",
                "If every element of s is at most B or belongs to E, then the mex of s is at most B plus the cardinality of E plus one.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-14", "Count exceptional followers", "grundy_counting",
                "If every follower has value at most B or belongs to a finite set E, the current value is at most B plus the cardinality of E plus one.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-15", "Bounded follower values", "grundy_le_of_followers",
                "When every follower value is at most B, the current value is at most B plus one.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-16", "Zero and its followers", "grundy_zero_iff",
                "A position has value zero exactly when every follower has nonzero value.", DescribeRole.Theorem),
            Node("dnim-divisornimgrundy-17", "The twice-minimum bound", "claim",
                "For every nonempty positive heap multiset and each smallest occurring heap m, the Grundy value is at most twice m.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
